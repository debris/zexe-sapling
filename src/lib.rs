#![no_std]

extern crate alloc;

mod data;

use algebra::{
    curves::{bls12_381::Bls12_381Parameters, jubjub::JubJubParameters, models::bls12::Bls12},
    prelude::{Group, Zero},
    FromBytes, ModelParameters,
};
use alloc::vec::Vec;
use core::ops::{Add, Neg};
use data::{Sapling, SaplingOutputDescription, SaplingSpendDescription};
use groth16::{verify_proof, PreparedVerifyingKey, Proof};
use zexe_redjubjub::{read_point, write_point, FixedGenerators, PublicKey, Signature};

pub type Groth16VerifyingKey = PreparedVerifyingKey<Bls12<Bls12_381Parameters>>;
pub type Point = zexe_redjubjub::Point<JubJubParameters>;

pub fn accept_sapling(
    spend_vk: &Groth16VerifyingKey,
    output_vk: &Groth16VerifyingKey,
    sighash: &[u8; 32],
    sapling: &Sapling,
) -> Result<(), ()> {
    let mut total = Point::zero();
    for (_, spend) in sapling.spends.iter().enumerate() {
        accept_spend(spend_vk, sighash, &mut total, spend)?;
    }

    for (_, output) in sapling.outputs.iter().enumerate() {
        accept_output(output_vk, &mut total, output)?;
    }

    accept_sapling_final(sighash, total, sapling)
}

fn accept_spend(
    _spend_vk: &Groth16VerifyingKey,
    sighash: &[u8; 32],
    total: &mut Point,
    spend: &SaplingSpendDescription,
) -> Result<(), ()> {
    // deserialize and check value commitment
    let value_commitment = require_non_small_order_point(&spend.value_commitment)?;

    // accumulate value commitment
    *total += &value_commitment;

    // deserialize the anchor, which should be an element of Fr
    let _anchor = <JubJubParameters as ModelParameters>::BaseField::read(&spend.anchor as &[u8])
        .map_err(|_| ())?;

    // compute the signature's message for randomized key && spend_auth_sig
    let mut data_to_be_signed = [0u8; 64];
    data_to_be_signed[..32].copy_from_slice(&spend.randomized_key);
    data_to_be_signed[32..].copy_from_slice(sighash);

    let randomized_key = PublicKey::read(&spend.randomized_key[..]).map_err(|_| ())?;
    if is_small_order(&randomized_key.point) {
        return Err(());
    }

    // deserialize the signature
    let spend_auth_sig = Signature::read(&spend.spend_auth_sig[..])
        .expect("only could fail if length of passed buffer != 64; qed");

    // verify the spend_auth_sig
    if !randomized_key.verify(
        &data_to_be_signed,
        &spend_auth_sig,
        FixedGenerators::SpendingKeyGenerator,
    ) {
        return Err(());
    }

    // TODO: logic requiring sapling_crypto::multipack

    Ok(())
}

fn accept_output(
    output_vk: &Groth16VerifyingKey,
    total: &mut Point,
    output: &SaplingOutputDescription,
) -> Result<(), ()> {
    use algebra::curves::ProjectiveCurve;

    // deserialize and check value commitment
    let value_commitment = require_non_small_order_point(&output.value_commitment)?;

    // accumulate value commitment
    *total -= &value_commitment;

    // deserialize the anchor, which should be an element of Fr
    let note_commitment =
        <JubJubParameters as ModelParameters>::BaseField::read(&output.note_commitment as &[u8])
            .map_err(|_| ())?;

    // deserialize the ephemeral key
    let ephemeral_key = require_non_small_order_point(&output.ephemeral_key)?;

    // construct public input for circuit
    let ephemeral_xy = ephemeral_key.into_affine();
    let value_xy = value_commitment.into_affine();
    let public_input = [
        value_xy.x,
        value_xy.y,
        ephemeral_xy.x,
        ephemeral_xy.y,
        note_commitment,
    ];

    // deserialize the proof
    let zkproof =
        Proof::<Bls12<Bls12_381Parameters>>::read(&output.zkproof as &[u8]).map_err(|_| ())?;

    // check the proof
    let is_verification_ok = verify_proof(&output_vk, &zkproof, &public_input).map_err(|_| ())?;

    if !is_verification_ok {
        return Err(());
    }

    Ok(())
}

fn accept_sapling_final(sighash: &[u8; 32], total: Point, sapling: &Sapling) -> Result<(), ()> {
    // obtain current bvk from the context
    let mut binding_verification_key = PublicKey::new(total);

    // compute value balance
    let mut value_balance = compute_value_balance(sapling.balancing_value)?;

    // subtract value_balance from current bvk to get final bvk
    value_balance = value_balance.neg();
    binding_verification_key.point = binding_verification_key.point.add(&value_balance);

    // compute the signature's message for binding_verification_key/binding_sig
    let mut data_to_be_signed = [0u8; 64];
    write_point(
        &binding_verification_key.point,
        &mut data_to_be_signed[..32],
    )
    .expect("bvk is 32 bytes");
    data_to_be_signed[32..].copy_from_slice(&sighash[..]);

    // deserialize the binding signature
    let binding_sig = Signature::read(&sapling.binding_sig[..])
        .expect("only could fail if length of passed buffer != 64; qed");

    // check the binding signature
    let is_verification_ok = binding_verification_key.verify(
        &data_to_be_signed,
        &binding_sig,
        FixedGenerators::ValueCommitmentRandomness,
    );
    if !is_verification_ok {
        return Err(());
    }

    Ok(())
}

fn require_non_small_order_point(point_buff: &[u8; 32]) -> Result<Point, ()> {
    match read_point(&point_buff[..]) {
        Some(point) if !is_small_order(&point) => Ok(point),
        _ => Err(()),
    }
}

/// Is this a small order point?
fn is_small_order(point: &Point) -> bool {
    point.double().double().double().is_zero()
}

/// This function computes `value` in the exponent of the value commitment base
fn compute_value_balance(value: i64) -> Result<Point, ()> {
    // Compute the absolute value (failing if -i64::MAX is the value)
    let abs = match value.checked_abs() {
        Some(a) => a as u64,
        None => return Err(()),
    };

    // Is it negative? We'll have to negate later if so.
    let is_negative = value.is_negative();

    // Compute it in the exponent
    let mut value_balance = FixedGenerators::ValueCommitmentValue
        .point()
        .mul(&abs.into());

    // Negate if necessary
    if is_negative {
        value_balance = value_balance.neg();
    }

    // Convert to unknown order point
    Ok(value_balance.into())
}
