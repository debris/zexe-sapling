#![no_std]

extern crate alloc;

mod data;

// TODO: META:
// - replace bls12_377 with bls12_381
// - port redjubjub to zexe and no-std

use algebra::{
    curves::{
        bls12_377::Bls12_377Parameters,
        edwards_bls12::EdwardsParameters,
        models::{
            bls12::Bls12,
            twisted_edwards_extended::{GroupAffine, GroupProjective},
        },
    },
    fields::bls12_377::fr::Fr,
    prelude::{Group, Zero},
    FromBytes,
};
use alloc::vec::Vec;
use data::{Sapling, SaplingOutputDescription, SaplingSpendDescription};
use groth16::{PreparedVerifyingKey, Proof, verify_proof};

pub type Groth16VerifyingKey = PreparedVerifyingKey<Bls12<Bls12_377Parameters>>;
pub type Point = GroupProjective<EdwardsParameters>;

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
    let _anchor = Fr::read(&spend.anchor as &[u8]).map_err(|_| ())?;

    // compute the signature's message for randomized key && spend_auth_sig
    let mut data_to_be_signed = [0u8; 64];
    data_to_be_signed[..32].copy_from_slice(&spend.randomized_key);
    data_to_be_signed[32..].copy_from_slice(sighash);

    // TODO: logic requiring redjubjub

    Ok(())
}

fn accept_output(
    output_vk: &Groth16VerifyingKey,
    total: &mut Point,
    output: &SaplingOutputDescription,
) -> Result<(), ()> {
    // deserialize and check value commitment
    let value_commitment = require_non_small_order_point(&output.value_commitment)?;

    // accumulate value commitment
    *total -= &value_commitment;

    // deserialize the anchor, which should be an element of Fr
    let note_commitment = Fr::read(&output.note_commitment as &[u8]).map_err(|_| ())?;

    // deserialize the ephemeral key
    let ephemeral_key = require_non_small_order_point(&output.ephemeral_key)?;

    // construct public input for circuit
    let ephemeral_xy: GroupAffine<_> = ephemeral_key.into();
    let value_xy: GroupAffine<_> = value_commitment.into();
    let public_input = [
        value_xy.x,
        value_xy.y,
        ephemeral_xy.x,
        ephemeral_xy.y,
        note_commitment,
    ];

    // deserialize the proof
    let zkproof = Proof::<Bls12<Bls12_377Parameters>>::read(&output.zkproof as &[u8]).map_err(|_| ())?;

    // check the proof
    let is_verification_ok = verify_proof(&output_vk, &zkproof, &public_input).map_err(|_| ())?;

    if !is_verification_ok {
        return Err(());
    }

    Ok(())
}

fn accept_sapling_final(_sighash: &[u8; 32], _total: Point, _sapling: &Sapling) -> Result<(), ()> {
    // TODO: logic requiring redjubjub

    Ok(())
}

fn require_non_small_order_point(point_buff: &[u8; 32]) -> Result<Point, ()> {
    match Point::read(point_buff as &[u8]) {
        Ok(point) if !is_small_order(&point) => Ok(point),
        _ => Err(()),
    }
}

/// Is this a small order point?
fn is_small_order(point: &Point) -> bool {
    point.double().double().double().is_zero()
}
