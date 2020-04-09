#![no_std]

extern crate alloc;

pub mod zcash;

mod affine;
mod data;
mod multipack;
mod proof;

use algebra::{
    bls12_381,
    jubjub::JubJubParameters,
    prelude::{Group, Zero},
    Bls12_381, FromBytes, ModelParameters,
};
use alloc::vec::Vec;
use core::ops::{Add, Neg};
use groth16::{verify_proof, PreparedVerifyingKey, VerifyingKey};
use zexe_redjubjub::{read_point, write_point, FixedGenerators, PublicKey, Signature};

pub use data::{Sapling, SaplingOutputDescription, SaplingSpendDescription};

pub type Groth16VerifyingKey = VerifyingKey<Bls12_381>;
pub type Groth16PreparedVerifyingKey = PreparedVerifyingKey<Bls12_381>;
pub type Point = zexe_redjubjub::Point<JubJubParameters>;

pub fn accept_sapling(
    spend_vk: &Groth16PreparedVerifyingKey,
    output_vk: &Groth16PreparedVerifyingKey,
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

pub fn accept_spend(
    spend_vk: &Groth16PreparedVerifyingKey,
    sighash: &[u8; 32],
    total: &mut Point,
    spend: &SaplingSpendDescription,
) -> Result<(), ()> {
    use algebra::ProjectiveCurve;

    // deserialize and check value commitment
    let value_commitment = require_non_small_order_point(&spend.value_commitment)?;

    // accumulate value commitment
    *total += &value_commitment;

    // deserialize the anchor, which should be an element of Fr
    let anchor = <JubJubParameters as ModelParameters>::BaseField::read(&spend.anchor as &[u8])
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

    // Add the nullifier through multiscalar packing
    let nullifier = multipack::bytes_to_bits_le(&spend.nullifier);
    let nullifier = multipack::compute_multipacking::<bls12_381::g1::Parameters>(&nullifier);
    assert_eq!(nullifier.len(), 2);

    let randomized_key_xy = randomized_key.point.into_affine();
    let value_xy = value_commitment.into_affine();
    let public_input = [
        randomized_key_xy.x,
        randomized_key_xy.y,
        value_xy.x,
        value_xy.y,
        anchor,
        nullifier[0],
        nullifier[1],
    ];

    // deserialize the proof
    // TODO: its currently unimplemented in groth16
    let zkproof = proof::read_proof(spend.zkproof)?;

    // check the proof
    let is_verification_ok = verify_proof(&spend_vk, &zkproof, &public_input).map_err(|_| ())?;

    if !is_verification_ok {
        return Err(());
    }

    Ok(())
}

pub fn accept_output(
    output_vk: &Groth16PreparedVerifyingKey,
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
    // TODO: its currently unimplemented in groth16
    let zkproof = proof::read_proof(output.zkproof)?;

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

#[cfg(test)]
mod tests {
    use super::{accept_sapling, Sapling, SaplingOutputDescription, SaplingSpendDescription};
    use crate::zcash;
    use alloc::vec;
    use hex_literal::hex;

    #[test]
    fn test_lib() {
        // data comes from tx:
        // https://zcash.blockexplorer.com/tx/bd4fe81c15cfbd125f5ca6fe51fb5ac4ef340e64a36f576a6a09f7528eb2e176
        let test_sapling = Sapling {
            balancing_value: 0x2710,
            spends: vec![
                SaplingSpendDescription {
                    value_commitment: hex!("48b1c0668fce604361fbb1b89bbd76f8fee09b51a9dc0fdfcf6c6720cd596083"),
                    anchor: hex!("d970234fcc0e9a70fdfed82d32fbb9ca92c9c5c3bad5daad9ac62b5bf4255817"),
                    nullifier: hex!("ee5bc95a9af453bb9cc7e2c544aa29efa20011a65b624998369c849aa8f0bc83"),
                    randomized_key: hex!("d60e7902a3cfe6eeaeb8d583a491de5982c5ded29e64cd8f8fac594a5bb4f283"),
                    zkproof: hex!("8e6c30876e36a18d8d935238815c8d9205a4f1f523ff76b51f614bff1064d1c5fa0a27ec0c43c8a6c2714e7234d32e9a8934a3e9c0f74f1fdac2ddf6be3b13bc933b0478cae556a2d387cc23b05e8b0bd53d9e838ad2d2cb31daccefe256087511b044dfae665f0af0fa968edeea4cbb437a8099724159471adf7946eec434cccc1129f4d1e31d7f3f8be524226c65f28897d3604c14efb64bea6a889b2705617432927229dfa382e78c0ace31cc158fbf3ec1597242955e45af1ee5cfaffd78"),
                    spend_auth_sig: hex!("9cc80dc53d6b18d42033ec2c327170e2811fe8ec00feadeb1033eb48ab24a6dce2480ad428be57c4619466fc3181ece69b914fed30566ff853250ef19ef73706"),
                },
            ],
            outputs: vec![
                SaplingOutputDescription {
                    value_commitment: hex!("f4c24b0125e4059eec61f63ccbe277363172f2bdee384412ea073c5aca06b94e"),
                    note_commitment: hex!("402ba3a43e15bd9c65bbfb194c561c24a031dec43be95c59eb6b568c176b1038"),
                    ephemeral_key: hex!("d5b7b057dc032488335284adebfb6607e6a995b7fa418f13c8a61b343e5df44f"),
                    enc_cipher_text: hex!("aa1050d9d76550748d9efebe01da97ade5937afd5f007ed26e0af03f283611655e91bc6a4857f66a57a1584ff687c4baf725f4a1b32fae53a3e6e8b98bca319bb1badb704c9c1a04f401f33d813d605eef6943c2c52dbc85ab7081d1f8f69d3202aae281bf42336a949a12a7dbbd22abdd6e92996282ebd69033c22cb0539d97f83636d6a8232209a7411e8b03bef180d83e608563ea2d0becff56dc996c2049df054961bfb21b7cbef5049a7dacc18f2c977aa1b2d48291abc19c3c8ea25d2e61901048354b17ce952f6f2248cf3a0eb54c19b507b41d7281c3d227e2b142ff695d8b925a4bb942ed9492a73a17468a8332a367fd16295420bdca6c04d380271f40440709998fce3a3af3e1e505f5402e5dd464dd179cb0eede3d494a95b84d2fb2eb5abb425cf2c712af999c65259c4782a5ec97388324c67738908a5ba43b6db62a10f50cddf9b5039123437c74165921ac8cf4f13292a216baef9d00bd544106b52755986c98a462ade1149f69367e926d88eb92798c0e56cd19a1bcf264fd93293033b758da65c7901eb5b4a17ee265a3312dbc477868da0057e1b3cbf47726dead6ecfcc8e1044c6f311ff0fc83192dc2f75a89626ba33364dac747b63ff3c8337e00332c8783ba9c8dc13cdf0750d7adc3926fbe1279017d50adba35c38c5b810f73abe5d759cd7fb650f6b0a1f78dc1f62fd017090ff4de4cf54c883752ddda68083d4617ed2c38bab8da313965dd3f7b755aec23a2d9e2965d08d2134827a72ffb3bd65b1fd5410da105bfba7a74ddff0928a654aca1ee211ac9dce8019ddcb"),
                    out_cipher_text: hex!("b52263ce44b2544a314355c1e8c8543f3ed3e883e7a7a8f9e3c7c11f41ab9069854fb21e9b3660a860df19d289d54b29d82522b32d187cde6261eb0a429c3994dff6f37b9ab9102281223e3cd584790a"),
                    zkproof: hex!("909e05ba0ea1a2d9aef8e571986e98e09312dccaf8e739d718a1edd217dc4c8a5c8a650015405b592a7c674a451d7d1686c7ea6d93e74a8fe4ade12b679ac780457f08a79bfbf96dcf7eefe9a39b99f1ae39d2c5f86aadf156b7d5ce4b2733f307cfe1e1ff6de0ff2006d9cba535b0c40dfb7a98399cdff8e681fc38c7b9aa94ee5eb89432e28d94ee27f238776ba964a87caf58eddbb64771e64de094305a8eb848d2d9ad6373903687d22170f48f1ae8d714514034ee2733857af4747312bb"),
                },
            ],
            binding_sig: hex!("6e6ce3918ede8c730bacc7821b81c1b93bb50b219e79e8e0d74531ed18c1145632d9847d38783b49141ac5353aaa7d125fb2934e681467e16b28090978e74e0b"),
        };

        let sighash = hex!("839321aa5e46473277cc3828564f2a7b60d3fb1264320d6c436e74e7ffc75888");

        let spend_vk = zcash::spend_vk();
        let output_vk = zcash::output_vk();

        let _ =
            accept_sapling(&spend_vk.into(), &output_vk.into(), &sighash, &test_sapling).unwrap();
    }
}
