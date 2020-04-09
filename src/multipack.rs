use algebra::{
    fields::{Field, FpParameters, PrimeField},
    prelude::{One, Zero},
    ModelParameters,
};
use alloc::{vec, vec::Vec};
use core::ops::AddAssign;

pub fn bytes_to_bits_le(bytes: &[u8]) -> Vec<bool> {
    bytes
        .iter()
        .flat_map(|&v| (0..8).map(move |i| (v >> i) & 1 == 1))
        .collect()
}

pub fn compute_multipacking<E>(bits: &[bool]) -> Vec<E::ScalarField>
where
    E: ModelParameters,
    E::ScalarField: One + Zero + Zero,
{
    let mut result = vec![];

    for bits in bits.chunks(<E::ScalarField as PrimeField>::Params::CAPACITY as usize) {
        let mut cur = E::ScalarField::zero();
        let mut coeff = E::ScalarField::one();

        for bit in bits {
            if *bit {
                cur.add_assign(&coeff);
            }

            coeff.double_in_place();
        }

        result.push(cur);
    }

    result
}
