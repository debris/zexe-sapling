use crate::affine;
use algebra::Bls12_381;
use groth16::Proof;

pub fn read_proof(proof: [u8; 192]) -> Result<Proof<Bls12_381>, ()> {
    let mut a = [0u8; 48];
    let mut b = [0u8; 96];
    let mut c = [0u8; 48];

    a.copy_from_slice(&proof[..48]);
    b.copy_from_slice(&proof[48..48 + 96]);
    c.copy_from_slice(&proof[48 + 96..]);

    let proof = Proof {
        a: affine::read_compressed_g1affine(a)?,
        b: affine::read_compressed_g2affine(b)?,
        c: affine::read_compressed_g1affine(c)?,
    };

    Ok(proof)
}
