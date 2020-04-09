use algebra::{
    bls12_381::{Fq, Fq2, G1Affine, G2Affine},
    bytes::FromBytes,
    curves::models::short_weierstrass_jacobian::GroupAffine,
    fields::{Field, PrimeField, SquareRootField},
    io::Cursor,
    prelude::Zero,
    BigInteger384, SWModelParameters,
};
use core::ops::{AddAssign, MulAssign, Neg};

pub fn read_g1affine(data: [u8; 96]) -> Result<G1Affine, ()> {
    let uncompressed = G1Uncompressed::new(data);
    uncompressed.into_affine()
}

pub fn read_g2affine(data: [u8; 192]) -> Result<G2Affine, ()> {
    let uncompressed = G2Uncompressed::new(data);
    uncompressed.into_affine()
}

pub fn read_compressed_g1affine(data: [u8; 48]) -> Result<G1Affine, ()> {
    let uncompressed = G1Compressed::new(data);
    uncompressed.into_affine()
}

pub fn read_compressed_g2affine(data: [u8; 96]) -> Result<G2Affine, ()> {
    let uncompressed = G2Compressed::new(data);
    uncompressed.into_affine()
}

fn read_fq(cursor: &mut Cursor<&[u8]>) -> Result<Fq, ()> {
    let mut bi = BigInteger384::read(cursor).map_err(|_e| ())?;
    let mut res: BigInteger384 = 0.into();
    for (i, res) in bi.as_mut().iter_mut().zip(res.as_mut().iter_mut().rev()) {
        *res = i.to_be();
    }

    Ok(Fq::from_repr(res))
}

struct G1Uncompressed {
    data: [u8; 96],
}

impl G1Uncompressed {
    fn new(data: [u8; 96]) -> Self {
        G1Uncompressed { data }
    }

    fn into_affine(&self) -> Result<G1Affine, ()> {
        let affine = self.into_affine_unchecked()?;

        if !affine.is_on_curve() {
            return Err(());
        } else if !affine.is_in_correct_subgroup_assuming_on_curve() {
            return Err(());
        } else {
            Ok(affine)
        }
    }

    fn into_affine_unchecked(&self) -> Result<G1Affine, ()> {
        // Create a copy of this representation.
        let mut copy = self.data;

        if copy[0] & (1 << 7) != 0 {
            // Distinguisher bit is set, but this should be uncompressed!
            return Err(());
        }

        if copy[0] & (1 << 6) != 0 {
            // This is the point at infinity, which means that if we mask away
            // the first two bits, the entire representation should consist
            // of zeroes.
            copy[0] &= 0x3f;

            if copy.iter().all(|b| *b == 0) {
                Ok(G1Affine::zero())
            } else {
                return Err(());
            }
        } else {
            if copy[0] & (1 << 5) != 0 {
                // The bit indicating the y-coordinate should be lexicographically
                // largest is set, but this is an uncompressed element.
                return Err(());
            }

            // Unset the three most significant bits.
            copy[0] &= 0x1f;

            let mut cursor = Cursor::new(&copy as &[u8]);
            let x = read_fq(&mut cursor)?;
            let y = read_fq(&mut cursor)?;

            Ok(G1Affine::new(x, y, false))
        }
    }
}

struct G2Uncompressed {
    data: [u8; 192],
}

impl G2Uncompressed {
    fn new(data: [u8; 192]) -> Self {
        G2Uncompressed { data }
    }

    fn into_affine(&self) -> Result<G2Affine, ()> {
        let affine = self.into_affine_unchecked()?;

        if !affine.is_on_curve() {
            return Err(());
        } else if !affine.is_in_correct_subgroup_assuming_on_curve() {
            return Err(());
        } else {
            Ok(affine)
        }
    }

    fn into_affine_unchecked(&self) -> Result<G2Affine, ()> {
        // Create a copy of this representation.
        let mut copy = self.data;

        if copy[0] & (1 << 7) != 0 {
            // Distinguisher bit is set, but this should be uncompressed!
            return Err(());
        }

        if copy[0] & (1 << 6) != 0 {
            // This is the point at infinity, which means that if we mask away
            // the first two bits, the entire representation should consist
            // of zeroes.
            copy[0] &= 0x3f;

            if copy.iter().all(|b| *b == 0) {
                Ok(G2Affine::zero())
            } else {
                Err(())
            }
        } else {
            if copy[0] & (1 << 5) != 0 {
                // The bit indicating the y-coordinate should be lexicographically
                // largest is set, but this is an uncompressed element.
                return Err(());
            }

            // Unset the three most significant bits.
            copy[0] &= 0x1f;

            let mut cursor = Cursor::new(&copy as &[u8]);
            let x_c1 = read_fq(&mut cursor)?;
            let x_c0 = read_fq(&mut cursor)?;
            let y_c1 = read_fq(&mut cursor)?;
            let y_c0 = read_fq(&mut cursor)?;

            Ok(G2Affine::new(
                Fq2::new(x_c0, x_c1),
                Fq2::new(y_c0, y_c1),
                false,
            ))
        }
    }
}

fn get_point_from_x<P: SWModelParameters>(
    x: P::BaseField,
    greatest: bool,
) -> Result<GroupAffine<P>, ()> {
    // Compute x^3 + b
    let mut x3b = x;
    x3b.square_in_place();
    x3b.mul_assign(&x);
    x3b.add_assign(&P::COEFF_B);

    x3b.sqrt()
        .map(|y| {
            let negy = y.neg();

            GroupAffine::new(x, if (y < negy) ^ greatest { y } else { negy }, false)
        })
        .ok_or_else(|| ())
}

struct G1Compressed {
    data: [u8; 48],
}

impl G1Compressed {
    fn new(data: [u8; 48]) -> Self {
        G1Compressed { data }
    }

    fn into_affine(&self) -> Result<G1Affine, ()> {
        let affine = self.into_affine_unchecked()?;

        // decompression guarantees that this is on the curve

        if !affine.is_in_correct_subgroup_assuming_on_curve() {
            return Err(());
        } else {
            Ok(affine)
        }
    }

    fn into_affine_unchecked(&self) -> Result<G1Affine, ()> {
        // Create a copy of this representation.
        let mut copy = self.data;

        if copy[0] & (1 << 7) == 0 {
            // Distinguisher bit is set, but this should be uncompressed!
            return Err(());
        }

        if copy[0] & (1 << 6) != 0 {
            // This is the point at infinity, which means that if we mask away
            // the first two bits, the entire representation should consist
            // of zeroes.
            copy[0] &= 0x3f;

            if copy.iter().all(|b| *b == 0) {
                Ok(G1Affine::zero())
            } else {
                return Err(());
            }
        } else {
            // Determine if the intended y coordinate must be greater
            // lexicographically.
            let greatest = copy[0] & (1 << 5) != 0;

            // Unset the three most significant bits.
            copy[0] &= 0x1f;

            let mut cursor = Cursor::new(&copy as &[u8]);
            let x = read_fq(&mut cursor)?;
            get_point_from_x(x, greatest)
        }
    }
}

struct G2Compressed {
    data: [u8; 96],
}

impl G2Compressed {
    fn new(data: [u8; 96]) -> Self {
        G2Compressed { data }
    }

    fn into_affine(&self) -> Result<G2Affine, ()> {
        let affine = self.into_affine_unchecked()?;

        // decompression guarantees that this is on the curve

        if !affine.is_in_correct_subgroup_assuming_on_curve() {
            return Err(());
        } else {
            Ok(affine)
        }
    }

    fn into_affine_unchecked(&self) -> Result<G2Affine, ()> {
        // Create a copy of this representation.
        let mut copy = self.data;

        if copy[0] & (1 << 7) == 0 {
            // Distinguisher bit is set, but this should be uncompressed!
            return Err(());
        }

        if copy[0] & (1 << 6) != 0 {
            // This is the point at infinity, which means that if we mask away
            // the first two bits, the entire representation should consist
            // of zeroes.
            copy[0] &= 0x3f;

            if copy.iter().all(|b| *b == 0) {
                Ok(G2Affine::zero())
            } else {
                return Err(());
            }
        } else {
            // Determine if the intended y coordinate must be greater
            // lexicographically.
            let greatest = copy[0] & (1 << 5) != 0;

            // Unset the three most significant bits.
            copy[0] &= 0x1f;

            let mut cursor = Cursor::new(&copy as &[u8]);
            let x_c1 = read_fq(&mut cursor)?;
            let x_c0 = read_fq(&mut cursor)?;
            get_point_from_x(Fq2::new(x_c0, x_c1), greatest)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::{read_g1affine, read_g2affine};
    use hex_literal::hex;

    #[test]
    fn test_readg1affine() {
        let t1 = hex!("0db882cf5db3e8567f16b4db1772d4d1f5a3fe8d62f0df2eb8a5cfa50806702afde8fc25335eb5ec859c2818b2610b2e19ab445dac720bb1f2b0cd3336f7a1acc62bf1b3a321826264dc7e469281e23b218394d598689da04e136878ff9a7897");
        let _value = read_g1affine(t1).unwrap();
    }

    #[test]
    fn test_readg2affine() {
        let t2 = hex!("0a416b8187450b28f025c421e3ff14d38f9abd9af2f1046b914b53ab37e9aebba683cb25284e5c22fa341129985250a103547de5d005df48265f7cb258162253d56fbc682d106a1ecb07666ebf7524a364e512c37aa62f82d6e7dd4ed8838478104376a98072766c29959358e9cde6a4985618f65ea257e8f288974f4aedde52e5dac2fb7ae5d30eab7cd828a2c8b15f15b16f139f2c33ef33d63befe404e696c97077d17ea42f4ff9d82ec456aaf43914a3d07968111a3a348f157e64c0278a");
        let _value = read_g2affine(t2).unwrap();
    }
}
