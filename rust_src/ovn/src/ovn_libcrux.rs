use hacspec_concordium::*;

// https://github.com/zkcrypto/group
use group::{
    // ff::Field,
    Group as ZkGroup, GroupEncoding,
};

use crate::ovn_traits::{Field, Group};

use bls12_381::{Gt};
type G = Gt;
type Z = <G as ZkGroup>::Scalar;

// use au_curves::bls12::*;
use libcrux_curve25519::hacl::*;

// type temp = group::ff::PrimeField;

////////////////////

// , hacspec_concordium::Serial, hacspec_concordium::Deserial
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Zzk { z_val : Z }

impl hacspec_concordium::Deserial for Zzk {
    // TODO:
    fn deserial<R: Read>(source: &mut R) -> ParseResult<Self> {
        let b : [u8; 32] = <_ as Deserial>::deserial(source)?;
        let z : Z = Z::from_bytes(&b).unwrap();
        // <G as ZkGroup>::Scalar::from(value)
        Ok(Zzk { z_val: z })
    }
}

impl hacspec_concordium::Serial for Zzk {
    // TODO:
    fn serial<W: Write>(&self, out: &mut W) -> Result<(), W::Err> {
        self.z_val.to_bytes().serial(out)
    }
}

impl core::ops::Mul for Zzk {
    type Output = Self;
    fn mul(self, o: Self) -> Self {
        Zzk { z_val: self.z_val * o.z_val }
    }
}

impl core::ops::Add for Zzk {
    type Output = Self;
    fn add(self, o: Self) -> Self {
        Zzk { z_val: self.z_val + o.z_val }
    }
}

impl core::ops::Neg for Zzk {
    type Output = Self;
    fn neg(self) -> Self {
        Zzk { z_val: self.z_val.neg() }
    }
}

impl Field for Zzk {
    fn q() -> Self {
        // TODO
        unimplemented!()
    } // Prime order
    fn random_field_elem(random: u128) -> Self {
        Zzk { z_val: group::ff::PrimeField::from_u128(random) }
        // TODO: Z::random()
        // unimplemented!()
    }

    fn field_zero() -> Self {
        Zzk { z_val: Z::zero() }
    }

    fn field_one() -> Self {
        Zzk { z_val: Z::one() }
    }

    fn inv(x: Self) -> Self {
        unimplemented!()
        // assert!(false); // Missing
        // return x;
    }

    fn add(x: Self, y: Self) -> Self {
        x + y
    }

    fn opp(x: Self) -> Self {
        -x
    }

    fn mul(x: Self, y: Self) -> Self {
        x * y
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Gzk { g_val : G }

impl hacspec_concordium::Deserial for Gzk {
    // TODO:
    fn deserial<R: Read>(source: &mut R) -> ParseResult<Self> {
        // unimplemented!()
        Ok(Gzk{g_val: G::identity()})
    }
}

impl hacspec_concordium::Serial for Gzk {
    // TODO:
    fn serial<W: Write>(&self, out: &mut W) -> Result<(), W::Err> {
        let x : Gt = self.g_val;
        UncompressedEncoding
        
        let bytes : &[u8] = <Gt as GroupEncoding>::to_bytes(x);
        bytes.serial(out)

        // let x : [u64; 6] = self.g_val.into(); // .0.c0.c0.c0.to_bytes().serial(out)?;
        // Ok(())

        // unimplemented!("serial")
        // Ok(())
    }
}

impl core::ops::Mul for Gzk {
    type Output = Self;
    fn mul(self, o: Self) -> Self {
        Gzk { g_val: self.g_val + o.g_val }
    }
}

impl Group for Gzk {
    type Z = Zzk;

    fn g() -> Self {
        Gzk { g_val: G::generator() }
    } // Generator (elemnent of group)

    fn hash(x: Vec<Self>) -> Self::Z {
        // let hash = blake2b("temp");
        // let val = Scalar::from_uniform_bytes(hash.as_array());

        // Self::Z::hash()

        Self::Z::field_one()
    }

    fn g_pow(x: Self::Z) -> Self {
        Gzk { g_val: G::generator() * x.z_val }
    }

    // TODO: use repeated squaring instead!
    fn pow(g: Self, x: Self::Z) -> Self {
        Gzk { g_val: g.g_val * x.z_val }
    }

    fn group_one() -> Self {
        Gzk { g_val: G::identity() }
    }

    fn group_inv(x: Self) -> Self {
        Gzk { g_val: -x.g_val } // inverse not negative? (same for curve?)
    }

    fn prod(x: Self, y: Self) -> Self {
        x * y
    }
}
