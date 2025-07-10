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
// use libcrux_curve25519::hacl::*;
// use libcrux_ed25519::*;
use libcrux_p256::*;

// type temp = group::ff::PrimeField;

////////////////////

// , hacspec_concordium::Serial, hacspec_concordium::Deserial
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Zzk { z_val : [u8; 32] }

impl hacspec_concordium::Deserial for Zzk {
    // TODO:
    fn deserial<R: Read>(source: &mut R) -> ParseResult<Self> {
        let bytes : [u8; 32] = <_ as Deserial>::deserial(source)?;
        Ok(Zzk{z_val: bytes })
    }
}

impl hacspec_concordium::Serial for Zzk {
    // TODO:
    fn serial<W: Write>(&self, out: &mut W) -> Result<(), W::Err> {
        self.z_val.serial(out)
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
pub struct Gzk { g_val : [u8; 32] }

impl hacspec_concordium::Deserial for Gzk {
    // TODO:
    fn deserial<R: Read>(source: &mut R) -> ParseResult<Self> {
        // unimplemented!()
        let bytes : [u8; 32] = <_ as Deserial>::deserial(source)?;
        Ok(Gzk{g_val: bytes })
    }
}

impl hacspec_concordium::Serial for Gzk {
    // TODO:
    fn serial<W: Write>(&self, out: &mut W) -> Result<(), W::Err> {
        self.g_val.serial(out)
    }
}

impl core::ops::Mul for Gzk {
    type Output = Self;
    fn mul(self, o: Self) -> Self {
        point_add();
        Gzk { g_val: self.g_val + o.g_val }
    }
}

impl Group for Gzk {
    type Z = Zzk;

    fn g() -> Self {
        Gzk { g_val: [
            9u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8,
            0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8,
        ] }
    } // Generator (elemnent of group)

    fn hash(x: Vec<Self>) -> Self::Z {
        // let hash = blake2b("temp");
        // let val = Scalar::from_uniform_bytes(hash.as_array());

        // Self::Z::hash()

        Self::Z::field_one()
    }

    fn g_pow(x: Self::Z) -> Self {
        let mut out = [0u8; 32];
        scalarmult(&mut out, &Self::g().g_val, &x.z_val);
        Gzk { g_val: out }
    }

    // TODO: use repeated squaring instead!
    fn pow(g: Self, x: Self::Z) -> Self {
        let mut out = [0u8; 32];
        point_mul(&mut out, &g.g_val, &x.z_val);
        Gzk { g_val: out }
    }

    fn group_one() -> Self {
        Self::g()
        // Gzk { g_val: G::identity() }
    }

    fn group_inv(x: Self) -> Self {
        Self::g()
        // Gzk { g_val: -x.g_val } // inverse not negative? (same for curve?)
    }

    fn prod(x: Self, y: Self) -> Self {
        Self::g()
        // x * y
    }
}
