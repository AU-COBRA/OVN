// https://oeis.org/A132358
// Prime: 18446744073709551557 < 2^64

use hacspec_concordium::*;
pub use crate::ovn_traits::*;

////////////////////
// Impl for Z/18446744073709551557Z //
////////////////////

#[derive(Clone, Copy, PartialEq, Eq, hacspec_concordium::Serial, hacspec_concordium::Deserial, Debug)]
pub struct z_18446744073709551557 { z_val : u64 }

// impl hacspec_concordium::Deserial for z_18446744073709551557 {
//     // TODO:
//     fn deserial<R: Read>(source: &mut R) -> ParseResult<Self> {
//         let v : u8 = source.get()?;
//         Ok(z_18446744073709551557 {
//             z_val: v,
//         })
//     }
// }

// impl hacspec_concordium::Serial for z_18446744073709551557 {
//     // TODO:
//     fn serial<W: Write>(&self, out: &mut W) -> Result<(), W::Err> {
//         self.z_val.serial(out)
//     }
// }

impl core::ops::Mul for z_18446744073709551557 {
    type Output = Self;
    fn mul(self, y: Self) -> Self {
        let q_ = Self::q().z_val - 1;
        let x_ : u128 = (self.z_val % q_) as u128;
        let y_ : u128 = (y.z_val % q_) as u128;
        z_18446744073709551557{ z_val: ((x_ * y_) % (q_ as u128)) as u64 }
    }
}

impl core::iter::Product for z_18446744073709551557 {
    fn product<I: Iterator<Item = Self>>(iter: I) -> Self {
        iter.fold(
            z_18446744073709551557{ z_val: 1u64 },
            |a, b| a * b,
        )
    }
}

impl core::ops::Add for z_18446744073709551557 {
    type Output = Self;
    fn add(self, y: Self) -> Self {
        let q_ = Self::q().z_val - 1;
        let x_ = (self.z_val % q_) as u128;
        let y_ = (y.z_val % q_) as u128;
        z_18446744073709551557{ z_val: ((x_ + y_) % (q_ as u128)) as u64 }
    }
}

impl core::ops::Neg for z_18446744073709551557 {
    type Output = Self;
    fn neg(self) -> Self {
        let q_ = Self::q().z_val - 1;
        let x_ = self.z_val % q_;
        z_18446744073709551557{ z_val: q_ - x_ }
    }
}

impl Field for z_18446744073709551557 {
    fn q() -> Self {
        z_18446744073709551557{ z_val: 18446744073709551557u64}
    } // Prime order
    fn random_field_elem(random: u128) -> Self {
        z_18446744073709551557{ z_val: random as u64 % (Self::q().z_val - 1) }
    }

    fn field_zero() -> Self {
        z_18446744073709551557{ z_val: 0u64 }
    }

    fn field_one() -> Self {
        z_18446744073709551557{ z_val: 1u64 }
    }

    fn inv(x: Self) -> Self {
        assert!(false); // Missing
        return x;
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

#[derive(Clone, Copy, PartialEq, Eq, hacspec_concordium::Serial, hacspec_concordium::Deserial, Debug)]
pub struct g_z_18446744073709551557 { g_val : u64 }

// impl hacspec_concordium::Deserial for g_z_18446744073709551557 {
//     // TODO:
//     fn deserial<R: Read>(source: &mut R) -> ParseResult<Self> {
//         let v : u64 = source.get()?;

//         Ok(g_z_18446744073709551557 {
//             g_val: v,
//         })
//     }
// }

// impl hacspec_concordium::Serial for g_z_18446744073709551557 {
//     // TODO:
//     fn serial<W: Write>(&self, out: &mut W) -> Result<(), W::Err> {
//         self.g_val.serial(out)
//     }
// }

impl core::ops::Mul for g_z_18446744073709551557 {
    type Output = Self;
    fn mul(self, y: Self) -> Self {
        let q_ = z_18446744073709551557::q().z_val;
        let x_ = (self.g_val % q_) as u128;
        let y_ = (y.g_val % q_) as u128;
        g_z_18446744073709551557 { g_val: ((x_ * y_) % (q_ as u128)) as u64 }
    }
}

impl core::iter::Product for g_z_18446744073709551557 {
    fn product<I: Iterator<Item = Self>>(iter: I) -> Self {
        iter.fold(
            g_z_18446744073709551557 { g_val: 1 },
            |a, b| a * b,
        )
    }
}

impl Group for g_z_18446744073709551557 {
    type Z = z_18446744073709551557;

    #[warn(unused_doc_comment)]
    /// Found using the following python script:
    /// from sympy import isprime, primitive_root

    /// # Define the large prime number
    /// p = 18446744073709551557

    /// # Check if it's prime
    /// print("Is prime:", isprime(p))

    /// # Find a generator (primitive root) of the multiplicative group modulo p
    /// g = primitive_root(p)
    /// print("Primitive root (generator) of Z_p^* is:", g)
    fn g() -> Self {
        g_z_18446744073709551557 { g_val: 2u64 }
    } // Generator (elemnent of group)

    fn hash(x: Vec<Self>) -> z_18446744073709551557 {
        let mut res = z_18446744073709551557::field_one();
        for y in x {
            res = z_18446744073709551557{z_val: y.g_val} * res;
        }
        res // TODO
    }

    fn g_pow(x: z_18446744073709551557) -> Self {
        Self::pow(Self::g(), x)
    }

    // TODO: use repeated squaring instead!
    fn pow(g: Self, x: z_18446744073709551557) -> Self {
        let mut result = Self::group_one();
        let mut power = g;
        let mut exps : u64 = x.z_val % (z_18446744073709551557::q().z_val - 1);
        for _ in 0..64 { // exps is u64 so 64 is upper bound!
        // while exps > 0 {
            if (exps & 1) == 1 {
                result = Self::prod(result, power);
            }
            power = Self::prod(power, power);
            exps = exps >> 1;
        };
        result
    }

    fn group_one() -> Self {
        g_z_18446744073709551557 { g_val: 1 }
    }

    fn group_inv(x: Self) -> Self {
        // Fermat's little theorem x^-1 = x^(p-2)
        let p_sub_2 = z_18446744073709551557 { z_val: 18446744073709551557 - 2 };
        Self::pow(x, p_sub_2)
    }

    // fn div(x: Self, y: Self) -> Self {
    //     Self::prod(x, Self::inv(y))
    // }
    fn prod(x: Self, y: Self) -> Self {
        x * y
    }
}
