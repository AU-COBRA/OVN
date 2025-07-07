// // https://oeis.org/A132358
// // Prime: 115792089237316195423570985008687907853269984665640564039457584007913129639747 < 2^256

// pub use crate::ovn_traits::*;
// use hacspec_concordium::*;
// use hacspec_lib::{num::FromPrimitive, One};
// pub use num_bigint::BigUint;

// ////////////////////////////////////////////////////////////////////////////////////////////////
// // Impl for Z/bigintZ //
// ////////////////////////////////////////////////////////////////////////////////////////////////

// pub trait ZBigUintField : Sized
// {
//     fn q() -> Self;
// }

// #[derive(Clone, PartialEq, Eq, Debug)]
// pub struct z_115792089237316195423570985008687907853269984665640564039457584007913129639747 { z_val : BigUint }

// impl ZBigUintField for z_115792089237316195423570985008687907853269984665640564039457584007913129639747 {
//     fn q() -> Self {
//         z_115792089237316195423570985008687907853269984665640564039457584007913129639747{
//             z_val: BigUint::parse_bytes( b"115792089237316195423570985008687907853269984665640564039457584007913129639747", 10 ).unwrap()
//         }
//     }

//     fn to_bigint(self) -> BigUint {
//         self.z_val
//     }

//     fn from_bigint (x : BigUint) -> Self {
//         z_115792089237316195423570985008687907853269984665640564039457584007913129639747 {
//             z_val: x
//         }
//     }
// }

// impl hacspec_concordium::Deserial for dyn ZBigUintField {
//     // TODO:
//     fn deserial<R: Read>(source: &mut R) -> ParseResult<Self> {
//         let v: Vec<u8> = source.get()?;
//         Ok(Self::from_bigint(BigUint::from_radix_be(&v, 10).unwrap()))
//     }
// }

// // impl<Z : ZBigUintField> hacspec_concordium::Serial for Z {
// //     // TODO:
// //     fn serial<W: Write>(&self, out: &mut W) -> Result<(), W::Err> {
// //         Z::to_bigint().to_radix_be(10).serial(out)
// //     }
// // }

// // impl core::ops::Mul for z_bigint {
// //     type Output = Self;
// //     fn mul(self, y: Self) -> Self {
// //         let q_ = Self::q().z_val - BigUint::one();
// //         let x_: BigUint = self.z_val % q_.clone();
// //         let y_: BigUint = y.z_val % q_.clone();
// //         z_bigint {
// //             z_val: ((x_ * y_) % q_) as BigUint,
// //         }
// //     }
// // }

// // impl core::iter::Product for z_bigint {
// //     fn product<I: Iterator<Item = Self>>(iter: I) -> Self {
// //         iter.fold(
// //             z_bigint {
// //                 z_val: BigUint::one(),
// //             },
// //             |a, b| a * b,
// //         )
// //     }
// // }

// // impl core::ops::Add for z_bigint {
// //     type Output = Self;
// //     fn add(self, y: Self) -> Self {
// //         let q_ = Self::q().z_val - BigUint::one();
// //         let x_ = (self.z_val % q_.clone());
// //         let y_ = (y.z_val % q_.clone());
// //         z_bigint {
// //             z_val: (x_ + y_) % q_,
// //         }
// //     }
// // }

// // impl core::ops::Neg for z_bigint {
// //     type Output = Self;
// //     fn neg(self) -> Self {
// //         let q_ = Self::q().z_val - BigUint::one();
// //         let x_ = self.z_val % q_.clone();
// //         z_bigint { z_val: q_ - x_ }
// //     }
// // }

// // impl<const q: BigUint> Field for z_bigint {
// //     fn q() -> Self {
// //         z_bigint { z_val: q }
// //     } // Prime order
// //     fn random_field_elem(random: u128) -> Self {
// //         z_bigint {
// //             z_val: BigUint::from_u128(random).unwrap() % (Self::q().z_val - BigUint::one()),
// //         }
// //     }

// //     fn field_zero() -> Self {
// //         z_bigint {
// //             z_val: BigUint::ZERO,
// //         }
// //     }

// //     fn field_one() -> Self {
// //         z_bigint {
// //             z_val: BigUint::one(),
// //         }
// //     }

// //     fn inv(x: Self) -> Self {
// //         assert!(false); // Missing
// //         return x;
// //     }

// //     fn add(x: Self, y: Self) -> Self {
// //         x + y
// //     }

// //     fn opp(x: Self) -> Self {
// //         -x
// //     }

// //     fn mul(x: Self, y: Self) -> Self {
// //         x * y
// //     }
// // }

// // #[derive(Clone, PartialEq, Eq, Debug)]
// // pub struct g_z_bigint {
// //     g_val: BigUint,
// // }

// // impl hacspec_concordium::Deserial for g_z_bigint {
// //     // TODO:
// //     fn deserial<R: Read>(source: &mut R) -> ParseResult<Self> {
// //         let v: Vec<u8> = source.get()?;
// //         Ok(g_z_bigint {
// //             g_val: BigUint::from_radix_be(&v, 10).unwrap(),
// //         })
// //     }
// // }

// // impl hacspec_concordium::Serial for g_z_bigint {
// //     // TODO:
// //     fn serial<W: Write>(&self, out: &mut W) -> Result<(), W::Err> {
// //         self.g_val.to_radix_be(10).serial(out)
// //     }
// // }

// // impl core::ops::Mul for g_z_bigint {
// //     type Output = Self;
// //     fn mul(self, y: Self) -> Self {
// //         let q_ = z_bigint::q().z_val;
// //         let x_: BigUint = self.g_val % q_.clone();
// //         let y_: BigUint = y.g_val % q_.clone();
// //         g_z_bigint {
// //             g_val: (x_ * y_) % q_,
// //         }
// //     }
// // }

// // impl core::iter::Product for g_z_bigint {
// //     fn product<I: Iterator<Item = Self>>(iter: I) -> Self {
// //         iter.fold(
// //             g_z_bigint {
// //                 g_val: BigUint::one(),
// //             },
// //             |a, b| a * b,
// //         )
// //     }
// // }

// // impl<const q: BigUint> Group for g_z_bigint {
// //     type Z = z_bigint;

// //     #[warn(unused_doc_comment)]
// //     /// Found using the following python script:
// //     /// from sympy import isprime, primitive_root

// //     /// # Define the large prime number
// //     /// p = bigint

// //     /// # Check if it's prime
// //     /// print("Is prime:", isprime(p))

// //     /// # Find a generator (primitive root) of the multiplicative group modulo p
// //     /// g = primitive_root(p)
// //     /// print("Primitive root (generator) of Z_p^* is:", g)
// //     fn g() -> Self {
// //         g_z_bigint {
// //             g_val: BigUint::from_u8(2u8).unwrap(),
// //         }
// //     } // Generator (elemnent of group)

// //     fn hash(x: Vec<Self>) -> z_bigint {
// //         let mut res = z_bigint::field_one();
// //         for y in x {
// //             res = z_bigint { z_val: y.g_val } * res;
// //         }
// //         res // TODO
// //     }

// //     fn g_pow(x: z_bigint) -> Self {
// //         Self::pow(Self::g(), x)
// //     }

// //     // TODO: use repeated squaring instead!
// //     fn pow(g: Self, x: z_bigint) -> Self {
// //         let mut result = Self::group_one();
// //         let mut power = g;
// //         let mut exps = x.z_val % (z_bigint::q().z_val - BigUint::one());
// //         for _ in 0..256 {
// //             // exps is u256 so 256 is upper bound!
// //             // while exps > 0 {
// //             if (exps.clone() & BigUint::one()) == BigUint::one() {
// //                 result = Self::prod(result, power.clone());
// //             }
// //             power = Self::prod(power.clone(), power.clone());
// //             exps = exps >> 1;
// //         }
// //         result
// //     }

// //     fn group_one() -> Self {
// //         g_z_bigint {
// //             g_val: BigUint::one(),
// //         }
// //     }

// //     fn group_inv(x: Self) -> Self {
// //         // Fermat's little theorem x^-1 = x^(p-2)
// //         let p_sub_2 = z_bigint {
// //             z_val: q - BigUint::from_u8(2u8).unwrap(),
// //         };
// //         Self::pow(x, p_sub_2)
// //     }

// //     // fn div(x: Self, y: Self) -> Self {
// //     //     Self::prod(x, Self::inv(y))
// //     // }
// //     fn prod(x: Self, y: Self) -> Self {
// //         x * y
// //     }
// // }
