#![no_std]
#![feature(register_tool)]
#![register_tool(hax)]

#[hax_lib_macros::exclude]
extern crate hax_lib_macros;

#[hax_lib_macros::exclude]
use hax_lib_macros::*;

#[exclude]
use hacspec_concordium::*;


////////////
// Traits //
////////////

/** Interface for field implementation */
pub trait Field: core::marker::Copy + PartialEq + Eq + Clone + Copy + hacspec_concordium::Serialize {
    fn q() -> Self;

    fn random_field_elem(random: u32) -> Self;

    fn field_zero() -> Self;
    fn field_one() -> Self;

    fn add(x: Self, y: Self) -> Self;
    fn opp(x: Self) -> Self;

    fn mul(x: Self, y: Self) -> Self;
    fn inv(x: Self) -> Self;
}

/** Interface for group implementation */
pub trait Group: core::marker::Copy + PartialEq + Eq + Clone + Copy + hacspec_concordium::Serialize {
    type Z : Field;

    fn g() -> Self; // Generator (elemnent of group)

    fn g_pow(x: Self::Z) -> Self;
    fn pow(g: Self, x: Self::Z) -> Self; // TODO: Link with q
    fn group_one() -> Self;
    fn prod(x: Self, y: Self) -> Self;
    fn group_inv(x: Self) -> Self;

    fn hash(x: Vec<Self>) -> Self::Z;
}
