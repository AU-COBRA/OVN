// #![no_std]
// #![feature(register_tool)]
// #![register_tool(hax)]

// #[hax_lib_macros::exclude]
// extern crate hax_lib_macros;

// #[hax_lib_macros::exclude]
// use hax_lib_macros::*;

// #[exclude]
use concordium_std::*;

////////////
// Traits //
////////////

/** Interface for field implementation */
pub trait Field:
    core::marker::Copy + PartialEq + Eq + Clone + Copy + concordium_std::Serialize + std::fmt::Debug
{
    fn q() -> Self;

    fn random_field_elem(random: u128) -> Self;

    fn field_zero() -> Self;
    fn field_one() -> Self;

    fn add(x: Self, y: Self) -> Self;
    fn opp(x: Self) -> Self;

    fn mul(x: Self, y: Self) -> Self;
    fn inv(x: Self) -> Self;
}

/** Interface for group implementation */
pub trait Group:
    core::marker::Copy + PartialEq + Eq + Clone + Copy + concordium_std::Serialize + std::fmt::Debug
{
    type Z: Field;

    fn g() -> Self; // Generator (elemnent of group)
    
    fn g_pow(x: Self::Z) -> Self;
    fn pow(g: Self, x: Self::Z) -> Self; // TODO: Link with q
    fn group_one() -> Self;
    fn prod(x: Self, y: Self) -> Self;
    fn group_inv(x: Self) -> Self;

    fn hash(x: Vec<Self>) -> Self::Z;
}

////////////////////////
// Useful definitions //
////////////////////////

pub fn sub<Z: Field>(x: Z, y: Z) -> Z {
    Z::add(x, Z::opp(y))
}

pub fn div<G: Group>(x: G, y: G) -> G {
    G::prod(x, G::group_inv(y))
}
