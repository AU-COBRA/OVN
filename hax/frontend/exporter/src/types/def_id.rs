//! This module contains the type definition for `DefId` and the types
//! `DefId` depends on.
//!
//! This is purposely a very small isolated module:
//! `hax-engine-names-extract` uses those types, but we don't want
//! `hax-engine-names-extract` to have a build dependency on the whole
//! frontend, that double the build times for the Rust part of hax.
//!
//! The feature `extract_names_mode` exists only in the crate
//! `hax-engine-names-extract`, and is used to turn off the derive
//! attributes `AdtInto` and `JsonSchema`.

use hax_adt_into::derive_group;

#[cfg(not(feature = "extract_names_mode"))]
use crate::{AdtInto, JsonSchema};

#[cfg(all(not(feature = "extract_names_mode"), feature = "rustc"))]
use crate::{BaseState, SInto};

pub type Symbol = String;

#[derive_group(Serializers)]
#[derive(Clone, Debug, Hash, PartialEq, Eq, PartialOrd, Ord)]
#[cfg_attr(not(feature = "extract_names_mode"), derive(AdtInto, JsonSchema))]
#[cfg_attr(not(feature = "extract_names_mode"), args(<'a, S: BaseState<'a>>, from: rustc_hir::definitions::DisambiguatedDefPathData, state: S as s))]
/// Reflects [`rustc_hir::definitions::DisambiguatedDefPathData`]
pub struct DisambiguatedDefPathItem {
    pub data: DefPathItem,
    pub disambiguator: u32,
}

/// Reflects [`rustc_hir::def_id::DefId`]
#[derive_group(Serializers)]
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord)]
#[cfg_attr(not(feature = "extract_names_mode"), derive(JsonSchema))]
pub struct DefId {
    pub krate: String,
    pub path: Vec<DisambiguatedDefPathItem>,
    /// Rustc's `CrateNum` and `DefIndex` raw indexes. This can be
    /// useful if one needs to convert a [`DefId`] into a
    /// [`rustc_hir::def_id::DefId`]; there is a `From` instance for
    /// that purpose.
    ///
    /// **Warning: this `index` field might not be safe to use**. They are
    /// valid only for one Rustc sesssion. Please do not rely on those
    /// indexes unless you cannot do otherwise.
    pub index: (u32, u32),
    pub is_local: bool,
}

#[cfg(not(feature = "rustc"))]
impl std::fmt::Debug for DefId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("DefId")
            .field("krate", &self.krate)
            .field("path", &self.path)
            .finish()
    }
}

#[cfg(feature = "rustc")]
impl std::fmt::Debug for DefId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        // Use the more legible rustc debug implementation.
        write!(f, "{:?}", rustc_span::def_id::DefId::from(self))
    }
}

/// Reflects [`rustc_hir::definitions::DefPathData`]
#[derive_group(Serializers)]
#[derive(Clone, Debug, Hash, PartialEq, Eq, PartialOrd, Ord)]
#[cfg_attr(not(feature = "extract_names_mode"), derive(AdtInto, JsonSchema))]
#[cfg_attr(not(feature = "extract_names_mode"), args(<'ctx, S: BaseState<'ctx>>, from: rustc_hir::definitions::DefPathData, state: S as state))]
pub enum DefPathItem {
    CrateRoot,
    Impl,
    ForeignMod,
    Use,
    GlobalAsm,
    TypeNs(Symbol),
    ValueNs(Symbol),
    MacroNs(Symbol),
    LifetimeNs(Symbol),
    Closure,
    Ctor,
    AnonConst,
    OpaqueTy,
    AnonAdt,
}
