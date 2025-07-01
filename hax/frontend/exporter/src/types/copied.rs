use crate::prelude::*;

#[cfg(feature = "rustc")]
use rustc_middle::ty;
#[cfg(feature = "rustc")]
use rustc_span::def_id::DefId as RDefId;

impl std::hash::Hash for DefId {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        let DefId {
            krate,
            path,
            index: _,    // intentionally discarding index
            is_local: _, // intentionally discarding is_local
        } = self;
        krate.hash(state);
        path.hash(state);
    }
}

#[cfg(feature = "rustc")]
impl<'s, S: BaseState<'s>> SInto<S, DefId> for rustc_hir::def_id::DefId {
    fn sinto(&self, s: &S) -> DefId {
        s.base().exported_def_ids.borrow_mut().insert(self.clone());
        let tcx = s.base().tcx;
        let def_path = tcx.def_path(self.clone());
        let krate = tcx.crate_name(def_path.krate);
        DefId {
            path: def_path.data.iter().map(|x| x.sinto(s)).collect(),
            krate: format!("{}", krate),
            index: (
                rustc_hir::def_id::CrateNum::as_u32(self.krate),
                rustc_hir::def_id::DefIndex::as_u32(self.index),
            ),
            is_local: self.is_local(),
        }
    }
}

#[cfg(feature = "rustc")]
impl From<&DefId> for rustc_span::def_id::DefId {
    fn from<'tcx>(def_id: &DefId) -> Self {
        let (krate, index) = def_id.index;
        Self {
            krate: rustc_hir::def_id::CrateNum::from_u32(krate),
            index: rustc_hir::def_id::DefIndex::from_u32(index),
        }
    }
}

// Impl to be able to use hax's `DefId` for many rustc queries.
#[cfg(feature = "rustc")]
impl rustc_middle::query::IntoQueryParam<RDefId> for &DefId {
    fn into_query_param(self) -> RDefId {
        self.into()
    }
}

#[cfg(feature = "rustc")]
impl std::convert::From<DefId> for Path {
    fn from(v: DefId) -> Vec<String> {
        std::iter::once(v.krate)
            .chain(v.path.into_iter().filter_map(|item| match item.data {
                DefPathItem::TypeNs(s)
                | DefPathItem::ValueNs(s)
                | DefPathItem::MacroNs(s)
                | DefPathItem::LifetimeNs(s) => Some(s),
                _ => None,
            }))
            .collect()
    }
}

pub type GlobalIdent = DefId;
#[cfg(feature = "rustc")]
impl<'tcx, S: UnderOwnerState<'tcx>> SInto<S, GlobalIdent> for rustc_hir::def_id::LocalDefId {
    fn sinto(&self, st: &S) -> DefId {
        self.to_def_id().sinto(st)
    }
}

/// Reflects [`rustc_middle::thir::LogicalOp`]
#[derive_group(Serializers)]
#[derive(AdtInto, Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
#[args(<'a, S>, from: rustc_middle::thir::LogicalOp, state: S as _s)]
pub enum LogicalOp {
    And,
    Or,
}

/// Reflects [`rustc_middle::thir::LintLevel`]
#[derive_group(Serializers)]
#[derive(AdtInto, Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
#[args(<'slt, S: UnderOwnerState<'slt> + HasThir<'slt>>, from: rustc_middle::thir::LintLevel, state: S as gstate)]
pub enum LintLevel {
    Inherited,
    Explicit(HirId),
}

/// Reflects [`rustc_ast::ast::AttrStyle`]
#[derive_group(Serializers)]
#[derive(AdtInto, Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
#[args(<S>, from: rustc_ast::ast::AttrStyle, state: S as _s)]
pub enum AttrStyle {
    Outer,
    Inner,
}

/// Reflects [`rustc_ast::ast::Attribute`]
#[derive_group(Serializers)]
#[derive(AdtInto, Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
#[args(<'tcx, S: BaseState<'tcx>>, from: rustc_ast::ast::Attribute, state: S as gstate)]
pub struct Attribute {
    pub kind: AttrKind,
    #[map(x.as_usize())]
    pub id: usize,
    pub style: AttrStyle,
    pub span: Span,
}

/// Reflects [`rustc_attr::InlineAttr`]
#[derive_group(Serializers)]
#[derive(AdtInto, Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
#[args(<'tcx, S: BaseState<'tcx>>, from: rustc_attr::InlineAttr, state: S as _s)]
pub enum InlineAttr {
    None,
    Hint,
    Always,
    Never,
}

/// Generic container for decorating items with a type, a span,
/// attributes and other meta-data.
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct Decorated<T> {
    pub ty: Ty,
    pub span: Span,
    pub contents: Box<T>,
    pub hir_id: Option<(usize, usize)>,
    pub attributes: Vec<Attribute>,
}

/// Reflects [`rustc_middle::mir::UnOp`]
#[derive_group(Serializers)]
#[derive(AdtInto, Copy, Clone, Debug, JsonSchema)]
#[args(<'slt, S: UnderOwnerState<'slt>>, from: rustc_middle::mir::UnOp, state: S as _s)]
pub enum UnOp {
    Not,
    Neg,
    PtrMetadata,
}

/// Reflects [`rustc_middle::mir::BinOp`]
#[derive_group(Serializers)]
#[derive(AdtInto, Copy, Clone, Debug, JsonSchema)]
#[args(<'slt, S: UnderOwnerState<'slt>>, from: rustc_middle::mir::BinOp, state: S as _s)]
pub enum BinOp {
    // We merge the checked and unchecked variants because in either case overflow is failure.
    #[custom_arm(
        rustc_middle::mir::BinOp::Add | rustc_middle::mir::BinOp::AddUnchecked => BinOp::Add,
    )]
    Add,
    #[custom_arm(
        rustc_middle::mir::BinOp::Sub | rustc_middle::mir::BinOp::SubUnchecked => BinOp::Sub,
    )]
    Sub,
    #[custom_arm(
        rustc_middle::mir::BinOp::Mul | rustc_middle::mir::BinOp::MulUnchecked => BinOp::Mul,
    )]
    Mul,
    AddWithOverflow,
    SubWithOverflow,
    MulWithOverflow,
    Div,
    Rem,
    BitXor,
    BitAnd,
    BitOr,
    #[custom_arm(
        rustc_middle::mir::BinOp::Shl | rustc_middle::mir::BinOp::ShlUnchecked => BinOp::Shl,
    )]
    Shl,
    #[custom_arm(
        rustc_middle::mir::BinOp::Shr | rustc_middle::mir::BinOp::ShrUnchecked => BinOp::Shr,
    )]
    Shr,
    Eq,
    Lt,
    Le,
    Ne,
    Ge,
    Gt,
    Cmp,
    Offset,
}

pub type Pat = Decorated<PatKind>;
pub type Expr = Decorated<ExprKind>;

/// Reflects [`rustc_middle::mir::BinOp`]
#[derive_group(Serializers)]
#[derive(AdtInto, Clone, Debug, JsonSchema)]
#[args(<'tcx, S: UnderOwnerState<'tcx> + HasThir<'tcx>>, from: rustc_middle::middle::region::ScopeData, state: S as gstate)]
pub enum ScopeData {
    Node,
    CallSite,
    Arguments,
    Destruction,
    IfThen,
    Remainder(FirstStatementIndex),
}

/// Reflects [`rustc_middle::mir::BinOp`]
#[derive_group(Serializers)]
#[derive(AdtInto, Clone, Debug, JsonSchema)]
#[args(<'tcx, S: UnderOwnerState<'tcx> + HasThir<'tcx>>, from: rustc_middle::middle::region::Scope, state: S as gstate)]
pub struct Scope {
    pub id: ItemLocalId,
    pub data: ScopeData,
}

#[cfg(feature = "rustc")]
impl<'tcx, S: UnderOwnerState<'tcx>> SInto<S, ConstantExpr> for rustc_middle::mir::Const<'tcx> {
    fn sinto(&self, s: &S) -> ConstantExpr {
        use rustc_middle::mir::Const;
        let tcx = s.base().tcx;
        match self {
            Const::Val(const_value, ty) => const_value_to_constant_expr(
                s,
                ty.clone(),
                const_value.clone(),
                rustc_span::DUMMY_SP,
            ),
            Const::Ty(_ty, c) => c.sinto(s),
            Const::Unevaluated(ucv, _ty) => {
                use crate::rustc_middle::query::Key;
                let span = tcx
                    .def_ident_span(ucv.def)
                    .unwrap_or_else(|| ucv.def.default_span(tcx));
                match self.translate_uneval(s, ucv.shrink(), span) {
                    TranslateUnevalRes::EvaluatedConstant(c) => c.sinto(s),
                    TranslateUnevalRes::GlobalName(c) => c,
                }
            }
        }
    }
}

// For ConstantKind we merge all the cases (Ty, Val, Unevaluated) into one
pub type ConstantKind = ConstantExpr;

#[cfg(feature = "rustc")]
impl<S> SInto<S, u64> for rustc_middle::mir::interpret::AllocId {
    fn sinto(&self, _: &S) -> u64 {
        self.0.get()
    }
}

#[cfg(feature = "rustc")]
impl<'tcx, S: UnderOwnerState<'tcx>> SInto<S, Box<Ty>> for rustc_middle::ty::Ty<'tcx> {
    fn sinto(&self, s: &S) -> Box<Ty> {
        Box::new(self.sinto(s))
    }
}

#[cfg(feature = "rustc")]
impl<'tcx, S: UnderOwnerState<'tcx>> SInto<S, Ty> for rustc_middle::ty::Ty<'tcx> {
    fn sinto(&self, s: &S) -> Ty {
        self.kind().sinto(s)
    }
}

/// Reflects [`rustc_hir::hir_id::HirId`]
#[derive_group(Serializers)]
#[derive(AdtInto, Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
#[args(<'tcx, S: BaseState<'tcx>>, from: rustc_hir::hir_id::HirId, state: S as gstate)]
pub struct HirId {
    owner: DefId,
    local_id: usize,
    // attrs: String
}
// TODO: If not working: See original

#[cfg(feature = "rustc")]
impl<'tcx, S: BaseState<'tcx>> SInto<S, DefId> for rustc_hir::hir_id::OwnerId {
    fn sinto(&self, s: &S) -> DefId {
        self.to_def_id().sinto(s)
    }
}

/// Reflects [`rustc_ast::ast::LitFloatType`]
#[derive_group(Serializers)]
#[derive(AdtInto, Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
#[args(<'tcx, S: BaseState<'tcx>>, from: rustc_ast::ast::LitFloatType, state: S as gstate)]
pub enum LitFloatType {
    Suffixed(FloatTy),
    Unsuffixed,
}
/// Reflects [`rustc_hir::Movability`]
#[derive_group(Serializers)]
#[derive(AdtInto, Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
#[args(<'tcx, S>, from: rustc_hir::Movability, state: S as _s)]
pub enum Movability {
    Static,
    Movable,
}

/// Reflects [`rustc_middle::infer::canonical::CanonicalTyVarKind`]
#[derive_group(Serializers)]
#[derive(AdtInto, Clone, Debug, JsonSchema)]
#[args(<'tcx, S: UnderOwnerState<'tcx>>, from: rustc_middle::infer::canonical::CanonicalTyVarKind, state: S as gstate)]
pub enum CanonicalTyVarKind {
    General(UniverseIndex),
    Int,
    Float,
}

/// Reflects [`rustc_middle::ty::ParamTy`]
#[derive_group(Serializers)]
#[derive(AdtInto, Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
#[args(<'tcx, S: UnderOwnerState<'tcx>>, from: rustc_middle::ty::ParamTy, state: S as gstate)]
pub struct ParamTy {
    pub index: u32,
    pub name: Symbol,
}

/// Reflects [`rustc_middle::ty::ParamConst`]
#[derive_group(Serializers)]
#[derive(AdtInto, Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
#[args(<S>, from: rustc_middle::ty::ParamConst, state: S as gstate)]
pub struct ParamConst {
    pub index: u32,
    pub name: Symbol,
}

/// A predicate without `Self`, for use in `dyn Trait`.
///
/// Reflects [`rustc_middle::ty::ExistentialPredicate`]
#[derive(AdtInto)]
#[args(<'tcx, S: UnderOwnerState<'tcx>>, from: rustc_middle::ty::ExistentialPredicate<'tcx>, state: S as state)]
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum ExistentialPredicate {
    /// E.g. `From<u64>`. Note that this isn't `T: From<u64>` with a given `T`, this is just
    /// `From<u64>`. Could be written `?: From<u64>`.
    Trait(ExistentialTraitRef),
    /// E.g. `Iterator::Item = u64`. Could be written `<? as Iterator>::Item = u64`.
    Projection(ExistentialProjection),
    /// E.g. `Send`.
    AutoTrait(DefId),
}

/// Reflects [`rustc_type_ir::ExistentialTraitRef`]
#[derive(AdtInto)]
#[args(<'tcx, S: UnderOwnerState<'tcx>>, from: rustc_type_ir::ExistentialTraitRef<ty::TyCtxt<'tcx>>, state: S as state)]
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct ExistentialTraitRef {
    pub def_id: DefId,
    pub args: Vec<GenericArg>,
}

/// Reflects [`rustc_type_ir::ExistentialProjection`]
#[derive(AdtInto)]
#[args(<'tcx, S: UnderOwnerState<'tcx>>, from: rustc_type_ir::ExistentialProjection<ty::TyCtxt<'tcx>>, state: S as state)]
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct ExistentialProjection {
    pub def_id: DefId,
    pub args: Vec<GenericArg>,
    pub term: Term,
}

/// Reflects [`rustc_middle::ty::DynKind`]
#[derive_group(Serializers)]
#[derive(AdtInto, Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
#[args(<S>, from: rustc_middle::ty::DynKind, state: S as _s)]
pub enum DynKind {
    Dyn,
    DynStar,
}

/// Reflects [`rustc_middle::ty::BoundTyKind`]
#[derive_group(Serializers)]
#[derive(AdtInto, Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
#[args(<'tcx, S: UnderOwnerState<'tcx>>, from: rustc_middle::ty::BoundTyKind, state: S as gstate)]
pub enum BoundTyKind {
    Anon,
    Param(DefId, Symbol),
}

/// Reflects [`rustc_middle::ty::BoundTy`]
#[derive_group(Serializers)]
#[derive(AdtInto, Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
#[args(<'tcx, S: UnderOwnerState<'tcx>>, from: rustc_middle::ty::BoundTy, state: S as gstate)]
pub struct BoundTy {
    pub var: BoundVar,
    pub kind: BoundTyKind,
}

/// Reflects [`rustc_middle::ty::BoundRegionKind`]
#[derive_group(Serializers)]
#[derive(AdtInto, Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
#[args(<'tcx, S: UnderOwnerState<'tcx>>, from: rustc_middle::ty::BoundRegionKind, state: S as gstate)]
pub enum BoundRegionKind {
    BrAnon,
    BrNamed(DefId, Symbol),
    BrEnv,
}

/// Reflects [`rustc_middle::ty::BoundRegion`]
#[derive_group(Serializers)]
#[derive(AdtInto, Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
#[args(<'tcx, S: UnderOwnerState<'tcx>>, from: rustc_middle::ty::BoundRegion, state: S as gstate)]
pub struct BoundRegion {
    pub var: BoundVar,
    pub kind: BoundRegionKind,
}

/// Reflects [`rustc_middle::ty::PlaceholderRegion`]
pub type PlaceholderRegion = Placeholder<BoundRegion>;
/// Reflects [`rustc_middle::ty::PlaceholderConst`]
pub type PlaceholderConst = Placeholder<BoundVar>;
/// Reflects [`rustc_middle::ty::PlaceholderType`]
pub type PlaceholderType = Placeholder<BoundTy>;

/// Reflects [`rustc_middle::ty::Placeholder`]
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct Placeholder<T> {
    pub universe: UniverseIndex,
    pub bound: T,
}

#[cfg(feature = "rustc")]
impl<'tcx, S: UnderOwnerState<'tcx>, T: SInto<S, U>, U> SInto<S, Placeholder<U>>
    for rustc_middle::ty::Placeholder<T>
{
    fn sinto(&self, s: &S) -> Placeholder<U> {
        Placeholder {
            universe: self.universe.sinto(s),
            bound: self.bound.sinto(s),
        }
    }
}

/// Reflects [`rustc_middle::infer::canonical::Canonical`]
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema)]
pub struct Canonical<T> {
    pub max_universe: UniverseIndex,
    pub variables: Vec<CanonicalVarInfo>,
    pub value: T,
}
/// Reflects [`rustc_middle::ty::CanonicalUserType`]
pub type CanonicalUserType = Canonical<UserType>;

#[cfg(feature = "rustc")]
impl<'tcx, S: UnderOwnerState<'tcx>, T: SInto<S, U>, U> SInto<S, Canonical<U>>
    for rustc_middle::infer::canonical::Canonical<'tcx, T>
{
    fn sinto(&self, s: &S) -> Canonical<U> {
        Canonical {
            max_universe: self.max_universe.sinto(s),
            variables: self.variables.iter().map(|v| v.kind.sinto(s)).collect(),
            value: self.value.sinto(s),
        }
    }
}

/// Reflects [`rustc_middle::infer::canonical::CanonicalVarKind`]
#[derive_group(Serializers)]
#[derive(AdtInto, Clone, Debug, JsonSchema)]
#[args(<'tcx, S: UnderOwnerState<'tcx>>, from: rustc_middle::infer::canonical::CanonicalVarKind<ty::TyCtxt<'tcx>>, state: S as gstate)]
pub enum CanonicalVarInfo {
    Ty(CanonicalTyVarKind),
    PlaceholderTy(PlaceholderType),
    Region(UniverseIndex),
    PlaceholderRegion(PlaceholderRegion),
    Const(UniverseIndex),
    PlaceholderConst(PlaceholderConst),
    Effect,
}

/// Reflects [`rustc_middle::ty::UserSelfTy`]
#[derive_group(Serializers)]
#[derive(AdtInto, Clone, Debug, JsonSchema)]
#[args(<'tcx, S: UnderOwnerState<'tcx>>, from: rustc_middle::ty::UserSelfTy<'tcx>, state: S as gstate)]
pub struct UserSelfTy {
    pub impl_def_id: DefId,
    pub self_ty: Ty,
}

/// Reflects [`rustc_middle::ty::UserArgs`]
#[derive_group(Serializers)]
#[derive(AdtInto, Clone, Debug, JsonSchema)]
#[args(<'tcx, S: UnderOwnerState<'tcx>>, from: rustc_middle::ty::UserArgs<'tcx>, state: S as gstate)]
pub struct UserArgs {
    pub args: Vec<GenericArg>,
    pub user_self_ty: Option<UserSelfTy>,
}

/// Reflects [`rustc_middle::ty::UserType`]: this is currently
/// disabled, and everything is printed as debug in the
/// [`UserType::Todo`] variant.
#[derive_group(Serializers)]
#[derive(AdtInto, Clone, Debug, JsonSchema)]
#[args(<'tcx, S: UnderOwnerState<'tcx>>, from: rustc_middle::ty::UserType<'tcx>, state: S as _s)]
pub enum UserType {
    // TODO: for now, we don't use user types at all.
    // We disable it for now, since it cause the following to fail:
    //
    //    pub const MY_VAL: u16 = 5;
    //    pub type Alias = MyStruct<MY_VAL>; // Using the literal 5, it goes through
    //
    //    pub struct MyStruct<const VAL: u16> {}
    //
    //    impl<const VAL: u16> MyStruct<VAL> {
    //        pub const MY_CONST: u16 = VAL;
    //    }
    //
    //    pub fn do_something() -> u32 {
    //        u32::from(Alias::MY_CONST)
    //    }
    //
    // In this case, we get a [rustc_middle::ty::ConstKind::Bound] in
    // [do_something], which we are not able to translate.
    // See: https://github.com/hacspec/hax/pull/209

    // Ty(Ty),
    // TypeOf(DefId, UserArgs),
    #[todo]
    Todo(String),
}

/// Reflects [`rustc_hir::def::CtorKind`]
#[derive_group(Serializers)]
#[derive(AdtInto, Clone, Debug, JsonSchema)]
#[args(<S>, from: rustc_hir::def::CtorKind, state: S as _s)]
pub enum CtorKind {
    Fn,
    Const,
}

/// Reflects [`rustc_hir::def::CtorOf`]
#[derive_group(Serializers)]
#[derive(AdtInto, Clone, Debug, JsonSchema)]
#[args(<S>, from: rustc_hir::def::CtorOf, state: S as _s)]
pub enum CtorOf {
    Struct,
    Variant,
}

/// Reflects [`rustc_middle::ty::VariantDiscr`]
#[derive_group(Serializers)]
#[derive(AdtInto, Clone, Debug, JsonSchema)]
#[args(<'tcx, S: UnderOwnerState<'tcx>>, from: rustc_middle::ty::VariantDiscr, state: S as gstate)]
pub enum DiscriminantDefinition {
    Explicit(DefId),
    Relative(u32),
}

/// Reflects [`rustc_middle::ty::util::Discr`]
#[derive_group(Serializers)]
#[derive(AdtInto, Clone, Debug, JsonSchema)]
#[args(<'tcx, S: UnderOwnerState<'tcx>>, from: rustc_middle::ty::util::Discr<'tcx>, state: S as gstate)]
pub struct DiscriminantValue {
    pub val: u128,
    pub ty: Ty,
}

/// Reflects [`rustc_middle::ty::Visibility`]
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema)]
pub enum Visibility<Id> {
    Public,
    Restricted(Id),
}

#[cfg(feature = "rustc")]
impl<S, T: SInto<S, U>, U> SInto<S, Visibility<U>> for rustc_middle::ty::Visibility<T> {
    fn sinto(&self, s: &S) -> Visibility<U> {
        use rustc_middle::ty::Visibility as T;
        match self {
            T::Public => Visibility::Public,
            T::Restricted(id) => Visibility::Restricted(id.sinto(s)),
        }
    }
}

/// Reflects [`rustc_middle::ty::FieldDef`]
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema)]
pub struct FieldDef {
    pub did: DefId,
    /// Field definition of [tuple
    /// structs](https://doc.rust-lang.org/book/ch05-01-defining-structs.html#using-tuple-structs-without-named-fields-to-create-different-types)
    /// are anonymous, in that case `name` is [`None`].
    pub name: Option<Symbol>,
    pub vis: Visibility<DefId>,
    pub ty: Ty,
    pub span: Span,
}

#[cfg(feature = "rustc")]
impl<'tcx, S: UnderOwnerState<'tcx>> SInto<S, FieldDef> for rustc_middle::ty::FieldDef {
    fn sinto(&self, s: &S) -> FieldDef {
        let tcx = s.base().tcx;
        let ty = {
            let generics = rustc_middle::ty::GenericArgs::identity_for_item(tcx, self.did);
            self.ty(tcx, generics).sinto(s)
        };
        let name = {
            let name = self.name.sinto(s);
            let is_user_provided = {
                // SH: Note that the only way I found of checking if the user wrote the name or if it
                // is just an integer generated by rustc is by checking if it is just made of
                // numerals...
                name.parse::<usize>().is_err()
            };
            is_user_provided.then_some(name)
        };

        FieldDef {
            did: self.did.sinto(s),
            name,
            vis: self.vis.sinto(s),
            ty,
            span: tcx.def_span(self.did).sinto(s),
        }
    }
}

/// Reflects [`rustc_middle::ty::VariantDef`]
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema)]
pub struct VariantDef {
    pub def_id: DefId,
    pub ctor: Option<(CtorKind, DefId)>,
    pub name: Symbol,
    pub discr_def: DiscriminantDefinition,
    pub discr_val: DiscriminantValue,
    /// The definitions of the fields on this variant. In case of
    /// [tuple
    /// structs](https://doc.rust-lang.org/book/ch05-01-defining-structs.html#using-tuple-structs-without-named-fields-to-create-different-types),
    /// the fields are anonymous, otherwise fields are named.
    pub fields: Vec<FieldDef>,
    /// Span of the definition of the variant
    pub span: Span,
}

#[cfg(feature = "rustc")]
impl VariantDef {
    fn sfrom<'tcx, S: UnderOwnerState<'tcx>>(
        s: &S,
        def: &ty::VariantDef,
        discr_val: ty::util::Discr<'tcx>,
    ) -> Self {
        VariantDef {
            def_id: def.def_id.sinto(s),
            ctor: def.ctor.sinto(s),
            name: def.name.sinto(s),
            discr_def: def.discr.sinto(s),
            discr_val: discr_val.sinto(s),
            fields: def.fields.raw.sinto(s),
            span: s.base().tcx.def_span(def.def_id).sinto(s),
        }
    }
}

/// Reflects [`rustc_middle::ty::EarlyParamRegion`]
#[derive_group(Serializers)]
#[derive(AdtInto, Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
#[args(<'tcx, S: UnderOwnerState<'tcx>>, from: rustc_middle::ty::EarlyParamRegion, state: S as gstate)]
pub struct EarlyParamRegion {
    pub index: u32,
    pub name: Symbol,
}

/// Reflects [`rustc_middle::ty::LateParamRegion`]
#[derive_group(Serializers)]
#[derive(AdtInto, Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
#[args(<'tcx, S: UnderOwnerState<'tcx>>, from: rustc_middle::ty::LateParamRegion, state: S as gstate)]
pub struct LateParamRegion {
    pub scope: DefId,
    pub bound_region: BoundRegionKind,
}

/// Reflects [`rustc_middle::ty::RegionKind`]
#[derive_group(Serializers)]
#[derive(AdtInto, Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
#[args(<'tcx, S: UnderOwnerState<'tcx>>, from: rustc_middle::ty::RegionKind<'tcx>, state: S as gstate)]
pub enum RegionKind {
    ReEarlyParam(EarlyParamRegion),
    ReBound(DebruijnIndex, BoundRegion),
    ReLateParam(LateParamRegion),
    ReStatic,
    ReVar(RegionVid),
    RePlaceholder(PlaceholderRegion),
    ReErased,
    ReError(ErrorGuaranteed),
}

/// Reflects [`rustc_middle::ty::Region`]
#[derive_group(Serializers)]
#[derive(AdtInto, Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
#[args(<'tcx, S: UnderOwnerState<'tcx>>, from: rustc_middle::ty::Region<'tcx>, state: S as s)]
pub struct Region {
    #[value(self.kind().sinto(s))]
    pub kind: RegionKind,
}

/// Reflects both [`rustc_middle::ty::GenericArg`] and [`rustc_middle::ty::GenericArgKind`]
#[derive_group(Serializers)]
#[derive(AdtInto, Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
#[args(<'tcx, S: UnderOwnerState<'tcx>>, from: rustc_middle::ty::GenericArgKind<'tcx>, state: S as s)]
pub enum GenericArg {
    Lifetime(Region),
    Type(Ty),
    Const(ConstantExpr),
}

#[cfg(feature = "rustc")]
impl<'tcx, S: UnderOwnerState<'tcx>> SInto<S, GenericArg> for rustc_middle::ty::GenericArg<'tcx> {
    fn sinto(&self, s: &S) -> GenericArg {
        self.unpack().sinto(s)
    }
}

#[cfg(feature = "rustc")]
impl<'tcx, S: UnderOwnerState<'tcx>> SInto<S, Vec<GenericArg>>
    for rustc_middle::ty::GenericArgsRef<'tcx>
{
    fn sinto(&self, s: &S) -> Vec<GenericArg> {
        self.iter().map(|v| v.unpack().sinto(s)).collect()
    }
}

/// Reflects both [`rustc_middle::ty::GenericArg`] and [`rustc_middle::ty::GenericArgKind`]
#[derive(AdtInto)]
#[args(<'tcx, S: BaseState<'tcx>>, from: rustc_ast::ast::LitIntType, state: S as gstate)]
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum LitIntType {
    Signed(IntTy),
    Unsigned(UintTy),
    Unsuffixed,
}

#[derive_group(Serializers)]
#[derive(AdtInto, Clone, Debug, JsonSchema)]
#[args(<'tcx, S: ExprState<'tcx>>, from: rustc_middle::thir::FruInfo<'tcx>, state: S as gstate)]
/// Field Record Update (FRU) informations, this reflects [`rustc_middle::thir::FruInfo`]
pub struct FruInfo {
    /// The base, e.g. `Foo {x: 1, .. base}`
    pub base: Expr,
    pub field_types: Vec<Ty>,
}

/// A field expression: a field name along with a value
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema)]
pub struct FieldExpr {
    pub field: DefId,
    pub value: Expr,
}

/// A field pattern: a field name along with a pattern
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema)]
pub struct FieldPat {
    pub field: DefId,
    pub pattern: Pat,
}

/// Reflects [`rustc_middle::thir::AdtExpr`]
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema)]
pub struct AdtExpr {
    pub info: VariantInformations,
    pub user_ty: Option<CanonicalUserType>,
    pub fields: Vec<FieldExpr>,
    pub base: Option<FruInfo>,
}

#[cfg(feature = "rustc")]
impl<'tcx, S: ExprState<'tcx>> SInto<S, AdtExpr> for rustc_middle::thir::AdtExpr<'tcx> {
    fn sinto(&self, s: &S) -> AdtExpr {
        let variants = self.adt_def.variants();
        let variant: &rustc_middle::ty::VariantDef = &variants[self.variant_index];
        AdtExpr {
            info: get_variant_information(&self.adt_def, self.variant_index, s),
            fields: self
                .fields
                .iter()
                .map(|f| FieldExpr {
                    field: variant.fields[f.name].did.sinto(s),
                    value: f.expr.sinto(s),
                })
                .collect(),
            base: self.base.sinto(s),
            user_ty: self.user_ty.sinto(s),
        }
    }
}

/// Reflects [`rustc_span::Loc`]
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Loc {
    pub line: usize,
    pub col: usize,
}

/// Reflects [`rustc_span::hygiene::DesugaringKind`]
#[derive_group(Serializers)]
#[derive(AdtInto, Clone, Debug, JsonSchema)]
#[args(<S>, from: rustc_span::hygiene::DesugaringKind, state: S as _s)]
pub enum DesugaringKind {
    CondTemporary,
    QuestionMark,
    TryBlock,
    YeetExpr,
    OpaqueTy,
    Async,
    Await,
    ForLoop,
    WhileLoop,
    BoundModifier,
}

/// Reflects [`rustc_span::hygiene::AstPass`]
#[derive_group(Serializers)]
#[derive(AdtInto, Clone, Debug, JsonSchema)]
#[args(<S>, from: rustc_span::hygiene::AstPass, state: S as _s)]
pub enum AstPass {
    StdImports,
    TestHarness,
    ProcMacroHarness,
}

/// Reflects [`rustc_span::hygiene::MacroKind`]
#[derive_group(Serializers)]
#[derive(AdtInto, Clone, Debug, JsonSchema)]
#[args(<S>, from: rustc_span::hygiene::MacroKind, state: S as _s)]
pub enum MacroKind {
    Bang,
    Attr,
    Derive,
}

/// Reflects [`rustc_span::hygiene::ExpnKind`]
#[derive(AdtInto)]
#[args(<'tcx, S: BaseState<'tcx>>, from: rustc_span::hygiene::ExpnKind, state: S as gstate)]
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema)]
pub enum ExpnKind {
    Root,
    Macro(MacroKind, Symbol),
    AstPass(AstPass),
    Desugaring(DesugaringKind),
}

/// Reflects [`rustc_span::edition::Edition`]
#[derive(AdtInto)]
#[args(<S>, from: rustc_span::edition::Edition, state: S as _s)]
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema)]
pub enum Edition {
    Edition2015,
    Edition2018,
    Edition2021,
    Edition2024,
}

/// Reflects [`rustc_span::hygiene::ExpnData`]
#[derive(AdtInto)]
#[args(<'tcx, S: BaseState<'tcx>>, from: rustc_span::hygiene::ExpnData, state: S as state)]
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema)]
pub struct ExpnData {
    pub kind: ExpnKind,
    // pub parent: Box<ExpnData>,
    pub call_site: Span,
    pub def_site: Span,
    #[map(x.as_ref().map(|x| x.clone().iter().map(|x|x.sinto(state)).collect()))]
    pub allow_internal_unstable: Option<Vec<Symbol>>,
    pub edition: Edition,
    pub macro_def_id: Option<DefId>,
    pub parent_module: Option<DefId>,
    pub local_inner_macros: bool,
}

/// Reflects [`rustc_span::Span`]
#[derive(::serde::Serialize, ::serde::Deserialize, Clone, Debug, JsonSchema, Eq, Ord)]
pub struct Span {
    pub lo: Loc,
    pub hi: Loc,
    pub filename: FileName,
    /// Original rustc span; can be useful for reporting rustc
    /// diagnostics (this is used in Charon)
    #[cfg(feature = "rustc")]
    #[serde(skip)]
    pub rust_span_data: Option<rustc_span::SpanData>,
    #[cfg(not(feature = "rustc"))]
    #[serde(skip)]
    pub rust_span_data: Option<()>,
    // expn_backtrace: Vec<ExpnData>,
}

/// We need to define manual `impl`s of `Span`: we want to skip the
/// field `rust_span_data`. The derive macros from `bincode` don't
/// allow that, see https://github.com/bincode-org/bincode/issues/452.
const _: () = {
    impl bincode::Encode for Span {
        fn encode<E: bincode::enc::Encoder>(
            &self,
            encoder: &mut E,
        ) -> core::result::Result<(), bincode::error::EncodeError> {
            bincode::Encode::encode(&self.lo, encoder)?;
            bincode::Encode::encode(&self.hi, encoder)?;
            bincode::Encode::encode(&self.filename, encoder)?;
            Ok(())
        }
    }

    impl bincode::Decode for Span {
        fn decode<D: bincode::de::Decoder>(
            decoder: &mut D,
        ) -> core::result::Result<Self, bincode::error::DecodeError> {
            Ok(Self {
                lo: bincode::Decode::decode(decoder)?,
                hi: bincode::Decode::decode(decoder)?,
                filename: bincode::Decode::decode(decoder)?,
                rust_span_data: None,
            })
        }
    }

    impl<'de> bincode::BorrowDecode<'de> for Span {
        fn borrow_decode<D: bincode::de::BorrowDecoder<'de>>(
            decoder: &mut D,
        ) -> core::result::Result<Self, bincode::error::DecodeError> {
            Ok(Self {
                lo: bincode::BorrowDecode::borrow_decode(decoder)?,
                hi: bincode::BorrowDecode::borrow_decode(decoder)?,
                filename: bincode::BorrowDecode::borrow_decode(decoder)?,
                rust_span_data: None,
            })
        }
    }
};

const _: () = {
    // `rust_span_data` is a metadata that should *not* be taken into
    // account while hashing or comparing

    impl std::hash::Hash for Span {
        fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
            self.lo.hash(state);
            self.hi.hash(state);
            self.filename.hash(state);
        }
    }
    impl PartialEq for Span {
        fn eq(&self, other: &Self) -> bool {
            self.lo == other.lo && self.hi == other.hi && self.filename == other.filename
        }
    }

    impl PartialOrd for Span {
        fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
            Some(
                self.lo.partial_cmp(&other.lo)?.then(
                    self.hi
                        .partial_cmp(&other.hi)?
                        .then(self.filename.partial_cmp(&other.filename)?),
                ),
            )
        }
    }
};

#[cfg(feature = "rustc")]
impl Into<Loc> for rustc_span::Loc {
    fn into(self) -> Loc {
        Loc {
            line: self.line,
            col: self.col_display,
        }
    }
}

#[cfg(feature = "rustc")]
impl<'tcx, S: BaseState<'tcx>> SInto<S, Span> for rustc_span::Span {
    fn sinto(&self, s: &S) -> Span {
        let set: crate::state::ExportedSpans = s.base().exported_spans;
        set.borrow_mut().insert(self.clone());
        translate_span(self.clone(), s.base().tcx.sess)
    }
}

/// Reflects [`rustc_middle::thir::LocalVarId`]
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema)]
pub struct LocalIdent {
    pub name: String,
    pub id: HirId,
}

#[cfg(feature = "rustc")]
impl<'tcx, S: UnderOwnerState<'tcx>> SInto<S, LocalIdent> for rustc_middle::thir::LocalVarId {
    fn sinto(&self, s: &S) -> LocalIdent {
        LocalIdent {
            name: s
                .base()
                .local_ctx
                .borrow()
                .vars
                .get(self)
                .clone()
                .s_unwrap(s)
                .to_string(),
            id: self.clone().0.sinto(s),
        }
    }
}

/// Reflects [`rustc_span::source_map::Spanned`]
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema)]
pub struct Spanned<T> {
    pub node: T,
    pub span: Span,
}
#[cfg(feature = "rustc")]
impl<'s, S: UnderOwnerState<'s>, T: SInto<S, U>, U> SInto<S, Spanned<U>>
    for rustc_span::source_map::Spanned<T>
{
    fn sinto<'a>(&self, s: &S) -> Spanned<U> {
        Spanned {
            node: self.node.sinto(s),
            span: self.span.sinto(s),
        }
    }
}

impl<'tcx, S> SInto<S, PathBuf> for PathBuf {
    fn sinto(&self, _: &S) -> PathBuf {
        self.clone()
    }
}

/// Reflects [`rustc_span::RealFileName`]
#[derive_group(Serializers)]
#[derive(AdtInto, Clone, Debug, JsonSchema, PartialEq, Eq, Hash, PartialOrd, Ord)]
#[args(<S>, from: rustc_span::RealFileName, state: S as _s)]
pub enum RealFileName {
    LocalPath(PathBuf),
    Remapped {
        local_path: Option<PathBuf>,
        virtual_name: PathBuf,
    },
}

#[cfg(feature = "rustc")]
impl<S> SInto<S, u64> for rustc_data_structures::stable_hasher::Hash64 {
    fn sinto(&self, _: &S) -> u64 {
        self.as_u64()
    }
}

/// Reflects [`rustc_span::FileName`]
#[derive(AdtInto)]
#[args(<S>, from: rustc_span::FileName, state: S as gstate)]
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum FileName {
    Real(RealFileName),
    QuoteExpansion(u64),
    Anon(u64),
    MacroExpansion(u64),
    ProcMacroSourceCode(u64),
    CliCrateAttr(u64),
    Custom(String),
    // #[map(FileName::DocTest(x.0.to_str().unwrap().into()))]
    #[custom_arm(FROM_TYPE::DocTest(x, _) => TO_TYPE::DocTest(x.to_str().unwrap().into()),)]
    DocTest(String),
    InlineAsm(u64),
}

impl FileName {
    pub fn to_string(&self) -> String {
        match self {
            Self::Real(RealFileName::LocalPath(path))
            | Self::Real(RealFileName::Remapped {
                local_path: Some(path),
                ..
            })
            | Self::Real(RealFileName::Remapped {
                virtual_name: path, ..
            }) => format!("{}", path.display()),
            _ => format!("{:?}", self),
        }
    }
    pub fn to_path(&self) -> Option<&std::path::Path> {
        match self {
            Self::Real(RealFileName::LocalPath(path))
            | Self::Real(RealFileName::Remapped {
                local_path: Some(path),
                ..
            })
            | Self::Real(RealFileName::Remapped {
                virtual_name: path, ..
            }) => Some(path),
            _ => None,
        }
    }
}

/// Reflects partially [`rustc_middle::ty::InferTy`]
#[derive_group(Serializers)]
#[derive(AdtInto, Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
#[args(<'tcx, S>, from: rustc_middle::ty::InferTy, state: S as gstate)]
pub enum InferTy {
    #[custom_arm(FROM_TYPE::TyVar(..) => TO_TYPE::TyVar,)]
    TyVar, /*TODO?*/
    #[custom_arm(FROM_TYPE::IntVar(..) => TO_TYPE::IntVar,)]
    IntVar, /*TODO?*/
    #[custom_arm(FROM_TYPE::FloatVar(..) => TO_TYPE::FloatVar,)]
    FloatVar, /*TODO?*/
    FreshTy(u32),
    FreshIntTy(u32),
    FreshFloatTy(u32),
}

/// Reflects [`rustc_middle::thir::BlockSafety`]
#[derive_group(Serializers)]
#[derive(AdtInto, Clone, Debug, JsonSchema)]
#[args(<'tcx, S>, from: rustc_middle::thir::BlockSafety, state: S as _s)]
pub enum BlockSafety {
    Safe,
    BuiltinUnsafe,
    #[custom_arm(FROM_TYPE::ExplicitUnsafe{..} => BlockSafety::ExplicitUnsafe,)]
    ExplicitUnsafe,
}

/// Reflects [`rustc_middle::thir::Block`]
#[derive_group(Serializers)]
#[derive(AdtInto, Clone, Debug, JsonSchema)]
#[args(<'tcx, S: ExprState<'tcx>>, from: rustc_middle::thir::Block, state: S as gstate)]
pub struct Block {
    pub targeted_by_break: bool,
    pub region_scope: Scope,
    pub span: Span,
    pub stmts: Vec<Stmt>,
    pub expr: Option<Expr>,
    pub safety_mode: BlockSafety,
}

/// Reflects [`rustc_ast::ast::BindingMode`]
#[derive(AdtInto)]
#[args(<S>, from: rustc_ast::ast::BindingMode, state: S as s)]
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema)]
pub struct BindingMode {
    #[value(self.0.sinto(s))]
    pub by_ref: ByRef,
    #[value(self.1.sinto(s))]
    pub mutability: Mutability,
}

/// Reflects [`rustc_ast::ast::ByRef`]
#[derive(AdtInto)]
#[args(<S>, from: rustc_ast::ast::ByRef, state: S as s)]
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema)]
pub enum ByRef {
    Yes(Mutability),
    No,
}

/// Reflects [`rustc_middle::thir::Stmt`]
#[derive(AdtInto)]
#[args(<'tcx, S: ExprState<'tcx>>, from: rustc_middle::thir::Stmt<'tcx>, state: S as s)]
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema)]
pub struct Stmt {
    pub kind: StmtKind,
}

/// Reflects [`rustc_ast::token::Delimiter`]
#[derive(AdtInto)]
#[args(<S>, from: rustc_ast::token::Delimiter, state: S as _s)]
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum Delimiter {
    Parenthesis,
    Brace,
    Bracket,
    Invisible,
}

/// Reflects [`rustc_ast::tokenstream::TokenTree`]
#[derive(AdtInto)]
#[args(<'tcx, S: UnderOwnerState<'tcx>>, from: rustc_ast::tokenstream::TokenTree, state: S as s)]
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum TokenTree {
    Token(Token, Spacing),
    Delimited(DelimSpan, DelimSpacing, Delimiter, TokenStream),
}

/// Reflects [`rustc_ast::tokenstream::Spacing`]
#[derive(AdtInto)]
#[args(<'tcx, S: UnderOwnerState<'tcx>>, from: rustc_ast::tokenstream::Spacing, state: S as _s)]
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum Spacing {
    Alone,
    Joint,
    JointHidden,
}

/// Reflects [`rustc_ast::token::BinOpToken`]
#[derive(AdtInto)]
#[args(<S>, from: rustc_ast::token::BinOpToken, state: S as _s)]
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum BinOpToken {
    Plus,
    Minus,
    Star,
    Slash,
    Percent,
    Caret,
    And,
    Or,
    Shl,
    Shr,
}

/// Reflects [`rustc_ast::token::TokenKind`]
#[derive(AdtInto)]
#[args(<'tcx, S: UnderOwnerState<'tcx>>, from: rustc_ast::token::TokenKind, state: S as gstate)]
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum TokenKind {
    Eq,
    Lt,
    Le,
    EqEq,
    Ne,
    Ge,
    Gt,
    AndAnd,
    OrOr,
    Not,
    Tilde,
    BinOp(BinOpToken),
    BinOpEq(BinOpToken),
    At,
    Dot,
    DotDot,
    DotDotDot,
    DotDotEq,
    Comma,
    Semi,
    Colon,
    RArrow,
    LArrow,
    FatArrow,
    Pound,
    Dollar,
    Question,
    SingleQuote,
    OpenDelim(Delimiter),
    CloseDelim(Delimiter),
    // Literal(l: Lit),
    Ident(Symbol, bool),
    Lifetime(Symbol),
    // Interpolated(n: Nonterminal),
    // DocComment(k: CommentKind, ats: AttrStyle, s: Symbol),
    Eof,
    #[todo]
    Todo(String),
}

#[cfg(feature = "rustc")]
impl<S> SInto<S, bool> for rustc_ast::token::IdentIsRaw {
    fn sinto(&self, _s: &S) -> bool {
        match self {
            Self::Yes => true,
            Self::No => false,
        }
    }
}

/// Reflects [`rustc_ast::token::Token`]
#[derive(AdtInto)]
#[args(<'tcx, S: UnderOwnerState<'tcx>>, from: rustc_ast::token::Token, state: S as gstate)]
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct Token {
    pub kind: TokenKind,
    pub span: Span,
}

/// Reflects [`rustc_ast::ast::DelimArgs`]
#[derive(AdtInto)]
#[args(<S>, from: rustc_ast::ast::DelimArgs, state: S as gstate)]
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct DelimArgs {
    pub dspan: DelimSpan,
    pub delim: Delimiter,
    pub tokens: TokenStream,
}

/// Reflects [`rustc_ast::ast::MacCall`]
#[derive(AdtInto)]
#[args(<'tcx, S: UnderOwnerState<'tcx>>, from: rustc_ast::ast::MacCall, state: S as gstate)]
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct MacCall {
    #[map(x.segments.iter().map(|rustc_ast::ast::PathSegment{ident, ..}| ident.as_str().into()).collect())]
    pub path: Path,
    pub args: DelimArgs,
}

/// Reflects [`rustc_ast::tokenstream::TokenStream`] as a plain
/// string. If you need to reshape that into Rust tokens or construct,
/// please use, e.g., `syn`.
pub type TokenStream = String;
#[cfg(feature = "rustc")]
impl<'t, S> SInto<S, TokenStream> for rustc_ast::tokenstream::TokenStream {
    fn sinto(&self, _: &S) -> String {
        rustc_ast_pretty::pprust::tts_to_string(self)
    }
}

#[cfg(feature = "rustc")]
impl<'tcx, S: ExprState<'tcx>> SInto<S, Block> for rustc_middle::thir::BlockId {
    fn sinto(&self, s: &S) -> Block {
        s.thir().blocks[*self].sinto(s)
    }
}

#[cfg(feature = "rustc")]
impl<'tcx, S: ExprState<'tcx>> SInto<S, Stmt> for rustc_middle::thir::StmtId {
    fn sinto(&self, s: &S) -> Stmt {
        s.thir().stmts[*self].sinto(s)
    }
}

#[cfg(feature = "rustc")]
impl<'tcx, S: ExprState<'tcx>> SInto<S, Expr> for rustc_middle::thir::Expr<'tcx> {
    fn sinto(&self, s: &S) -> Expr {
        let (hir_id, attributes) = self.hir_id_and_attributes(s);
        let hir_id = hir_id.map(|hir_id| hir_id.index());
        let unrolled = self.unroll_scope(s);
        let rustc_middle::thir::Expr { span, kind, ty, .. } = unrolled;
        let contents = match macro_invocation_of_span(span, s).map(ExprKind::MacroInvokation) {
            Some(contents) => contents,
            None => match kind {
                // Introduce intermediate `Cast` from `T` to `U` when casting from a `#[repr(T)]` enum to `U`
                rustc_middle::thir::ExprKind::Cast { source } => {
                    if let rustc_middle::ty::TyKind::Adt(def, _) = s.thir().exprs[source].ty.kind()
                    {
                        let tcx = s.base().tcx;
                        let contents = kind.sinto(s);
                        use crate::rustc_middle::ty::util::IntTypeExt;
                        let repr_type = tcx
                            .repr_options_of_def(def.did().expect_local())
                            .discr_type()
                            .to_ty(s.base().tcx);
                        if repr_type == ty {
                            contents
                        } else {
                            ExprKind::Cast {
                                source: Decorated {
                                    ty: repr_type.sinto(s),
                                    span: span.sinto(s),
                                    contents: Box::new(contents),
                                    hir_id,
                                    attributes: vec![],
                                },
                            }
                        }
                    } else {
                        kind.sinto(s)
                    }
                }
                rustc_middle::thir::ExprKind::NonHirLiteral { lit, .. } => {
                    let cexpr: ConstantExpr =
                        (ConstantExprKind::Literal(scalar_int_to_constant_literal(s, lit, ty)))
                            .decorate(ty.sinto(s), span.sinto(s));
                    return cexpr.into();
                }
                rustc_middle::thir::ExprKind::ZstLiteral { .. } => match ty.kind() {
                    rustc_middle::ty::TyKind::FnDef(def, _generics) => {
                        /* TODO: translate generics
                        let tcx = s.base().tcx;
                        let sig = &tcx.fn_sig(*def).instantiate(tcx, generics);
                        let ret: rustc_middle::ty::Ty = tcx.erase_late_bound_regions(sig.output());
                        let inputs = sig.inputs();
                        let indexes = inputs.skip_binder().iter().enumerate().map(|(i, _)| i);
                        let params = indexes.map(|i| inputs.map_bound(|tys| tys[i]));
                        let params: Vec<rustc_middle::ty::Ty> =
                        params.map(|i| tcx.erase_late_bound_regions(i)).collect();
                        */
                        return Expr {
                            contents: Box::new(ExprKind::GlobalName { id: def.sinto(s) }),
                            span: self.span.sinto(s),
                            ty: ty.sinto(s),
                            hir_id,
                            attributes,
                        };
                    }
                    _ => {
                        if ty.is_phantom_data() {
                            let rustc_middle::ty::Adt(def, _) = ty.kind() else {
                                supposely_unreachable_fatal!(s[span], "PhantomDataNotAdt"; {kind, ty})
                            };
                            let adt_def = AdtExpr {
                                info: get_variant_information(
                                    def,
                                    rustc_target::abi::FIRST_VARIANT,
                                    s,
                                ),
                                user_ty: None,
                                base: None,
                                fields: vec![],
                            };
                            return Expr {
                                contents: Box::new(ExprKind::Adt(adt_def)),
                                span: self.span.sinto(s),
                                ty: ty.sinto(s),
                                hir_id,
                                attributes,
                            };
                        } else {
                            supposely_unreachable!(
                                s[span],
                                "ZstLiteral ty≠FnDef(...) or PhantomData";
                                {kind, span, ty}
                            );
                            kind.sinto(s)
                        }
                    }
                },
                rustc_middle::thir::ExprKind::Field {
                    lhs,
                    variant_index,
                    name,
                } => {
                    let lhs_ty = s.thir().exprs[lhs].ty.kind();
                    let idx = variant_index.index();
                    if idx != 0 {
                        let _ = supposely_unreachable!(
                            s[span],
                            "ExprKindFieldIdxNonZero"; {
                                kind,
                                span,
                                ty,
                                ty.kind()
                            }
                        );
                    };
                    match lhs_ty {
                        rustc_middle::ty::TyKind::Adt(adt_def, _generics) => {
                            let variant = adt_def.variant(variant_index);
                            ExprKind::Field {
                                field: variant.fields[name].did.sinto(s),
                                lhs: lhs.sinto(s),
                            }
                        }
                        rustc_middle::ty::TyKind::Tuple(..) => ExprKind::TupleField {
                            field: name.index(),
                            lhs: lhs.sinto(s),
                        },
                        _ => supposely_unreachable_fatal!(
                            s[span],
                            "ExprKindFieldBadTy"; {
                                kind,
                                span,
                                ty.kind(),
                                lhs_ty
                            }
                        ),
                    }
                }
                _ => kind.sinto(s),
            },
        };
        Decorated {
            ty: ty.sinto(s),
            span: span.sinto(s),
            contents: Box::new(contents),
            hir_id,
            attributes,
        }
    }
}

#[cfg(feature = "rustc")]
impl<'tcx, S: ExprState<'tcx>> SInto<S, Expr> for rustc_middle::thir::ExprId {
    fn sinto(&self, s: &S) -> Expr {
        s.thir().exprs[*self].sinto(s)
    }
}

#[cfg(feature = "rustc")]
impl<'tcx, S: ExprState<'tcx>> SInto<S, Pat> for rustc_middle::thir::Pat<'tcx> {
    fn sinto(&self, s: &S) -> Pat {
        let rustc_middle::thir::Pat { span, kind, ty } = self;
        let contents = match kind {
            rustc_middle::thir::PatKind::Leaf { subpatterns } => match ty.kind() {
                rustc_middle::ty::TyKind::Adt(adt_def, args) => {
                    (rustc_middle::thir::PatKind::Variant {
                        adt_def: adt_def.clone(),
                        args,
                        variant_index: rustc_target::abi::VariantIdx::from_usize(0),
                        subpatterns: subpatterns.clone(),
                    })
                    .sinto(s)
                }
                rustc_middle::ty::TyKind::Tuple(..) => PatKind::Tuple {
                    subpatterns: subpatterns
                        .iter()
                        .map(|pat| pat.pattern.clone())
                        .collect::<Vec<_>>()
                        .sinto(s),
                },
                _ => supposely_unreachable_fatal!(
                    s[span],
                    "PatLeafNonAdtTy";
                    {ty.kind(), kind}
                ),
            },
            _ => kind.sinto(s),
        };
        Decorated {
            ty: ty.sinto(s),
            span: span.sinto(s),
            contents: Box::new(contents),
            hir_id: None,
            attributes: vec![],
        }
    }
}

#[cfg(feature = "rustc")]
impl<'tcx, S: ExprState<'tcx>> SInto<S, Arm> for rustc_middle::thir::ArmId {
    fn sinto(&self, s: &S) -> Arm {
        s.thir().arms[*self].sinto(s)
    }
}

/// Reflects [`rustc_type_ir::IntTy`]
#[derive(AdtInto)]
#[args(<S>, from: rustc_type_ir::IntTy, state: S as _s)]
#[derive_group(Serializers)]
#[derive(Copy, Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum IntTy {
    Isize,
    I8,
    I16,
    I32,
    I64,
    I128,
}

/// Reflects [`rustc_type_ir::FloatTy`]
#[derive(AdtInto)]
#[args(<S>, from: rustc_type_ir::FloatTy, state: S as _s)]
#[derive_group(Serializers)]
#[derive(Copy, Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum FloatTy {
    F16,
    F32,
    F64,
    F128,
}

#[cfg(feature = "rustc")]
impl<'tcx, S> SInto<S, FloatTy> for rustc_ast::ast::FloatTy {
    fn sinto(&self, _: &S) -> FloatTy {
        use rustc_ast::ast::FloatTy as T;
        match self {
            T::F16 => FloatTy::F16,
            T::F32 => FloatTy::F32,
            T::F64 => FloatTy::F64,
            T::F128 => FloatTy::F128,
        }
    }
}

#[cfg(feature = "rustc")]
impl<'tcx, S> SInto<S, IntTy> for rustc_ast::ast::IntTy {
    fn sinto(&self, _: &S) -> IntTy {
        use rustc_ast::ast::IntTy as T;
        match self {
            T::Isize => IntTy::Isize,
            T::I8 => IntTy::I8,
            T::I16 => IntTy::I16,
            T::I32 => IntTy::I32,
            T::I64 => IntTy::I64,
            T::I128 => IntTy::I128,
        }
    }
}
#[cfg(feature = "rustc")]
impl<'tcx, S> SInto<S, UintTy> for rustc_ast::ast::UintTy {
    fn sinto(&self, _: &S) -> UintTy {
        use rustc_ast::ast::UintTy as T;
        match self {
            T::Usize => UintTy::Usize,
            T::U8 => UintTy::U8,
            T::U16 => UintTy::U16,
            T::U32 => UintTy::U32,
            T::U64 => UintTy::U64,
            T::U128 => UintTy::U128,
        }
    }
}

/// Reflects [`rustc_type_ir::UintTy`]
#[derive(AdtInto)]
#[args(<S>, from: rustc_type_ir::UintTy, state: S as _s)]
#[derive_group(Serializers)]
#[derive(Copy, Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum UintTy {
    Usize,
    U8,
    U16,
    U32,
    U64,
    U128,
}

impl ToString for IntTy {
    fn to_string(&self) -> String {
        use IntTy::*;
        match self {
            Isize => "isize".to_string(),
            I8 => "i8".to_string(),
            I16 => "i16".to_string(),
            I32 => "i32".to_string(),
            I64 => "i64".to_string(),
            I128 => "i128".to_string(),
        }
    }
}

impl ToString for UintTy {
    fn to_string(&self) -> String {
        use UintTy::*;
        match self {
            Usize => "usize".to_string(),
            U8 => "u8".to_string(),
            U16 => "u16".to_string(),
            U32 => "u32".to_string(),
            U64 => "u64".to_string(),
            U128 => "u128".to_string(),
        }
    }
}

/// Reflects [`rustc_middle::ty::TypeAndMut`]
#[derive(AdtInto)]
#[args(<'tcx, S: UnderOwnerState<'tcx>>, from: rustc_middle::ty::TypeAndMut<'tcx>, state: S as gstate)]
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct TypeAndMut {
    pub ty: Box<Ty>,
    pub mutbl: Mutability,
}

#[cfg(feature = "rustc")]
impl<S, U, T: SInto<S, U>> SInto<S, Vec<U>> for rustc_middle::ty::List<T> {
    fn sinto(&self, s: &S) -> Vec<U> {
        self.iter().map(|x| x.sinto(s)).collect()
    }
}

/// Reflects [`rustc_middle::ty::GenericParamDef`]
#[derive(AdtInto)]
#[args(<'tcx, S: UnderOwnerState<'tcx>>, from: rustc_middle::ty::GenericParamDef, state: S as s)]
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema)]
pub struct GenericParamDef {
    pub name: Symbol,
    pub def_id: DefId,
    pub index: u32,
    pub pure_wrt_drop: bool,
    #[value(
        match self.kind {
            ty::GenericParamDefKind::Lifetime => GenericParamDefKind::Lifetime,
            ty::GenericParamDefKind::Type { has_default, synthetic } => GenericParamDefKind::Type { has_default, synthetic },
            ty::GenericParamDefKind::Const { has_default, is_host_effect, .. } => {
                let ty = s.base().tcx.type_of(self.def_id).instantiate_identity().sinto(s);
                GenericParamDefKind::Const { has_default, is_host_effect, ty }
            },
        }
    )]
    pub kind: GenericParamDefKind,
}

/// Reflects [`rustc_middle::ty::GenericParamDefKind`]
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema)]
pub enum GenericParamDefKind {
    Lifetime,
    Type {
        has_default: bool,
        synthetic: bool,
    },
    Const {
        has_default: bool,
        is_host_effect: bool,
        ty: Ty,
    },
}

/// Reflects [`rustc_middle::ty::Generics`]
#[derive(AdtInto)]
#[args(<'tcx, S: UnderOwnerState<'tcx>>, from: rustc_middle::ty::Generics, state: S as state)]
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema)]
pub struct TyGenerics {
    pub parent: Option<DefId>,
    pub parent_count: usize,
    #[from(own_params)]
    pub params: Vec<GenericParamDef>,
    // pub param_def_id_to_index: FxHashMap<DefId, u32>,
    pub has_self: bool,
    pub has_late_bound_regions: Option<Span>,
}

/// This type merges the information from
/// `rustc_type_ir::AliasKind` and `rustc_middle::ty::AliasTy`
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct Alias {
    pub kind: AliasKind,
    pub args: Vec<GenericArg>,
    pub def_id: DefId,
}

/// Reflects [`rustc_middle::ty::AliasKind`]
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum AliasKind {
    /// The projection of a trait type: `<Ty as Trait<...>>::Type<...>`
    Projection {
        /// The `impl Trait for Ty` in `Ty: Trait<..., Type = U>`.
        impl_expr: ImplExpr,
        /// The `Type` in `Ty: Trait<..., Type = U>`.
        assoc_item: AssocItem,
    },
    /// An associated type in an inherent impl.
    Inherent,
    /// An `impl Trait` opaque type.
    Opaque,
    /// A type alias that references opaque types. Likely to always be normalized away.
    Weak,
}

#[cfg(feature = "rustc")]
impl Alias {
    #[tracing::instrument(level = "trace", skip(s))]
    fn from<'tcx, S: BaseState<'tcx> + HasOwnerId>(
        s: &S,
        alias_kind: &rustc_type_ir::AliasTyKind,
        alias_ty: &rustc_middle::ty::AliasTy<'tcx>,
    ) -> Self {
        use rustc_type_ir::AliasTyKind as RustAliasKind;
        let kind = match alias_kind {
            RustAliasKind::Projection => {
                use rustc_middle::ty::{Binder, EarlyBinder, TypeVisitableExt};
                let tcx = s.base().tcx;
                let trait_ref = alias_ty.trait_ref(tcx);
                // Sometimes (see
                // https://github.com/hacspec/hax/issues/495), we get
                // trait refs with escaping bound vars. Empirically,
                // this seems fine. If we detect such a situation, we
                // emit a warning with a lot of debugging information.
                let poly_trait_ref = if trait_ref.has_escaping_bound_vars() {
                    let trait_ref_and_generics = alias_ty.trait_ref_and_own_args(tcx);
                    let rebased_generics =
                        alias_ty.rebase_inherent_args_onto_impl(alias_ty.args, tcx);
                    let norm_rebased_generics = tcx.try_instantiate_and_normalize_erasing_regions(
                        rebased_generics,
                        s.param_env(),
                        EarlyBinder::bind(trait_ref),
                    );
                    let norm_generics = tcx.try_instantiate_and_normalize_erasing_regions(
                        alias_ty.args,
                        s.param_env(),
                        EarlyBinder::bind(trait_ref),
                    );
                    let early_binder_generics =
                        std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                            EarlyBinder::bind(trait_ref).instantiate(tcx, alias_ty.args)
                        }));
                    let early_binder_rebased_generics =
                        std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                            EarlyBinder::bind(trait_ref).instantiate(tcx, alias_ty.args)
                        }));
                    warning!(
                        s,
                        "Hax frontend found a projected type with escaping bound vars. Please report https://github.com/hacspec/hax/issues/495";
                        {alias_ty, alias_kind, trait_ref, trait_ref_and_generics, rebased_generics,
                         norm_rebased_generics, norm_generics,
                         early_binder_generics, early_binder_rebased_generics}
                    );
                    // we cannot use `Binder::dummy`: it asserts that
                    // there is no any escaping bound vars
                    Binder::bind_with_vars(trait_ref, rustc_middle::ty::List::empty())
                } else {
                    Binder::dummy(trait_ref)
                };
                AliasKind::Projection {
                    assoc_item: tcx.associated_item(alias_ty.def_id).sinto(s),
                    impl_expr: poly_trait_ref.impl_expr(s, s.param_env()),
                }
            }
            RustAliasKind::Inherent => AliasKind::Inherent,
            RustAliasKind::Opaque => AliasKind::Opaque,
            RustAliasKind::Weak => AliasKind::Weak,
        };
        Alias {
            kind,
            args: alias_ty.args.sinto(s),
            def_id: alias_ty.def_id.sinto(s),
        }
    }
}

/// Reflects [`rustc_middle::ty::TyKind`]
#[derive(AdtInto)]
#[args(<'tcx, S: UnderOwnerState<'tcx>>, from: rustc_middle::ty::TyKind<'tcx>, state: S as state)]
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum Ty {
    Bool,
    Char,
    Int(IntTy),
    Uint(UintTy),
    Float(FloatTy),

    #[custom_arm(
        rustc_middle::ty::TyKind::FnPtr(sig) => arrow_of_sig(sig, state),
        rustc_middle::ty::TyKind::FnDef(def, generics) => {
            let tcx = state.base().tcx;
            arrow_of_sig(&tcx.fn_sig(*def).instantiate(tcx, generics), state)
        },
        FROM_TYPE::Closure (_defid, generics) => {
            let sig = generics.as_closure().sig();
            let sig = state.base().tcx.signature_unclosure(sig, rustc_hir::Safety::Safe);
            arrow_of_sig(&sig, state)
        },
    )]
    /// Reflects [`rustc_middle::ty::TyKind::FnPtr`], [`rustc_middle::ty::TyKind::FnDef`] and [`rustc_middle::ty::TyKind::Closure`]
    Arrow(Box<PolyFnSig>),

    #[custom_arm(
        rustc_middle::ty::TyKind::Adt(adt_def, generics) => {
            let def_id = adt_def.did().sinto(state);
            let generic_args: Vec<GenericArg> = generics.sinto(state);
            let trait_refs = if state.base().ty_alias_mode {
                vec![]
            } else {
                solve_item_traits(state, state.param_env(), adt_def.did(), generics, None)
            };
            Ty::Adt { def_id, generic_args, trait_refs }
        },
    )]
    Adt {
        /// Reflects [`rustc_middle::ty::TyKind::Adt`]'s substitutions
        generic_args: Vec<GenericArg>,
        /// Predicates required by the type, e.g. `T: Sized` for `Option<T>` or `B: 'a + ToOwned`
        /// for `Cow<'a, B>`.
        trait_refs: Vec<ImplExpr>,
        def_id: DefId,
    },
    Foreign(DefId),
    Str,
    Array(Box<Ty>, #[map(Box::new(x.sinto(state)))] Box<ConstantExpr>),
    Slice(Box<Ty>),
    RawPtr(Box<Ty>, Mutability),
    Ref(Region, Box<Ty>, Mutability),
    Dynamic(Vec<Binder<ExistentialPredicate>>, Region, DynKind),
    Coroutine(DefId, Vec<GenericArg>),
    Never,
    Tuple(Vec<Ty>),
    #[custom_arm(
        rustc_middle::ty::TyKind::Alias(alias_kind, alias_ty) => {
            Ty::Alias(Alias::from(state, alias_kind, alias_ty))
        },
    )]
    Alias(Alias),
    Param(ParamTy),
    Bound(DebruijnIndex, BoundTy),
    Placeholder(PlaceholderType),
    Infer(InferTy),
    #[custom_arm(rustc_middle::ty::TyKind::Error(..) => Ty::Error,)]
    Error,
    #[todo]
    Todo(String),
}

/// Reflects [`rustc_middle::thir::StmtKind`]
#[derive(AdtInto)]
#[args(<'tcx, S: ExprState<'tcx>>, from: rustc_middle::thir::StmtKind<'tcx>, state: S as gstate)]
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema)]
pub enum StmtKind {
    Expr {
        scope: Scope,
        expr: Expr,
    },
    Let {
        remainder_scope: Scope,
        init_scope: Scope,
        pattern: Pat,
        initializer: Option<Expr>,
        else_block: Option<Block>,
        lint_level: LintLevel,
        #[value(attribute_from_scope(gstate, init_scope).1)]
        /// The attribute on this `let` binding
        attributes: Vec<Attribute>,
    },
}

/// Reflects [`rustc_middle::ty::Variance`]
#[derive(AdtInto)]
#[args(<S>, from: rustc_middle::ty::Variance, state: S as _s)]
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema)]
pub enum Variance {
    Covariant,
    Invariant,
    Contravariant,
    Bivariant,
}

/// Reflects [`rustc_middle::ty::CanonicalUserTypeAnnotation`]
#[derive(AdtInto)]
#[args(<'tcx, S: UnderOwnerState<'tcx>>, from: rustc_middle::ty::CanonicalUserTypeAnnotation<'tcx>, state: S as gstate)]
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema)]
pub struct CanonicalUserTypeAnnotation {
    pub user_ty: CanonicalUserType,
    pub span: Span,
    pub inferred_ty: Ty,
}

/// Reflects [`rustc_middle::thir::Ascription`]
#[derive(AdtInto)]
#[args(<'tcx, S: UnderOwnerState<'tcx> + HasThir<'tcx>>, from: rustc_middle::thir::Ascription<'tcx>, state: S as gstate)]
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema)]
pub struct Ascription {
    pub annotation: CanonicalUserTypeAnnotation,
    pub variance: Variance,
}

/// Reflects [`rustc_hir::RangeEnd`]
#[derive(AdtInto)]
#[args(<S>, from: rustc_hir::RangeEnd, state: S as _s)]
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema)]
pub enum RangeEnd {
    Included,
    Excluded,
}

/// Reflects [`rustc_middle::thir::PatRange`]
#[derive(AdtInto)]
#[args(<'tcx, S: UnderOwnerState<'tcx> + HasThir<'tcx>>, from: rustc_middle::thir::PatRange<'tcx>, state: S as state)]
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema)]
pub struct PatRange {
    pub lo: PatRangeBoundary,
    pub hi: PatRangeBoundary,
    pub end: RangeEnd,
}

/// Reflects [`rustc_middle::thir::PatRangeBoundary`]
#[derive(AdtInto)]
#[args(<'tcx, S: UnderOwnerState<'tcx> + HasThir<'tcx>>, from: rustc_middle::thir::PatRangeBoundary<'tcx>, state: S as state)]
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema)]
pub enum PatRangeBoundary {
    Finite(ConstantExpr),
    NegInfinity,
    PosInfinity,
}

/// Reflects [`rustc_middle::ty::AdtKind`]
#[derive_group(Serializers)]
#[derive(AdtInto, Copy, Clone, Debug, JsonSchema)]
#[args(<'tcx, S: UnderOwnerState<'tcx>>, from: rustc_middle::ty::AdtKind, state: S as _s)]
pub enum AdtKind {
    Struct,
    Union,
    Enum,
}

// This comes from MIR
// TODO: add the generics and the predicates
/// Reflects [`rustc_middle::ty::AdtDef`]
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema)]
pub struct AdtDef {
    pub did: DefId,
    pub adt_kind: AdtKind,
    pub variants: IndexVec<VariantIdx, VariantDef>,
    pub flags: AdtFlags,
    pub repr: ReprOptions,
}

/// Reflects [`rustc_middle::ty::ReprOptions`]
#[derive_group(Serializers)]
#[derive(AdtInto, Clone, Debug, JsonSchema)]
#[args(<'tcx, S: UnderOwnerState<'tcx>>, from: rustc_middle::ty::ReprOptions, state: S as s)]
pub struct ReprOptions {
    pub int: Option<IntegerType>,
    #[value({
        use crate::rustc_middle::ty::util::IntTypeExt;
        self.discr_type().to_ty(s.base().tcx).sinto(s)
    })]
    pub typ: Ty,
    pub align: Option<Align>,
    pub pack: Option<Align>,
    pub flags: ReprFlags,
    pub field_shuffle_seed: u64,
}

#[cfg(feature = "rustc")]
impl<'tcx, S: UnderOwnerState<'tcx>> SInto<S, AdtDef> for rustc_middle::ty::AdtDef<'tcx> {
    fn sinto(&self, s: &S) -> AdtDef {
        let variants = self
            .variants()
            .iter_enumerated()
            .map(|(variant_idx, variant)| {
                let discr = if self.is_enum() {
                    self.discriminant_for_variant(s.base().tcx, variant_idx)
                } else {
                    // Structs and unions have a single variant.
                    assert_eq!(variant_idx.index(), 0);
                    rustc_middle::ty::util::Discr {
                        val: 0,
                        ty: s.base().tcx.types.isize,
                    }
                };
                VariantDef::sfrom(s, variant, discr)
            })
            .collect();
        AdtDef {
            did: self.did().sinto(s),
            adt_kind: self.adt_kind().sinto(s),
            variants,
            flags: self.flags().sinto(s),
            repr: self.repr().sinto(s),
        }
    }
}

/// Describe a variant
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct VariantInformations {
    pub type_namespace: DefId,

    pub typ: DefId,
    pub variant: DefId,
    pub variant_index: VariantIdx,

    /// A record type is a type with only one variant which is a
    /// record variant.
    pub typ_is_record: bool,
    /// A record variant is a variant whose fields are named, a record
    /// variant always has at least one field.
    pub variant_is_record: bool,
    /// A struct is a type with exactly one variant. Note that one
    /// variant is named exactly as the type.
    pub typ_is_struct: bool,
}

/// Reflects [`rustc_middle::thir::PatKind`]
#[derive(AdtInto)]
#[args(<'tcx, S: ExprState<'tcx>>, from: rustc_middle::thir::PatKind<'tcx>, state: S as gstate)]
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema)]
#[append(rustc_middle::thir::PatKind::Leaf {..} => fatal!(gstate, "PatKind::Leaf: should never come up"),)]
pub enum PatKind {
    Wild,
    AscribeUserType {
        ascription: Ascription,
        subpattern: Pat,
    },
    #[custom_arm(
        rustc_middle::thir::PatKind::Binding {name, mode, var, ty, subpattern, is_primary} => {
            let local_ctx = gstate.base().local_ctx;
            local_ctx.borrow_mut().vars.insert(var.clone(), name.to_string());
            PatKind::Binding {
                mode: mode.sinto(gstate),
                var: var.sinto(gstate),
                ty: ty.sinto(gstate),
                subpattern: subpattern.sinto(gstate),
                is_primary: is_primary.sinto(gstate),
            }
        }
    )]
    Binding {
        mode: BindingMode,
        var: LocalIdent, // name VS var? TODO
        ty: Ty,
        subpattern: Option<Pat>,
        is_primary: bool,
    },
    #[custom_arm(
        FROM_TYPE::Variant {adt_def, variant_index, args, subpatterns} => {
            let variants = adt_def.variants();
            let variant: &rustc_middle::ty::VariantDef = &variants[*variant_index];
            TO_TYPE::Variant {
                info: get_variant_information(adt_def, *variant_index, gstate),
                subpatterns: subpatterns
                    .iter()
                    .map(|f| FieldPat {
                        field: variant.fields[f.field].did.sinto(gstate),
                        pattern: f.pattern.sinto(gstate),
                    })
                    .collect(),
                args: args.sinto(gstate),
            }
        }
    )]
    Variant {
        info: VariantInformations,
        args: Vec<GenericArg>,
        subpatterns: Vec<FieldPat>,
    },
    #[disable_mapping]
    Tuple {
        subpatterns: Vec<Pat>,
    },
    Deref {
        subpattern: Pat,
    },
    DerefPattern {
        subpattern: Pat,
    },
    Constant {
        value: ConstantExpr,
    },
    InlineConstant {
        def: DefId,
        subpattern: Pat,
    },
    Range(PatRange),
    Slice {
        prefix: Vec<Pat>,
        slice: Option<Pat>,
        suffix: Vec<Pat>,
    },
    Array {
        prefix: Vec<Pat>,
        slice: Option<Pat>,
        suffix: Vec<Pat>,
    },
    Or {
        pats: Vec<Pat>,
    },
    Never,
    Error(ErrorGuaranteed),
}

/// Reflects [`rustc_middle::thir::Arm`]
#[derive(AdtInto)]
#[args(<'tcx, S: ExprState<'tcx>>, from: rustc_middle::thir::Arm<'tcx>, state: S as gstate)]
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema)]
pub struct Arm {
    pub pattern: Pat,
    pub guard: Option<Expr>,
    pub body: Expr,
    pub lint_level: LintLevel,
    pub scope: Scope,
    pub span: Span,
    #[value(attribute_from_scope(gstate, scope).1)]
    attributes: Vec<Attribute>,
}

/// Reflects [`rustc_hir::Safety`]
#[derive(AdtInto)]
#[args(<S>, from: rustc_hir::Safety, state: S as _s)]
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum Safety {
    Unsafe,
    Safe,
}

/// Reflects [`rustc_middle::ty::adjustment::PointerCoercion`]
#[derive(AdtInto)]
#[args(<S>, from: rustc_middle::ty::adjustment::PointerCoercion, state: S as gstate)]
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema)]
pub enum PointerCoercion {
    ReifyFnPointer,
    UnsafeFnPointer,
    ClosureFnPointer(Safety),
    MutToConstPointer,
    ArrayToPointer,
    Unsize,
}

/// Reflects [`rustc_middle::mir::BorrowKind`]
#[derive(AdtInto)]
#[args(<S>, from: rustc_middle::mir::BorrowKind, state: S as gstate)]
#[derive_group(Serializers)]
#[derive(Copy, Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum BorrowKind {
    Shared,
    Fake(FakeBorrowKind),
    Mut { kind: MutBorrowKind },
}

/// Reflects [`rustc_middle::mir::MutBorrowKind`]
#[derive(AdtInto)]
#[args(<S>, from: rustc_middle::mir::MutBorrowKind, state: S as _s)]
#[derive_group(Serializers)]
#[derive(Copy, Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum MutBorrowKind {
    Default,
    TwoPhaseBorrow,
    ClosureCapture,
}

/// Reflects [`rustc_middle::mir::FakeBorrowKind`]
#[derive(AdtInto)]
#[args(<S>, from: rustc_middle::mir::FakeBorrowKind, state: S as _s)]
#[derive_group(Serializers)]
#[derive(Copy, Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum FakeBorrowKind {
    /// A shared (deep) borrow. Data must be immutable and is aliasable.
    Deep,
    /// The immediately borrowed place must be immutable, but projections from
    /// it don't need to be. This is used to prevent match guards from replacing
    /// the scrutinee. For example, a fake borrow of `a.b` doesn't
    /// conflict with a mutable borrow of `a.b.c`.
    Shallow,
}

/// Reflects [`rustc_ast::ast::StrStyle`]
#[derive(AdtInto)]
#[args(<S>, from: rustc_ast::ast::StrStyle, state: S as gstate)]
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum StrStyle {
    Cooked,
    Raw(u8),
}

/// Reflects [`rustc_ast::ast::LitKind`]
#[derive(AdtInto)]
#[args(<'tcx, S: BaseState<'tcx>>, from: rustc_ast::ast::LitKind, state: S as gstate)]
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum LitKind {
    Str(Symbol, StrStyle),
    ByteStr(Vec<u8>, StrStyle),
    CStr(Vec<u8>, StrStyle),
    Byte(u8),
    Char(char),
    Int(
        #[serde(with = "serialize_int::unsigned")]
        #[schemars(with = "String")]
        u128,
        LitIntType,
    ),
    Float(Symbol, LitFloatType),
    Bool(bool),
    Err(ErrorGuaranteed),
}

#[cfg(feature = "rustc")]
impl<S> SInto<S, u128> for rustc_data_structures::packed::Pu128 {
    fn sinto(&self, _s: &S) -> u128 {
        self.0
    }
}

// FIXME: typo: invo**C**ation
#[allow(rustdoc::private_intra_doc_links)]
/// Describe a macro invocation, using
/// [`macro_invocation_of_raw_mac_invocation`]
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema)]
pub struct MacroInvokation {
    pub macro_ident: DefId,
    pub argument: String,
    pub span: Span,
}

/// Reflects [`rustc_hir::ImplicitSelfKind`]
#[derive(AdtInto)]
#[args(<S>, from: rustc_hir::ImplicitSelfKind, state: S as _s)]
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema)]
pub enum ImplicitSelfKind {
    Imm,
    Mut,
    RefImm,
    RefMut,
    None,
}

/// Reflects [`rustc_ast::token::CommentKind`]
#[derive(AdtInto)]
#[args(<S>, from: rustc_ast::token::CommentKind, state: S as _s)]
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum CommentKind {
    Line,
    Block,
}

/// Reflects [`rustc_ast::ast::AttrArgs`]
#[derive(AdtInto)]
#[args(<'tcx, S: BaseState<'tcx>>, from: rustc_ast::ast::AttrArgs, state: S as tcx)]
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum AttrArgs {
    Empty,
    Delimited(DelimArgs),

    Eq(Span, AttrArgsEq),
    // #[todo]
    // Todo(String),
}

/// Reflects [`rustc_ast::ast::AttrArgsEq`]
#[derive(AdtInto)]
#[args(<'tcx, S: BaseState<'tcx>>, from: rustc_ast::ast::AttrArgsEq, state: S as tcx)]
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum AttrArgsEq {
    Hir(MetaItemLit),
    #[todo]
    Ast(String),
    // Ast(P<Expr>),
}

/// Reflects [`rustc_ast::ast::MetaItemLit`]
#[derive(AdtInto)]
#[args(<'tcx, S: BaseState<'tcx>>, from: rustc_ast::ast::MetaItemLit, state: S as tcx)]
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct MetaItemLit {
    pub symbol: Symbol,
    pub suffix: Option<Symbol>,
    pub kind: LitKind,
    pub span: Span,
}

/// Reflects [`rustc_ast::ast::AttrItem`]
#[derive(AdtInto)]
#[args(<'tcx, S: BaseState<'tcx>>, from: rustc_ast::ast::AttrItem, state: S as tcx)]
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct AttrItem {
    #[map(rustc_ast_pretty::pprust::path_to_string(x))]
    pub path: String,
    pub args: AttrArgs,
    pub tokens: Option<TokenStream>,
}

#[cfg(feature = "rustc")]
impl<S> SInto<S, String> for rustc_ast::tokenstream::LazyAttrTokenStream {
    fn sinto(&self, st: &S) -> String {
        rustc_ast::tokenstream::TokenStream::new(self.to_attr_token_stream().to_token_trees())
            .sinto(st)
    }
}

/// Reflects [`rustc_ast::ast::NormalAttr`]
#[derive(AdtInto)]
#[args(<'tcx, S: BaseState<'tcx>>, from: rustc_ast::ast::NormalAttr, state: S as tcx)]
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct NormalAttr {
    pub item: AttrItem,
    pub tokens: Option<TokenStream>,
}

/// Reflects [`rustc_ast::AttrKind`]
#[derive(AdtInto)]
#[args(<'tcx, S: BaseState<'tcx>>, from: rustc_ast::AttrKind, state: S as tcx)]
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum AttrKind {
    Normal(NormalAttr),
    DocComment(CommentKind, Symbol),
}

/// Reflects [`rustc_middle::thir::Param`]
#[derive(AdtInto)]
#[args(<'tcx, S: ExprState<'tcx>>, from: rustc_middle::thir::Param<'tcx>, state: S as s)]
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema)]
pub struct Param {
    pub pat: Option<Pat>,
    pub ty: Ty,
    pub ty_span: Option<Span>,
    pub self_kind: Option<ImplicitSelfKind>,
    pub hir_id: Option<HirId>,
    #[value(hir_id.map(|id| {
        s.base().tcx.hir().attrs(id).sinto(s)
    }).unwrap_or(vec![]))]
    /// attributes on this parameter
    pub attributes: Vec<Attribute>,
}

/// Reflects [`rustc_middle::thir::ExprKind`]
#[derive(AdtInto)]
#[args(<'tcx, S: ExprState<'tcx>>, from: rustc_middle::thir::ExprKind<'tcx>, state: S as gstate)]
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema)]
#[append(
    rustc_middle::thir::ExprKind::Scope {..} => {
        fatal!(gstate, "Scope should have been eliminated at this point");
    },
    rustc_middle::thir::ExprKind::Field {..} => {
        fatal!(gstate, "Field should have been eliminated at this point");
    },
    rustc_middle::thir::ExprKind::NonHirLiteral {..} => {
        fatal!(gstate, "NonHirLiteral should have been eliminated at this point");
    },
)]
pub enum ExprKind {
    Box {
        value: Expr,
    },
    #[disable_mapping]
    MacroInvokation(MacroInvokation),
    /// Resugared macros calls. This is deprecated: see
    /// <https://github.com/hacspec/hax/issues/145>.
    If {
        if_then_scope: Scope,
        cond: Expr,
        then: Expr,
        else_opt: Option<Expr>,
    },
    #[map({
        let e = gstate.thir().exprs[*fun].unroll_scope(gstate);
        let (generic_args, r#trait, bounds_impls);
        // A function is any expression whose type is something callable
        let fun = match ty.kind() {
            rustc_middle::ty::TyKind::FnDef(def_id, generics) => {
                let (hir_id, attributes) = e.hir_id_and_attributes(gstate);
                let hir_id = hir_id.map(|hir_id| hir_id.index());
                let contents = Box::new(ExprKind::GlobalName {
                    id: def_id.sinto(gstate)
                });
                let mut translated_generics = generics.sinto(gstate);
                let tcx = gstate.base().tcx;
                r#trait = (|| {
                    let assoc_item = tcx.opt_associated_item(*def_id)?;
                    let assoc_trait = tcx.trait_of_item(assoc_item.def_id)?;
                    let trait_ref = ty::TraitRef::new(tcx, assoc_trait, generics.iter());
                    let impl_expr = {
                        // TODO: we should not wrap into a dummy binder
                        let poly_trait_ref = ty::Binder::dummy(trait_ref);
                        poly_trait_ref.impl_expr(gstate, gstate.param_env())
                    };
                    let assoc_generics = tcx.generics_of(assoc_item.def_id);
                    let assoc_generics = translated_generics.drain(0..assoc_generics.parent_count);
                    Some((impl_expr, assoc_generics.collect()))
                })();
                generic_args = translated_generics;
                bounds_impls = solve_item_traits(gstate, gstate.param_env(), *def_id, generics, None);
                Expr {
                    contents,
                    span: e.span.sinto(gstate),
                    ty: e.ty.sinto(gstate),
                    hir_id,
                    attributes,
                }
            },
            rustc_middle::ty::TyKind::FnPtr(..) => {
                generic_args = vec![]; // A function pointer has no generics
                bounds_impls = vec![]; // A function pointer has no bounds
                r#trait = None; // A function pointer is not a method
                e.sinto(gstate)
            },
            ty_kind => supposely_unreachable_fatal!(
                gstate[e.span],
                "CallNotTyFnDef";
                {e, ty_kind}
            )
        };
        TO_TYPE::Call {
            ty: ty.sinto(gstate),
            args: args.sinto(gstate),
            generic_args,
            from_hir_call: from_hir_call.sinto(gstate),
            fn_span: fn_span.sinto(gstate),
            bounds_impls,
            r#trait,
            fun,
        }
    })]
    /// A call to a function or a method.
    ///
    /// Example: `f(0i8)`, where `f` has signature `fn f<T: Clone>(t: T) -> ()`.
    Call {
        /// The type of the function, substitution applied.
        ///
        /// Example: for the call `f(0i8)`, this is `i8 -> ()`.
        ty: Ty,
        /// The function itself. This can be something else than a
        /// name, e.g. a closure.
        ///
        /// Example: for the call `f(0i8)`, this is `f`.
        fun: Expr, // TODO: can [ty] and [fun.ty] be different?
        /// The arguments given to the function.
        ///
        /// Example: for the call `f(0i8)`, this is `[0i8]`.
        args: Vec<Expr>,
        from_hir_call: bool,
        fn_span: Span,
        /// The generic arguments given to the function.
        ///
        /// Example: for the call `f(0i8)`, this is the type `i8`.
        #[not_in_source]
        generic_args: Vec<GenericArg>,
        /// The implementations for the bounds of the function.
        ///
        /// Example: for the call `f(0i8)`, this is two implementation
        /// expressions, one for the explicit bound `i8: Clone` and
        /// one for the implicit `i8: Sized`.
        #[not_in_source]
        bounds_impls: Vec<ImplExpr>,
        /// `trait` is `None` if this is a function call or a method
        /// to an inherent trait. If this is a method call from a
        /// trait `Trait`, then it contains the concrete
        /// implementation of `Trait` it is called on, and the generic
        /// arguments that comes from the trait declaration.
        ///
        /// Example: `f(0i8)` is a function call, hence the field
        /// `impl` is `None`.
        ///
        /// Example:
        /// ```ignore
        /// trait MyTrait<TraitType, const TraitConst: usize> {
        ///   fn meth<MethType>(...) {...}
        /// }
        /// fn example_call<TraitType, SelfType: MyTrait<TraitType, 12>>(x: SelfType) {
        ///   x.meth::<String>(...)
        /// }
        /// ```
        /// Here, in the call `x.meth::<String>(...)`, `r#trait` will
        /// be `Some((..., [SelfType, TraitType, 12]))`, and `generic_args`
        /// will be `[String]`.
        #[not_in_source]
        r#trait: Option<(ImplExpr, Vec<GenericArg>)>,
    },
    Deref {
        arg: Expr,
    },
    Binary {
        op: BinOp,
        lhs: Expr,
        rhs: Expr,
    },
    LogicalOp {
        op: LogicalOp,
        lhs: Expr,
        rhs: Expr,
    },
    Unary {
        op: UnOp,
        arg: Expr,
    },
    Cast {
        source: Expr,
    },
    Use {
        source: Expr,
    }, // Use a lexpr to get a vexpr.
    NeverToAny {
        source: Expr,
    },
    PointerCoercion {
        cast: PointerCoercion,
        source: Expr,
    },
    Loop {
        body: Expr,
    },
    Match {
        scrutinee: Expr,
        arms: Vec<Arm>,
    },
    Let {
        expr: Expr,
        pat: Pat,
    },
    Block {
        #[serde(flatten)]
        block: Block,
    },
    Assign {
        lhs: Expr,
        rhs: Expr,
    },
    AssignOp {
        op: BinOp,
        lhs: Expr,
        rhs: Expr,
    },
    #[disable_mapping]
    Field {
        field: DefId,
        lhs: Expr,
    },

    #[disable_mapping]
    TupleField {
        field: usize,
        lhs: Expr,
    },
    Index {
        lhs: Expr,
        index: Expr,
    },
    VarRef {
        id: LocalIdent,
    },
    #[disable_mapping]
    ConstRef {
        id: ParamConst,
    },
    #[disable_mapping]
    GlobalName {
        id: GlobalIdent,
    },
    UpvarRef {
        closure_def_id: DefId,
        var_hir_id: LocalIdent,
    },
    Borrow {
        borrow_kind: BorrowKind,
        arg: Expr,
    },
    AddressOf {
        mutability: Mutability,
        arg: Expr,
    },
    Break {
        label: Scope,
        value: Option<Expr>,
    },
    Continue {
        label: Scope,
    },
    Return {
        value: Option<Expr>,
    },
    ConstBlock {
        did: DefId,
        args: Vec<GenericArg>,
    },
    Repeat {
        value: Expr,
        count: ConstantExpr,
    },
    Array {
        fields: Vec<Expr>,
    },
    Tuple {
        fields: Vec<Expr>,
    },
    Adt(AdtExpr),
    PlaceTypeAscription {
        source: Expr,
        user_ty: Option<CanonicalUserType>,
    },
    ValueTypeAscription {
        source: Expr,
        user_ty: Option<CanonicalUserType>,
    },
    #[custom_arm(FROM_TYPE::Closure(e) => {
        let (thir, expr_entrypoint) = get_thir(e.closure_id, gstate);
        let s = &State {
            thir: thir.clone(),
            owner_id: gstate.owner_id(),
            base: gstate.base(),
            mir: (),
        };
        TO_TYPE::Closure {
            params: thir.params.raw.sinto(s),
            body: expr_entrypoint.sinto(s),
            upvars: e.upvars.sinto(gstate),
            movability: e.movability.sinto(gstate)
        }
    },
    )]
    Closure {
        params: Vec<Param>,
        body: Expr,
        upvars: Vec<Expr>,
        movability: Option<Movability>,
    },
    Literal {
        lit: Spanned<LitKind>,
        neg: bool, // TODO
    },
    //zero space type
    // This is basically used for functions! e.g. `<T>::from`
    ZstLiteral {
        user_ty: Option<CanonicalUserType>,
    },
    NamedConst {
        def_id: GlobalIdent,
        args: Vec<GenericArg>,
        user_ty: Option<CanonicalUserType>,
        #[not_in_source]
        #[value({
            let tcx = gstate.base().tcx;
            tcx.opt_associated_item(*def_id).as_ref().and_then(|assoc| {
                poly_trait_ref(gstate, assoc, args)
            }).map(|poly_trait_ref| poly_trait_ref.impl_expr(gstate, gstate.param_env()))
        })]
        r#impl: Option<ImplExpr>,
    },
    ConstParam {
        param: ParamConst,
        def_id: GlobalIdent,
    },
    StaticRef {
        alloc_id: u64,
        ty: Ty,
        def_id: GlobalIdent,
    },
    Yield {
        value: Expr,
    },
    #[todo]
    Todo(String),
}

#[cfg(feature = "rustc")]
pub trait ExprKindExt<'tcx> {
    fn hir_id_and_attributes<S: ExprState<'tcx>>(
        &self,
        s: &S,
    ) -> (Option<rustc_hir::HirId>, Vec<Attribute>);
    fn unroll_scope<S: IsState<'tcx> + HasThir<'tcx>>(
        &self,
        s: &S,
    ) -> rustc_middle::thir::Expr<'tcx>;
}

#[cfg(feature = "rustc")]
impl<'tcx> ExprKindExt<'tcx> for rustc_middle::thir::Expr<'tcx> {
    fn hir_id_and_attributes<S: ExprState<'tcx>>(
        &self,
        s: &S,
    ) -> (Option<rustc_hir::HirId>, Vec<Attribute>) {
        match &self.kind {
            rustc_middle::thir::ExprKind::Scope {
                region_scope: scope,
                ..
            } => attribute_from_scope(s, scope),
            _ => (None, vec![]),
        }
    }
    fn unroll_scope<S: IsState<'tcx> + HasThir<'tcx>>(
        &self,
        s: &S,
    ) -> rustc_middle::thir::Expr<'tcx> {
        // TODO: when we see a loop, we should lookup its label! label is actually a scope id
        // we remove scopes here, whence the TODO
        match self.kind {
            rustc_middle::thir::ExprKind::Scope { value, .. } => {
                s.thir().exprs[value].unroll_scope(s)
            }
            _ => self.clone(),
        }
    }
}

/// Reflects [`rustc_middle::ty::FnSig`]
#[derive_group(Serializers)]
#[derive(AdtInto, Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
#[args(<'tcx, S: UnderOwnerState<'tcx>>, from: rustc_middle::ty::FnSig<'tcx>, state: S as s)]
pub struct TyFnSig {
    #[value(self.inputs().sinto(s))]
    pub inputs: Vec<Ty>,
    #[value(self.output().sinto(s))]
    pub output: Ty,
    pub c_variadic: bool,
    pub safety: Safety,
    pub abi: Abi,
}

/// Reflects [`rustc_middle::ty::PolyFnSig`]
pub type PolyFnSig = Binder<TyFnSig>;

/// Function definition
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema)]
pub struct FnDef<Body: IsBody> {
    pub header: FnHeader,
    pub params: Vec<Param>,
    pub ret: Ty,
    pub body: Body,
    pub sig_span: Span,
}

/// Reflects [`rustc_hir::FnDecl`]
#[derive_group(Serializers)]
#[derive(AdtInto, Clone, Debug, JsonSchema)]
#[args(<'tcx, S: UnderOwnerState<'tcx> >, from: rustc_hir::FnDecl<'tcx>, state: S as tcx)]
pub struct FnDecl {
    pub inputs: Vec<Ty>,
    pub output: FnRetTy,
    pub c_variadic: bool,
    pub implicit_self: ImplicitSelfKind,
    pub lifetime_elision_allowed: bool,
}

/// Reflects [`rustc_hir::FnSig`]
#[derive_group(Serializers)]
#[derive(AdtInto, Clone, Debug, JsonSchema)]
#[args(<'tcx, S: UnderOwnerState<'tcx> >, from: rustc_hir::FnSig<'tcx>, state: S as tcx)]
pub struct FnSig {
    pub header: FnHeader,
    pub decl: FnDecl,
    pub span: Span,
}

/// Reflects [`rustc_hir::FnHeader`]
#[derive_group(Serializers)]
#[derive(AdtInto, Clone, Debug, JsonSchema)]
#[args(<'tcx, S: UnderOwnerState<'tcx>>, from: rustc_hir::FnHeader, state: S as tcx)]
pub struct FnHeader {
    pub safety: Safety,
    pub constness: Constness,
    pub asyncness: IsAsync,
    pub abi: Abi,
}

pub type ThirBody = Expr;

#[cfg(feature = "rustc")]
impl<'x: 'tcx, 'tcx, S: UnderOwnerState<'tcx>> SInto<S, Ty> for rustc_hir::Ty<'x> {
    fn sinto(self: &rustc_hir::Ty<'x>, s: &S) -> Ty {
        // **Important:**
        // We need a local id here, and we get it from the owner id, which must
        // be local. It is safe to do so, because if we have access to a HIR ty,
        // it necessarily means we are exploring a local item (we don't have
        // access to the HIR of external objects, only their MIR).
        let ctx =
            rustc_hir_analysis::collect::ItemCtxt::new(s.base().tcx, s.owner_id().expect_local());
        ctx.lower_ty(self).sinto(s)
    }
}

/// Reflects [`rustc_hir::UseKind`]
#[derive(AdtInto)]
#[args(<S>, from: rustc_hir::UseKind, state: S as _s)]
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema)]
pub enum UseKind {
    Single,
    Glob,
    ListStem,
}

/// Reflects [`rustc_hir::IsAuto`]
#[derive(AdtInto)]
#[args(<S>, from: rustc_hir::IsAuto, state: S as _s)]
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema)]
pub enum IsAuto {
    Yes,
    No,
}

/// Reflects [`rustc_hir::Defaultness`]
#[derive(AdtInto)]
#[args(<S>, from: rustc_hir::Defaultness, state: S as tcx)]
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema)]
pub enum Defaultness {
    Default { has_value: bool },
    Final,
}

/// Reflects [`rustc_hir::ImplPolarity`]
#[derive(AdtInto)]
#[args(<'tcx, S: UnderOwnerState<'tcx>>, from: rustc_hir::ImplPolarity, state: S as tcx)]
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema)]
pub enum ImplPolarity {
    Positive,
    Negative(Span),
}

/// Reflects [`rustc_hir::Constness`]
#[derive(AdtInto)]
#[args(<S>, from: rustc_hir::Constness, state: S as _s)]
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema)]
pub enum Constness {
    Const,
    NotConst,
}

/// Reflects [`rustc_hir::Generics`]
#[derive(AdtInto)]
#[args(<'tcx, S: UnderOwnerState<'tcx> >, from: rustc_hir::Generics<'tcx>, state: S as tcx)]
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema)]
pub struct Generics<Body: IsBody> {
    pub params: Vec<GenericParam<Body>>,
    pub predicates: Vec<WherePredicate<Body>>,
    #[value(region_bounds_at_current_owner(tcx))]
    pub bounds: GenericBounds,
    pub has_where_clause_predicates: bool,
    pub where_clause_span: Span,
    pub span: Span,
}

/// Reflects [`rustc_hir::WherePredicate`]
#[derive(AdtInto)]
#[args(<'tcx, S: UnderOwnerState<'tcx> >, from: rustc_hir::WherePredicate<'tcx>, state: S as tcx)]
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema)]
pub enum WherePredicate<Body: IsBody> {
    BoundPredicate(WhereBoundPredicate<Body>),
    RegionPredicate(WhereRegionPredicate),
    EqPredicate(WhereEqPredicate),
}

#[cfg(feature = "rustc")]
impl<'tcx, S: UnderOwnerState<'tcx>, Body: IsBody> SInto<S, ImplItem<Body>>
    for rustc_hir::ImplItemRef
{
    fn sinto(&self, s: &S) -> ImplItem<Body> {
        let tcx: rustc_middle::ty::TyCtxt = s.base().tcx;
        let impl_item = tcx.hir().impl_item(self.id.clone());
        let s = with_owner_id(s.base(), (), (), impl_item.owner_id.to_def_id());
        impl_item.sinto(&s)
    }
}

/// Reflects [`rustc_hir::ParamName`]
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema)]
pub enum ParamName {
    Plain(LocalIdent),
    Fresh,
    Error,
}

/// Reflects [`rustc_hir::LifetimeParamKind`]
#[derive(AdtInto)]
#[args(<S>, from: rustc_hir::LifetimeParamKind, state: S as _s)]
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema)]
pub enum LifetimeParamKind {
    Explicit,
    Elided(MissingLifetimeKind),
    Error,
}

/// Reflects [`rustc_hir::AnonConst`]
#[derive_group(Serializers)]
#[derive(AdtInto, Clone, Debug, JsonSchema)]
#[args(<'tcx, S: UnderOwnerState<'tcx>>, from: rustc_hir::AnonConst, state: S as s)]
pub struct AnonConst<Body: IsBody> {
    pub hir_id: HirId,
    pub def_id: GlobalIdent,
    #[map({
        body_from_id::<Body, _>(*x, &with_owner_id(s.base(), (), (), hir_id.owner.to_def_id()))
    })]
    pub body: Body,
}

/// Reflects [`rustc_hir::ConstArg`]
#[derive_group(Serializers)]
#[derive(AdtInto, Clone, Debug, JsonSchema)]
#[args(<'tcx, S: UnderOwnerState<'tcx>>, from: rustc_hir::ConstArg<'tcx>, state: S as s)]
pub struct ConstArg<Body: IsBody> {
    pub hir_id: HirId,
    pub kind: ConstArgKind<Body>,
    pub is_desugared_from_effects: bool,
}

/// Reflects [`rustc_hir::ConstArgKind`]
#[derive_group(Serializers)]
#[derive(AdtInto, Clone, Debug, JsonSchema)]
#[args(<'tcx, S: UnderOwnerState<'tcx>>, from: rustc_hir::ConstArgKind<'tcx>, state: S as s)]
pub enum ConstArgKind<Body: IsBody> {
    Path(QPath),
    Anon(AnonConst<Body>),
}

/// Reflects [`rustc_hir::GenericParamKind`]
#[derive_group(Serializers)]
#[derive(AdtInto, Clone, Debug, JsonSchema)]
#[args(<'tcx, S: UnderOwnerState<'tcx> >, from: rustc_hir::GenericParamKind<'tcx>, state: S as tcx)]
pub enum GenericParamKind<Body: IsBody> {
    Lifetime {
        kind: LifetimeParamKind,
    },
    Type {
        #[map(x.map(|ty| ty.sinto(tcx)))]
        default: Option<Ty>,
        synthetic: bool,
    },
    Const {
        ty: Ty,
        default: Option<ConstArg<Body>>,
    },
}

/// Reflects [`rustc_hir::GenericParam`]
#[derive_group(Serializers)]
#[derive(AdtInto, Clone, Debug, JsonSchema)]
#[args(<'tcx, S: UnderOwnerState<'tcx> >, from: rustc_hir::GenericParam<'tcx>, state: S as s)]
pub struct GenericParam<Body: IsBody> {
    pub hir_id: HirId,
    pub def_id: GlobalIdent,
    #[map(match x {
        rustc_hir::ParamName::Plain(loc_ident) =>
            ParamName::Plain(LocalIdent {
                name: loc_ident.as_str().to_string(),
                id: self.hir_id.sinto(s)
            }),
        rustc_hir::ParamName::Fresh =>
            ParamName::Fresh,
        rustc_hir::ParamName::Error =>
            ParamName::Error,
    })]
    pub name: ParamName,
    pub span: Span,
    pub pure_wrt_drop: bool,
    pub kind: GenericParamKind<Body>,
    pub colon_span: Option<Span>,
    #[value(s.base().tcx.hir().attrs(hir_id.clone()).sinto(s))]
    attributes: Vec<Attribute>,
}

/// Reflects [`rustc_hir::ImplItem`]
#[derive_group(Serializers)]
#[derive(AdtInto, Clone, Debug, JsonSchema)]
#[args(<'tcx, S: UnderOwnerState<'tcx> >, from: rustc_hir::ImplItem<'tcx>, state: S as s)]
pub struct ImplItem<Body: IsBody> {
    pub ident: Ident,
    pub owner_id: DefId,
    pub generics: Generics<Body>,
    pub kind: ImplItemKind<Body>,
    pub defaultness: Defaultness,
    pub span: Span,
    pub vis_span: Span,
    #[value(ItemAttributes::from_owner_id(s, *owner_id))]
    /// the attributes on this impl item
    pub attributes: ItemAttributes,
}

/// Reflects [`rustc_hir::ImplItemKind`], inlining the body of the items.
#[derive(AdtInto)]
#[args(<'tcx, S: UnderOwnerState<'tcx> >, from: rustc_hir::ImplItemKind<'tcx>, state: S as s)]
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema)]
pub enum ImplItemKind<Body: IsBody> {
    Const(Ty, Body),
    #[custom_arm(rustc_hir::ImplItemKind::Fn(sig, body) => {
                ImplItemKind::Fn(make_fn_def::<Body, _>(sig, body, s))
        },)]
    Fn(FnDef<Body>),
    #[custom_arm(rustc_hir::ImplItemKind::Type(t) => {
        let parent_bounds = {
            let (tcx, owner_id) = (s.base().tcx, s.owner_id());
            let assoc_item = tcx.opt_associated_item(owner_id).unwrap();
            let impl_did = assoc_item.impl_container(tcx).unwrap();
            tcx.explicit_item_bounds(assoc_item.trait_item_def_id.unwrap())
                .skip_binder()
                .iter()
                .copied()
                .filter_map(|(clause, span)| super_clause_to_clause_and_impl_expr(s, impl_did, clause, span))
                .collect::<Vec<_>>()
        };
        ImplItemKind::Type {
            ty: t.sinto(s),
            parent_bounds
        }
        },)]
    /// An associated type with its parent bounds inlined.
    Type {
        ty: Ty,
        parent_bounds: Vec<(Clause, ImplExpr, Span)>,
    },
}

/// Reflects [`rustc_hir::AssocItemKind`]
#[derive(AdtInto)]
#[args(<'tcx, S: UnderOwnerState<'tcx>>, from: rustc_hir::AssocItemKind, state: S as tcx)]
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema)]
pub enum AssocItemKind {
    Const,
    Fn { has_self: bool },
    Type,
}

#[cfg(feature = "rustc")]
impl<
        'tcx,
        S,
        D: Clone,
        T: SInto<S, D> + rustc_middle::ty::TypeFoldable<rustc_middle::ty::TyCtxt<'tcx>>,
    > SInto<S, D> for rustc_middle::ty::EarlyBinder<'tcx, T>
{
    fn sinto(&self, s: &S) -> D {
        self.clone().instantiate_identity().sinto(s)
    }
}

/// Reflects [`rustc_hir::Impl`].
#[derive(AdtInto)]
#[args(<'tcx, S: UnderOwnerState<'tcx> >, from: rustc_hir::Impl<'tcx>, state: S as s)]
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema)]
pub struct Impl<Body: IsBody> {
    pub safety: Safety,
    pub polarity: ImplPolarity,
    pub defaultness: Defaultness,
    pub defaultness_span: Option<Span>,
    pub generics: Generics<Body>,
    #[map({
        s.base().tcx.impl_trait_ref(s.owner_id()).sinto(s)
    })]
    pub of_trait: Option<TraitRef>,
    pub self_ty: Ty,
    pub items: Vec<ImplItem<Body>>,
    #[value({
        let (tcx, owner_id) = (s.base().tcx, s.owner_id());
        let trait_did = tcx.trait_id_of_impl(owner_id);
        if let Some(trait_did) = trait_did {
            tcx.explicit_super_predicates_of(trait_did)
                .predicates
                .iter()
                .copied()
                .filter_map(|(clause, span)| super_clause_to_clause_and_impl_expr(s, owner_id, clause, span))
                .collect::<Vec<_>>()
        } else {
            vec![]
        }
    })]
    /// The clauses and impl expressions corresponding to the impl's
    /// trait (if not inherent) super bounds (if any).
    pub parent_bounds: Vec<(Clause, ImplExpr, Span)>,
}

/// Reflects [`rustc_hir::IsAsync`]
#[derive(AdtInto)]
#[args(<'tcx, S: UnderOwnerState<'tcx>>, from: rustc_hir::IsAsync, state: S as _s)]
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema)]
pub enum IsAsync {
    Async(Span),
    NotAsync,
}

/// Reflects [`rustc_hir::FnRetTy`]
#[derive(AdtInto)]
#[args(<'tcx, S: UnderOwnerState<'tcx> >, from: rustc_hir::FnRetTy<'tcx>, state: S as tcx)]
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema)]
pub enum FnRetTy {
    DefaultReturn(Span),
    Return(Ty),
}

/// Reflects [`rustc_hir::VariantData`]
#[derive_group(Serializers)]
#[derive(AdtInto, Clone, Debug, JsonSchema)]
#[args(<'tcx, S: UnderOwnerState<'tcx> >, from: rustc_hir::VariantData<'tcx>, state: S as tcx)]
pub enum VariantData {
    Struct {
        fields: Vec<HirFieldDef>,
        recovered: bool,
    },
    Tuple(Vec<HirFieldDef>, HirId, GlobalIdent),
    Unit(HirId, GlobalIdent),
}

#[cfg(feature = "rustc")]
impl<S> SInto<S, bool> for rustc_ast::ast::Recovered {
    fn sinto(&self, _s: &S) -> bool {
        match self {
            Self::Yes(_) => true,
            Self::No => false,
        }
    }
}

/// Reflects [`rustc_hir::FieldDef`]
#[derive(AdtInto)]
#[args(<'tcx, S: UnderOwnerState<'tcx> >, from: rustc_hir::FieldDef<'tcx>, state: S as s)]
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema)]
pub struct HirFieldDef {
    pub span: Span,
    pub vis_span: Span,
    pub ident: Ident,
    pub hir_id: HirId,
    pub def_id: GlobalIdent,
    pub ty: Ty,
    #[value(s.base().tcx.hir().attrs(hir_id.clone()).sinto(s))]
    attributes: Vec<Attribute>,
}

/// Reflects [`rustc_hir::Variant`]
#[derive(AdtInto)]
#[args(<'tcx, S: UnderOwnerState<'tcx> >, from: rustc_hir::Variant<'tcx>, state: S as s)]
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema)]
pub struct Variant<Body: IsBody> {
    pub ident: Ident,
    pub hir_id: HirId,
    pub def_id: GlobalIdent,
    #[map(x.sinto(&with_owner_id(s.base(), (), (), self.def_id.to_def_id())))]
    pub data: VariantData,
    pub disr_expr: Option<AnonConst<Body>>,
    #[value({
        let tcx = s.base().tcx;
        let variant = tcx
            .adt_def(s.owner_id())
            .variants()
            .into_iter()
            .find(|v| v.def_id == self.def_id.into()).unwrap();
        variant.discr.sinto(s)
    })]
    pub discr: DiscriminantDefinition,
    pub span: Span,
    #[value(s.base().tcx.hir().attrs(hir_id.clone()).sinto(s))]
    pub attributes: Vec<Attribute>,
}

/// Reflects [`rustc_hir::UsePath`]
#[derive(AdtInto)]
#[args(<'tcx, S: UnderOwnerState<'tcx>>, from: rustc_hir::UsePath<'tcx>, state: S as s)]
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema)]
pub struct UsePath {
    pub span: Span,
    #[map(x.iter().map(|res| res.sinto(s)).collect())]
    pub res: Vec<Res>,
    pub segments: Vec<PathSegment>,
    #[value(self.segments.iter().last().map_or(None, |segment| {
            match s.base().tcx.hir_node_by_def_id(segment.hir_id.owner.def_id) {
                rustc_hir::Node::Item(rustc_hir::Item {
                    ident,
                    kind: rustc_hir::ItemKind::Use(_, _),
                    ..
                }) if ident.name.to_ident_string() != "" => Some(ident.name.to_ident_string()),
                _ => None,
            }
        }))]
    pub rename: Option<String>,
}

/// Reflects [`rustc_hir::def::Res`]
#[derive(AdtInto)]
#[args(<'tcx, S: UnderOwnerState<'tcx>>, from: rustc_hir::def::Res, state: S as s)]
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema)]
pub enum Res {
    Def(DefKind, DefId),
    PrimTy(PrimTy),
    SelfTyParam {
        trait_: DefId,
    },
    SelfTyAlias {
        alias_to: DefId,
        forbid_generic: bool,
        is_trait_impl: bool,
    },
    SelfCtor(DefId),
    Local(HirId),
    ToolMod,
    NonMacroAttr(NonMacroAttrKind),
    Err,
}

/// Reflects [`rustc_hir::PrimTy`]
#[derive(AdtInto)]
#[args(<S>, from: rustc_hir::PrimTy, state: S as s)]
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema)]
pub enum PrimTy {
    Int(IntTy),
    Uint(UintTy),
    Float(FloatTy),
    Str,
    Bool,
    Char,
}

/// Reflects [`rustc_hir::def::NonMacroAttrKind`]
#[derive(AdtInto)]
#[args(<S>, from: rustc_hir::def::NonMacroAttrKind, state: S as s)]
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema)]
pub enum NonMacroAttrKind {
    Builtin(Symbol),
    Tool,
    DeriveHelper,
    DeriveHelperCompat,
}

/// Reflects [`rustc_hir::PathSegment`]
#[derive(AdtInto)]
#[args(<'tcx, S: UnderOwnerState<'tcx>>, from: rustc_hir::PathSegment<'tcx>, state: S as s)]
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema)]
pub struct PathSegment {
    pub ident: Ident,
    pub hir_id: HirId,
    pub res: Res,
    #[map(args.map(|args| args.sinto(s)))]
    pub args: Option<HirGenericArgs>,
    pub infer_args: bool,
}

/// Reflects [`rustc_hir::ItemKind`]
#[derive(AdtInto)]
#[args(<'tcx, S: UnderOwnerState<'tcx> >, from: rustc_hir::ItemKind<'tcx>, state: S as s)]
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema)]
pub enum ItemKind<Body: IsBody> {
    #[disable_mapping]
    MacroInvokation(MacroInvokation),
    ExternCrate(Option<Symbol>),
    Use(UsePath, UseKind),
    Static(Ty, Mutability, Body),
    Const(Ty, Generics<Body>, Body),
    #[custom_arm(
            rustc_hir::ItemKind::Fn(sig, generics, body) => {
                ItemKind::Fn(generics.sinto(s), make_fn_def::<Body, _>(sig, body, s))
            }
        )]
    Fn(Generics<Body>, FnDef<Body>),
    Macro(MacroDef, MacroKind),
    Mod(Vec<Item<Body>>),
    ForeignMod {
        abi: Abi,
        items: Vec<ForeignItem<Body>>,
    },
    GlobalAsm(InlineAsm),
    TyAlias(
        #[map({
            let s = &State {
                thir: s.clone(),
                owner_id: s.owner_id(),
                base: Base {ty_alias_mode: true, ..s.base()},
                mir: (),
            };
            x.sinto(s)
        })]
        Ty,
        Generics<Body>,
    ),
    OpaqueTy(OpaqueTy<Body>),
    Enum(
        EnumDef<Body>,
        Generics<Body>,
        #[value({
            let tcx = s.base().tcx;
            tcx.repr_options_of_def(s.owner_id().expect_local()).sinto(s)
        })]
        ReprOptions,
    ),
    Struct(VariantData, Generics<Body>),
    Union(VariantData, Generics<Body>),
    Trait(
        IsAuto,
        Safety,
        Generics<Body>,
        GenericBounds,
        Vec<TraitItem<Body>>,
    ),
    TraitAlias(Generics<Body>, GenericBounds),
    Impl(Impl<Body>),
}

pub type EnumDef<Body> = Vec<Variant<Body>>;

/// Reflects [`rustc_hir::TraitItemKind`]
#[derive(AdtInto)]
#[args(<'tcx, S: UnderOwnerState<'tcx> >, from: rustc_hir::TraitItemKind<'tcx>, state: S as tcx)]
#[derive(Clone, Debug, JsonSchema)]
#[derive_group(Serializers)]
pub enum TraitItemKind<Body: IsBody> {
    Const(Ty, Option<Body>),
    #[custom_arm(
        rustc_hir::TraitItemKind::Fn(sig, rustc_hir::TraitFn::Required(id)) => {
            TraitItemKind::RequiredFn(sig.sinto(tcx), id.sinto(tcx))
        }
    )]
    /// Reflects a required [`rustc_hir::TraitItemKind::Fn`]
    RequiredFn(FnSig, Vec<Ident>),
    #[custom_arm(
        rustc_hir::TraitItemKind::Fn(sig, rustc_hir::TraitFn::Provided(body)) => {
            TraitItemKind::ProvidedFn(sig.sinto(tcx), make_fn_def::<Body, _>(sig, body, tcx))
        }
    )]
    /// Reflects a provided [`rustc_hir::TraitItemKind::Fn`]
    ProvidedFn(FnSig, FnDef<Body>),
    #[custom_arm(
        rustc_hir::TraitItemKind::Type(b, ty) => {
            TraitItemKind::Type(b.sinto(tcx), ty.map(|t| t.sinto(tcx)))
        }
    )]
    Type(GenericBounds, Option<Ty>),
}

/// Reflects [`rustc_hir::TraitItem`]
#[derive(AdtInto)]
#[args(<'tcx, S: UnderOwnerState<'tcx> >, from: rustc_hir::TraitItem<'tcx>, state: S as s)]
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema)]
pub struct TraitItem<Body: IsBody> {
    pub ident: Ident,
    pub owner_id: DefId,
    pub generics: Generics<Body>,
    pub kind: TraitItemKind<Body>,
    pub span: Span,
    pub defaultness: Defaultness,
    #[value(ItemAttributes::from_owner_id(s, *owner_id))]
    /// The attributes on this trait item
    pub attributes: ItemAttributes,
}

#[cfg(feature = "rustc")]
impl<'tcx, S: UnderOwnerState<'tcx>, Body: IsBody> SInto<S, EnumDef<Body>>
    for rustc_hir::EnumDef<'tcx>
{
    fn sinto(&self, s: &S) -> EnumDef<Body> {
        self.variants.iter().map(|v| v.sinto(s)).collect()
    }
}

#[cfg(feature = "rustc")]
impl<'a, S: UnderOwnerState<'a>, Body: IsBody> SInto<S, TraitItem<Body>>
    for rustc_hir::TraitItemRef
{
    fn sinto(&self, s: &S) -> TraitItem<Body> {
        let s = with_owner_id(s.base(), (), (), self.id.owner_id.to_def_id());
        let tcx: rustc_middle::ty::TyCtxt = s.base().tcx;
        tcx.hir().trait_item(self.clone().id).sinto(&s)
    }
}

#[cfg(feature = "rustc")]
impl<'a, 'tcx, S: UnderOwnerState<'tcx>, Body: IsBody> SInto<S, Vec<Item<Body>>>
    for rustc_hir::Mod<'a>
{
    fn sinto(&self, s: &S) -> Vec<Item<Body>> {
        inline_macro_invocations(self.item_ids.iter().copied(), s)
        // .iter()
        // .map(|item_id| item_id.sinto(s))
        // .collect()
    }
}

/// Reflects [`rustc_hir::ForeignItemKind`]
#[derive(AdtInto)]
#[args(<'tcx, S: UnderOwnerState<'tcx> >, from: rustc_hir::ForeignItemKind<'tcx>, state: S as tcx)]
#[derive(Clone, Debug, JsonSchema)]
#[derive_group(Serializers)]
pub enum ForeignItemKind<Body: IsBody> {
    Fn(FnDecl, Vec<Ident>, Generics<Body>, Safety),
    Static(Ty, Mutability, Safety),
    Type,
}

/// Reflects [`rustc_hir::ForeignItem`]
#[derive(AdtInto)]
#[args(<'tcx, S: UnderOwnerState<'tcx> >, from: rustc_hir::ForeignItem<'tcx>, state: S as tcx)]
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema)]
pub struct ForeignItem<Body: IsBody> {
    pub ident: Ident,
    pub kind: ForeignItemKind<Body>,
    pub owner_id: DefId,
    pub span: Span,
    pub vis_span: Span,
}

#[cfg(feature = "rustc")]
impl<'a, S: UnderOwnerState<'a>, Body: IsBody> SInto<S, ForeignItem<Body>>
    for rustc_hir::ForeignItemRef
{
    fn sinto(&self, s: &S) -> ForeignItem<Body> {
        let tcx: rustc_middle::ty::TyCtxt = s.base().tcx;
        tcx.hir().foreign_item(self.clone().id).sinto(s)
    }
}

/// Reflects [`rustc_hir::OpaqueTy`]
#[derive(AdtInto)]
#[args(<'tcx, S: UnderOwnerState<'tcx> >, from: rustc_hir::OpaqueTy<'tcx>, state: S as tcx)]
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema)]
pub struct OpaqueTy<Body: IsBody> {
    pub generics: Generics<Body>,
    pub bounds: GenericBounds,
    pub origin: OpaqueTyOrigin,
    pub in_trait: bool,
}

/// Reflects [`rustc_hir::LifetimeName`]
#[derive(AdtInto)]
#[args(<'tcx, S: UnderOwnerState<'tcx>>, from: rustc_hir::LifetimeName, state: S as tcx)]
#[derive(Clone, Debug, JsonSchema)]
#[derive_group(Serializers)]
pub enum LifetimeName {
    Param(GlobalIdent),
    ImplicitObjectLifetimeDefault,
    Error,
    Infer,
    Static,
}

/// Reflects [`rustc_hir::Lifetime`]
#[derive(AdtInto)]
#[args(<'tcx, S: UnderOwnerState<'tcx>>, from: rustc_hir::Lifetime, state: S as tcx)]
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema)]
pub struct Lifetime {
    pub hir_id: HirId,
    pub ident: Ident,
    pub res: LifetimeName,
}

/// Reflects [`rustc_middle::ty::TraitRef`]
#[derive_group(Serializers)]
#[derive(AdtInto)]
#[args(<'tcx, S: UnderOwnerState<'tcx>>, from: rustc_middle::ty::TraitRef<'tcx>, state: S as tcx)]
#[derive(Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct TraitRef {
    pub def_id: DefId,
    #[from(args)]
    /// reflects the `args` field
    pub generic_args: Vec<GenericArg>,
}

/// Reflects [`rustc_middle::ty::TraitPredicate`]
#[derive(AdtInto)]
#[args(<'tcx, S: UnderOwnerState<'tcx>>, from: rustc_middle::ty::TraitPredicate<'tcx>, state: S as tcx)]
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct TraitPredicate {
    pub trait_ref: TraitRef,
    #[map(x.clone() == rustc_middle::ty::PredicatePolarity::Positive)]
    #[from(polarity)]
    pub is_positive: bool,
}

/// Reflects [`rustc_middle::ty::OutlivesPredicate`] as a named struct
/// instead of a tuple struct. This is because the script converting
/// JSONSchema types to OCaml doesn't support tuple structs, and this
/// is the only tuple struct in the whole AST.
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct OutlivesPredicate<T> {
    pub lhs: T,
    pub rhs: Region,
}

#[cfg(feature = "rustc")]
impl<'tcx, S: UnderOwnerState<'tcx>, T, U> SInto<S, OutlivesPredicate<U>>
    for rustc_middle::ty::OutlivesPredicate<'tcx, T>
where
    T: SInto<S, U>,
{
    fn sinto(&self, s: &S) -> OutlivesPredicate<U> where {
        OutlivesPredicate {
            lhs: self.0.sinto(s),
            rhs: self.1.sinto(s),
        }
    }
}

/// Reflects [`rustc_middle::ty::RegionOutlivesPredicate`]
pub type RegionOutlivesPredicate = OutlivesPredicate<Region>;
/// Reflects [`rustc_middle::ty::TypeOutlivesPredicate`]
pub type TypeOutlivesPredicate = OutlivesPredicate<Ty>;

/// Reflects [`rustc_middle::ty::Term`]
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum Term {
    Ty(Ty),
    Const(ConstantExpr),
}

#[cfg(feature = "rustc")]
impl<'tcx, S: UnderOwnerState<'tcx>> SInto<S, Term> for rustc_middle::ty::Term<'tcx> {
    fn sinto(&self, s: &S) -> Term {
        use rustc_middle::ty::TermKind;
        match self.unpack() {
            TermKind::Ty(ty) => Term::Ty(ty.sinto(s)),
            TermKind::Const(c) => Term::Const(c.sinto(s)),
        }
    }
}

/// Expresses a constraints over an associated type.
///
/// For instance:
/// ```text
/// fn f<T : Foo<S = String>>(...)
///              ^^^^^^^^^^
/// ```
/// (provided the trait `Foo` has an associated type `S`).
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct ProjectionPredicate {
    /// The `impl Trait for Ty` in `Ty: Trait<..., Type = U>`.
    pub impl_expr: ImplExpr,
    /// The `Type` in `Ty: Trait<..., Type = U>`.
    pub assoc_item: AssocItem,
    /// The type `U` in `Ty: Trait<..., Type = U>`.
    pub ty: Ty,
}

#[cfg(feature = "rustc")]
impl<'tcx, S: BaseState<'tcx> + HasOwnerId> SInto<S, ProjectionPredicate>
    for rustc_middle::ty::ProjectionPredicate<'tcx>
{
    fn sinto(&self, s: &S) -> ProjectionPredicate {
        let tcx = s.base().tcx;
        let AliasKind::Projection {
            impl_expr,
            assoc_item,
        } = Alias::from(
            s,
            &rustc_middle::ty::AliasTyKind::Projection,
            &self.projection_term.expect_ty(tcx),
        )
        .kind
        else {
            unreachable!()
        };
        let Term::Ty(ty) = self.term.sinto(s) else {
            unreachable!()
        };
        ProjectionPredicate {
            impl_expr,
            assoc_item,
            ty,
        }
    }
}

/// Reflects [`rustc_middle::ty::ClauseKind`]
#[derive(AdtInto)]
#[args(<'tcx, S: UnderOwnerState<'tcx>>, from: rustc_middle::ty::ClauseKind<'tcx>, state: S as tcx)]
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum ClauseKind {
    Trait(TraitPredicate),
    RegionOutlives(RegionOutlivesPredicate),
    TypeOutlives(TypeOutlivesPredicate),
    Projection(ProjectionPredicate),
    ConstArgHasType(ConstantExpr, Ty),
    WellFormed(GenericArg),
    ConstEvaluatable(ConstantExpr),
}

/// Reflects [`rustc_middle::ty::Clause`] and adds a hash-consed predicate identifier.
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct Clause {
    pub kind: Binder<ClauseKind>,
    pub id: PredicateId,
}

#[cfg(feature = "rustc")]
impl<'tcx, S: UnderOwnerState<'tcx>> SInto<S, Clause> for rustc_middle::ty::Clause<'tcx> {
    fn sinto(&self, s: &S) -> Clause {
        Clause {
            kind: self.kind().sinto(s),
            id: self.predicate_id(s),
        }
    }
}

/// Reflects [`rustc_middle::ty::Predicate`] and adds a hash-consed predicate identifier.
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct Predicate {
    pub kind: Binder<PredicateKind>,
    pub id: PredicateId,
}

#[cfg(feature = "rustc")]
impl<'tcx, S: UnderOwnerState<'tcx>> SInto<S, Predicate> for rustc_middle::ty::Predicate<'tcx> {
    fn sinto(&self, s: &S) -> Predicate {
        Predicate {
            kind: self.kind().sinto(s),
            id: self.predicate_id(s),
        }
    }
}

/// Reflects [`rustc_middle::ty::BoundVariableKind`]
#[derive(AdtInto)]
#[args(<'tcx, S: UnderOwnerState<'tcx>>, from: rustc_middle::ty::BoundVariableKind, state: S as tcx)]
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum BoundVariableKind {
    Ty(BoundTyKind),
    Region(BoundRegionKind),
    Const,
}

/// Reflects [`rustc_middle::ty::Binder`]
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct Binder<T> {
    pub value: T,
    pub bound_vars: Vec<BoundVariableKind>,
}

/// Reflects [`rustc_middle::ty::GenericPredicates`]
#[derive(AdtInto)]
#[args(<'tcx, S: UnderOwnerState<'tcx>>, from: rustc_middle::ty::GenericPredicates<'tcx>, state: S as s)]
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct GenericPredicates {
    pub parent: Option<DefId>,
    // FIXME: Switch from `Predicate` to `Clause` (will require correct handling of binders).
    #[value(self.predicates.iter().map(|(clause, span)| (clause.as_predicate().sinto(s), span.sinto(s))).collect())]
    pub predicates: Vec<(Predicate, Span)>,
}

#[cfg(feature = "rustc")]
impl<'tcx, S: UnderOwnerState<'tcx>, T1, T2> SInto<S, Binder<T2>>
    for rustc_middle::ty::Binder<'tcx, T1>
where
    T1: SInto<S, T2> + Clone + rustc_middle::ty::TypeFoldable<rustc_middle::ty::TyCtxt<'tcx>>,
{
    fn sinto(&self, s: &S) -> Binder<T2> {
        let bound_vars = self.bound_vars().sinto(s);
        let value = self.as_ref().skip_binder().sinto(s);
        Binder { value, bound_vars }
    }
}

/// Reflects [`rustc_middle::ty::SubtypePredicate`]
#[derive(AdtInto)]
#[args(<'tcx, S: UnderOwnerState<'tcx>>, from: rustc_middle::ty::SubtypePredicate<'tcx>, state: S as tcx)]
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct SubtypePredicate {
    pub a_is_expected: bool,
    pub a: Ty,
    pub b: Ty,
}

/// Reflects [`rustc_middle::ty::CoercePredicate`]
#[derive(AdtInto)]
#[args(<'tcx, S: UnderOwnerState<'tcx>>, from: rustc_middle::ty::CoercePredicate<'tcx>, state: S as tcx)]
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct CoercePredicate {
    pub a: Ty,
    pub b: Ty,
}

/// Reflects [`rustc_middle::ty::AliasRelationDirection`]
#[derive(AdtInto)]
#[args(<'tcx, S: UnderOwnerState<'tcx>>, from: rustc_middle::ty::AliasRelationDirection, state: S as _tcx)]
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum AliasRelationDirection {
    Equate,
    Subtype,
}

/// Reflects [`rustc_middle::ty::ClosureArgs`]
#[derive(AdtInto)]
#[args(<'tcx, S: UnderOwnerState<'tcx> >, from: ty::ClosureArgs<ty::TyCtxt<'tcx>>, state: S as s)]
#[derive(Clone, Debug, JsonSchema)]
#[derive_group(Serializers)]
pub struct ClosureArgs {
    #[value(self.kind().sinto(s))]
    pub kind: ClosureKind,
    #[value(self.parent_args().sinto(s))]
    pub parent_args: Vec<GenericArg>,
    #[value(self.sig().sinto(s))]
    pub sig: PolyFnSig,
    #[value(self.upvar_tys().sinto(s))]
    pub upvar_tys: Vec<Ty>,
}

/// Reflects [`rustc_middle::ty::ClosureKind`]
#[derive(AdtInto)]
#[args(<'tcx, S: UnderOwnerState<'tcx>>, from: rustc_middle::ty::ClosureKind, state: S as _tcx)]
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum ClosureKind {
    Fn,
    FnMut,
    FnOnce,
}

/// Reflects [`rustc_middle::ty::PredicateKind`]
#[derive(AdtInto)]
#[args(<'tcx, S: UnderOwnerState<'tcx>>, from: rustc_middle::ty::PredicateKind<'tcx>, state: S as tcx)]
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum PredicateKind {
    Clause(ClauseKind),
    ObjectSafe(DefId),
    Subtype(SubtypePredicate),
    Coerce(CoercePredicate),
    ConstEquate(ConstantExpr, ConstantExpr),
    Ambiguous,
    AliasRelate(Term, Term, AliasRelationDirection),
    NormalizesTo(NormalizesTo),
}

/// Reflects [`rustc_middle::ty::ImplSubject`]
#[derive(AdtInto)]
#[args(<'tcx, S: UnderOwnerState<'tcx>>, from: rustc_middle::ty::ImplSubject<'tcx>, state: S as s)]
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum ImplSubject {
    Trait(
        // Also record the polarity.
        #[map({
            let polarity = s.base().tcx.impl_polarity(s.owner_id());
            TraitPredicate {
                trait_ref: x.sinto(s),
                is_positive: matches!(polarity, rustc_middle::ty::ImplPolarity::Positive),
            }
        })]
        TraitPredicate,
    ),
    Inherent(Ty),
}

/// Reflects [`rustc_hir::GenericBounds`]
type GenericBounds = Vec<Clause>;

/// Compute the bounds for the owner registed in the state `s`
#[cfg(feature = "rustc")]
fn region_bounds_at_current_owner<'tcx, S: UnderOwnerState<'tcx>>(s: &S) -> GenericBounds {
    let tcx = s.base().tcx;

    // According to what kind of node we are looking at, we should
    // either call `predicates_defined_on` or `item_bounds`
    let use_item_bounds = {
        if let Some(oid) = s.owner_id().as_local() {
            let hir_id = tcx.local_def_id_to_hir_id(oid);
            let node = tcx.hir_node(hir_id);
            use rustc_hir as hir;
            matches!(
                node,
                hir::Node::TraitItem(hir::TraitItem {
                    kind: hir::TraitItemKind::Type(..),
                    ..
                }) | hir::Node::Item(hir::Item {
                    kind: hir::ItemKind::OpaqueTy(hir::OpaqueTy { .. }),
                    ..
                })
            )
        } else {
            false
        }
    };

    let clauses: Vec<ty::Clause<'tcx>> = if use_item_bounds {
        tcx.item_bounds(s.owner_id())
            .instantiate_identity()
            .iter()
            .collect()
    } else {
        tcx.predicates_defined_on(s.owner_id())
            .predicates
            .iter()
            .map(|(x, _span)| x)
            .copied()
            .collect()
    };
    clauses.sinto(s)
}

#[cfg(feature = "rustc")]
impl<'tcx, S: UnderOwnerState<'tcx>> SInto<S, GenericBounds> for rustc_hir::GenericBounds<'tcx> {
    fn sinto(&self, s: &S) -> GenericBounds {
        region_bounds_at_current_owner(s)
    }
}

/// Reflects [`rustc_hir::OpaqueTyOrigin`]
#[derive(AdtInto)]
#[args(<'tcx, S: UnderOwnerState<'tcx>>, from: rustc_hir::OpaqueTyOrigin, state: S as tcx)]
#[derive(Clone, Debug, JsonSchema)]
#[derive_group(Serializers)]
pub enum OpaqueTyOrigin {
    FnReturn(GlobalIdent),
    AsyncFn(GlobalIdent),
    TyAlias { in_assoc_ty: bool },
}

/// Reflects [`rustc_ast::ast::MacroDef`]
#[derive(AdtInto)]
#[args(<'tcx, S: BaseState<'tcx>>, from: rustc_ast::ast::MacroDef, state: S as tcx)]
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema)]
pub struct MacroDef {
    pub body: DelimArgs,
    pub macro_rules: bool,
}

/// Reflects [`rustc_hir::Item`] (and [`rustc_hir::ItemId`])
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema)]
pub struct Item<Body: IsBody> {
    pub def_id: Option<GlobalIdent>,
    pub owner_id: DefId,
    pub span: Span,
    pub vis_span: Span,
    pub kind: ItemKind<Body>,
    pub attributes: ItemAttributes,
    pub expn_backtrace: Vec<ExpnData>,
}

#[cfg(feature = "rustc")]
impl<'tcx, S: BaseState<'tcx>, Body: IsBody> SInto<S, Item<Body>> for rustc_hir::Item<'tcx> {
    fn sinto(&self, s: &S) -> Item<Body> {
        let name: String = self.ident.name.to_ident_string();
        let s = &with_owner_id(s.base(), (), (), self.owner_id.to_def_id());
        let owner_id: DefId = self.owner_id.sinto(s);
        let def_id = Path::from(owner_id.clone())
            .ends_with(&[name])
            .then(|| owner_id.clone());
        Item {
            def_id,
            owner_id,
            span: self.span.sinto(s),
            vis_span: self.span.sinto(s),
            kind: self.kind.sinto(s),
            attributes: ItemAttributes::from_owner_id(s, self.owner_id),
            expn_backtrace: self.span.macro_backtrace().map(|o| o.sinto(s)).collect(),
        }
    }
}

#[cfg(feature = "rustc")]
impl<'tcx, S: BaseState<'tcx>, Body: IsBody> SInto<S, Item<Body>> for rustc_hir::ItemId {
    fn sinto(&self, s: &S) -> Item<Body> {
        let tcx: rustc_middle::ty::TyCtxt = s.base().tcx;
        tcx.hir().item(self.clone()).sinto(s)
    }
}

/// Reflects [`rustc_span::symbol::Ident`]
pub type Ident = (Symbol, Span);

#[cfg(feature = "rustc")]
impl<'tcx, S: UnderOwnerState<'tcx>> SInto<S, Ident> for rustc_span::symbol::Ident {
    fn sinto(&self, s: &S) -> Ident {
        (self.name.sinto(s), self.span.sinto(s))
    }
}

/// Reflects [`rustc_hir::WhereBoundPredicate`]
#[derive(AdtInto)]
#[args(<'tcx, S: UnderOwnerState<'tcx> >, from: rustc_hir::WhereBoundPredicate<'tcx>, state: S as tcx)]
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema)]
pub struct WhereBoundPredicate<Body: IsBody> {
    pub hir_id: HirId,
    pub span: Span,
    pub origin: PredicateOrigin,
    pub bound_generic_params: Vec<GenericParam<Body>>,
    pub bounded_ty: Ty,
    // TODO: What to do with WhereBoundPredicate?
    // pub bounds: GenericBounds,
}

/// Reflects [`rustc_hir::PredicateOrigin`]
#[derive(AdtInto)]
#[args(<S>, from: rustc_hir::PredicateOrigin, state: S as _s)]
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema)]
pub enum PredicateOrigin {
    WhereClause,
    GenericParam,
    ImplTrait,
}

/// Reflects [`rustc_middle::ty::AssocItem`]
#[derive(AdtInto)]
#[args(<'tcx, S: BaseState<'tcx>>, from: rustc_middle::ty::AssocItem, state: S as s)]
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct AssocItem {
    pub def_id: DefId,
    pub name: Symbol,
    pub kind: AssocKind,
    #[value(get_container_for_assoc_item(s, self))]
    pub container: AssocItemContainer,
    /// Whether this item has a value (e.g. this is `false` for trait methods without default
    /// implementations).
    #[value(self.defaultness(s.base().tcx).has_value())]
    pub has_value: bool,
    pub fn_has_self_parameter: bool,
    pub opt_rpitit_info: Option<ImplTraitInTraitData>,
}

/// Reflects [`rustc_middle::ty::ImplTraitInTraitData`]
#[derive(AdtInto)]
#[args(<'tcx, S: BaseState<'tcx>>, from: rustc_middle::ty::ImplTraitInTraitData, state: S as _s)]
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum ImplTraitInTraitData {
    Trait {
        fn_def_id: DefId,
        opaque_def_id: DefId,
    },
    Impl {
        fn_def_id: DefId,
    },
}

#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum AssocItemContainer {
    TraitContainer {
        trait_id: DefId,
    },
    TraitImplContainer {
        impl_id: DefId,
        implemented_trait: DefId,
        implemented_trait_item: DefId,
        /// Whether the corresponding trait item had a default (and therefore this one overrides
        /// it).
        overrides_default: bool,
    },
    InherentImplContainer {
        impl_id: DefId,
    },
}

#[cfg(feature = "rustc")]
fn get_container_for_assoc_item<'tcx, S: BaseState<'tcx>>(
    s: &S,
    item: &ty::AssocItem,
) -> AssocItemContainer {
    let container_id = item.container_id(s.base().tcx);
    match item.container {
        ty::AssocItemContainer::TraitContainer => AssocItemContainer::TraitContainer {
            trait_id: container_id.sinto(s),
        },
        ty::AssocItemContainer::ImplContainer => {
            if let Some(implemented_trait_item) = item.trait_item_def_id {
                AssocItemContainer::TraitImplContainer {
                    impl_id: container_id.sinto(s),
                    implemented_trait: s
                        .base()
                        .tcx
                        .trait_of_item(implemented_trait_item)
                        .unwrap()
                        .sinto(s),
                    implemented_trait_item: implemented_trait_item.sinto(s),
                    overrides_default: s.base().tcx.defaultness(implemented_trait_item).has_value(),
                }
            } else {
                AssocItemContainer::InherentImplContainer {
                    impl_id: container_id.sinto(s),
                }
            }
        }
    }
}

/// Reflects [`rustc_middle::ty::AssocKind`]
#[derive(AdtInto)]
#[args(<S>, from: rustc_middle::ty::AssocKind, state: S as _tcx)]
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum AssocKind {
    Const,
    Fn,
    Type,
}
