use crate::prelude::*;

#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum ConstantInt {
    Int(
        #[serde(with = "serialize_int::signed")]
        #[schemars(with = "String")]
        i128,
        IntTy,
    ),
    Uint(
        #[serde(with = "serialize_int::unsigned")]
        #[schemars(with = "String")]
        u128,
        UintTy,
    ),
}

#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum ConstantLiteral {
    Bool(bool),
    Char(char),
    Int(ConstantInt),
    Str(String, StrStyle),
    ByteStr(Vec<u8>, StrStyle),
}

/// The subset of [Expr] that corresponds to constants.
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum ConstantExprKind {
    Literal(ConstantLiteral),
    Adt {
        info: VariantInformations,
        fields: Vec<ConstantFieldExpr>,
    },
    Array {
        fields: Vec<ConstantExpr>,
    },
    Tuple {
        fields: Vec<ConstantExpr>,
    },
    /// A top-level constant or a constant appearing in an impl block.
    ///
    /// Remark: constants *can* have generic parameters.
    /// Example:
    /// ```text
    /// struct V<const N: usize, T> {
    ///   x: [T; N],
    /// }
    ///
    /// impl<const N: usize, T> V<N, T> {
    ///   const LEN: usize = N; // This has generics <N, T>
    /// }
    /// ```
    GlobalName {
        id: GlobalIdent,
        generics: Vec<GenericArg>,
        trait_refs: Vec<ImplExpr>,
    },
    /// A trait constant
    ///
    /// Ex.:
    /// ```text
    /// impl Foo for Bar {
    ///   const C : usize = 32; // <-
    /// }
    /// ```
    TraitConst {
        impl_expr: ImplExpr,
        name: String,
    },
    /// A shared reference to a static variable.
    Borrow(ConstantExpr),
    /// A `*mut` pointer to a static mutable variable.
    MutPtr(ConstantExpr),
    ConstRef {
        id: ParamConst,
    },
    FnPtr {
        def_id: DefId,
        generics: Vec<GenericArg>,
        /// The implementation expressions for every generic bounds
        /// ```text
        /// fn foo<T : Bar>(...)
        ///            ^^^
        /// ```
        generics_impls: Vec<ImplExpr>,
        /// If the function is a method of trait `Foo`, `method_impl`
        /// is an implementation of `Foo`
        method_impl: Option<ImplExpr>,
    },
    Todo(String),
}

#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct ConstantFieldExpr {
    pub field: DefId,
    pub value: ConstantExpr,
}

/// Rustc has different representation for constants: one for MIR
/// ([`rustc_middle::mir::Const`]), one for the type system
/// ([`rustc_middle::ty::ConstKind`]). For simplicity hax maps those
/// two construct to one same `ConstantExpr` type.
pub type ConstantExpr = Decorated<ConstantExprKind>;

#[cfg(feature = "rustc")]
pub use self::rustc::*;
#[cfg(feature = "rustc")]
mod rustc {
    use super::*;
    use rustc_middle::{mir, ty};

    impl From<ConstantFieldExpr> for FieldExpr {
        fn from(c: ConstantFieldExpr) -> FieldExpr {
            FieldExpr {
                value: c.value.into(),
                field: c.field,
            }
        }
    }

    impl ConstantLiteral {
        /// Rustc always represents string constants as `&[u8]`, but this
        /// is not nice to consume. This associated function interpret
        /// bytes as an unicode string, and as a byte string otherwise.
        fn byte_str(bytes: Vec<u8>, style: StrStyle) -> Self {
            match String::from_utf8(bytes.clone()) {
                Ok(s) => Self::Str(s, style),
                Err(_) => Self::ByteStr(bytes, style),
            }
        }
    }

    impl From<ConstantExpr> for Expr {
        fn from(c: ConstantExpr) -> Expr {
            use ConstantExprKind::*;
            let kind = match *c.contents {
                Literal(lit) => {
                    use ConstantLiteral::*;
                    let mut neg = false;
                    let node = match lit {
                        Bool(b) => LitKind::Bool(b),
                        Char(c) => LitKind::Char(c),
                        Int(i) => {
                            use LitIntType::*;
                            match i {
                                ConstantInt::Uint(v, t) => LitKind::Int(v, Unsigned(t)),
                                ConstantInt::Int(v, t) => {
                                    neg = v.is_negative();
                                    LitKind::Int(v.abs_diff(0), Signed(t))
                                }
                            }
                        }
                        ByteStr(raw, str_style) => LitKind::ByteStr(raw, str_style),
                        Str(raw, str_style) => LitKind::Str(raw, str_style),
                    };
                    let span = c.span.clone();
                    let lit = Spanned { span, node };
                    ExprKind::Literal { lit, neg }
                }
                Adt { info, fields } => ExprKind::Adt(AdtExpr {
                    info,
                    fields: fields.into_iter().map(|field| field.into()).collect(),
                    base: None,
                    user_ty: None,
                }),
                // TODO: propagate the generics and trait refs (see #636)
                GlobalName {
                    id,
                    generics: _,
                    trait_refs: _,
                } => ExprKind::GlobalName { id },
                Borrow(e) => ExprKind::Borrow {
                    borrow_kind: BorrowKind::Shared,
                    arg: e.into(),
                },
                MutPtr(e) => ExprKind::AddressOf {
                    mutability: true,
                    arg: e.into(),
                },
                ConstRef { id } => ExprKind::ConstRef { id },
                Array { fields } => ExprKind::Array {
                    fields: fields.into_iter().map(|field| field.into()).collect(),
                },
                Tuple { fields } => ExprKind::Tuple {
                    fields: fields.into_iter().map(|field| field.into()).collect(),
                },
                kind @ (FnPtr { .. } | TraitConst { .. }) => {
                    // SH: I see the `Closure` kind, but it's not the same as function pointer?
                    ExprKind::Todo(format!("FnPtr or TraitConst. kind={:#?}", kind))
                }
                Todo(msg) => ExprKind::Todo(msg),
            };
            Decorated {
                contents: Box::new(kind),
                ..c
            }
        }
    }

    pub(crate) fn scalar_int_to_constant_literal<'tcx, S: UnderOwnerState<'tcx>>(
        s: &S,
        x: rustc_middle::ty::ScalarInt,
        ty: rustc_middle::ty::Ty,
    ) -> ConstantLiteral {
        match ty.kind() {
            ty::Char => ConstantLiteral::Char(
                char::try_from(x)
                    .s_expect(s, "scalar_int_to_constant_literal: expected a char")
                    .into(),
            ),
            ty::Bool => ConstantLiteral::Bool(
                x.try_to_bool()
                    .s_expect(s, "scalar_int_to_constant_literal: expected a bool"),
            ),
            ty::Int(kind) => {
                let v = x.to_int(x.size());
                ConstantLiteral::Int(ConstantInt::Int(v, kind.sinto(s)))
            }
            ty::Uint(kind) => {
                let v = x.to_uint(x.size());
                ConstantLiteral::Int(ConstantInt::Uint(v, kind.sinto(s)))
            }
            _ => fatal!(
                s,
                "scalar_int_to_constant_literal: the type {:?} is not a literal",
                ty
            ),
        }
    }

    pub(crate) fn scalar_to_constant_expr<'tcx, S: UnderOwnerState<'tcx>>(
        s: &S,
        ty: rustc_middle::ty::Ty<'tcx>,
        scalar: &rustc_middle::mir::interpret::Scalar,
        span: rustc_span::Span,
    ) -> ConstantExpr {
        use rustc_middle::mir::Mutability;
        let cspan = span.sinto(s);
        // The documentation explicitly says not to match on a scalar.
        // We match on the type and use it to convert the value.
        let kind = match ty.kind() {
            ty::Char | ty::Bool | ty::Int(_) | ty::Uint(_) => {
                let scalar_int = scalar.try_to_scalar_int().unwrap_or_else(|_| {
                    fatal!(
                        s[span],
                        "Type is primitive, but the scalar {:#?} is not an [Int]",
                        scalar
                    )
                });
                ConstantExprKind::Literal(scalar_int_to_constant_literal(s, scalar_int, ty))
            }
            ty::Ref(_, inner_ty, Mutability::Not) | ty::RawPtr(inner_ty, Mutability::Mut) => {
                let tcx = s.base().tcx;
                let pointer = scalar.to_pointer(&tcx).unwrap_or_else(|_| {
                    fatal!(
                        s[span],
                        "Type is [Ref] or [RawPtr], but the scalar {:#?} is not a [Pointer]",
                        scalar
                    )
                });
                use rustc_middle::mir::interpret::GlobalAlloc;
                let contents = match tcx.global_alloc(pointer.provenance.s_unwrap(s).alloc_id()) {
                    GlobalAlloc::Static(did) => ConstantExprKind::GlobalName {
                        id: did.sinto(s),
                        generics: Vec::new(),
                        trait_refs: Vec::new(),
                    },
                    GlobalAlloc::Memory(alloc) => {
                        let values = alloc.inner().get_bytes_unchecked(
                            rustc_middle::mir::interpret::AllocRange {
                                start: rustc_abi::Size::ZERO,
                                size: alloc.inner().size(),
                            },
                        );
                        ConstantExprKind::Literal(ConstantLiteral::ByteStr(
                            values.iter().copied().collect(),
                            StrStyle::Cooked,
                        ))
                    }
                    provenance => fatal!(
                        s[span],
                        "Expected provenance to be `GlobalAlloc::Static` or \
                        `GlobalAlloc::Memory`, got {:#?} instead",
                        provenance
                    ),
                };
                let contents = contents.decorate(inner_ty.sinto(s), cspan.clone());
                match ty.kind() {
                    ty::Ref(..) => ConstantExprKind::Borrow(contents),
                    ty::RawPtr(..) => ConstantExprKind::MutPtr(contents),
                    _ => unreachable!(),
                }
            }
            // A [Scalar] might also be any zero-sized [Adt] or [Tuple] (i.e., unit)
            ty::Tuple(ty) if ty.is_empty() => ConstantExprKind::Tuple { fields: vec![] },
            // It seems we can have ADTs when there is only one variant, and this variant doesn't have any fields.
            ty::Adt(def, _) => {
                if let [variant_def] = &def.variants().raw {
                    if variant_def.fields.is_empty() {
                        ConstantExprKind::Adt {
                            info: get_variant_information(def, rustc_target::abi::FIRST_VARIANT, s),
                            fields: vec![],
                        }
                    } else {
                        fatal!(
                            s[span],
                            "Unexpected type `ty` for scalar `scalar`. Case `ty::Adt(def, _)`: \
                            `variant_def.fields` was not empty";
                            {ty, scalar, def, variant_def}
                        )
                    }
                } else {
                    fatal!(
                        s[span],
                        "Unexpected type `ty` for scalar `scalar`. Case `ty::Adt(def, _)`: \
                        `def.variants().raw` was supposed to contain exactly one variant.";
                        {ty, scalar, def, &def.variants().raw}
                    )
                }
            }
            _ => fatal!(
                s[span],
                "Unexpected type `ty` for scalar `scalar`";
                {ty, scalar}
            ),
        };
        kind.decorate(ty.sinto(s), cspan)
    }

    /// Whether a `DefId` is a `AnonConst`. An anonymous constant is
    /// generated by Rustc, hoisting every constat bits from items as
    /// separate top-level items. This AnonConst mechanism is internal to
    /// Rustc; we don't want to reflect that, instead we prefer inlining
    /// those. `is_anon_const` is used to detect such AnonConst so that we
    /// can evaluate and inline them.
    pub(crate) fn is_anon_const<'tcx>(
        did: rustc_span::def_id::DefId,
        tcx: rustc_middle::ty::TyCtxt<'tcx>,
    ) -> bool {
        matches!(
            tcx.def_path(did).data.last().map(|x| x.data),
            Some(rustc_hir::definitions::DefPathData::AnonConst)
        )
    }

    fn trait_const_to_constant_expr_kind<'tcx, S: BaseState<'tcx> + HasOwnerId>(
        s: &S,
        _const_def_id: rustc_hir::def_id::DefId,
        generics: rustc_middle::ty::GenericArgsRef<'tcx>,
        assoc: &rustc_middle::ty::AssocItem,
    ) -> ConstantExprKind {
        assert!(assoc.trait_item_def_id.is_some());
        let name = assoc.name.to_string();

        // Retrieve the trait information
        let impl_expr = get_trait_info(s, generics, assoc);

        ConstantExprKind::TraitConst { impl_expr, name }
    }

    impl ConstantExprKind {
        pub fn decorate(self, ty: Ty, span: Span) -> Decorated<Self> {
            Decorated {
                contents: Box::new(self),
                hir_id: None,
                attributes: vec![],
                ty,
                span,
            }
        }
    }

    pub enum TranslateUnevalRes<T> {
        // TODO: rename
        GlobalName(ConstantExpr),
        EvaluatedConstant(T),
    }

    pub trait ConstantExt<'tcx>: Sized + std::fmt::Debug {
        fn eval_constant<S: UnderOwnerState<'tcx>>(&self, s: &S) -> Option<Self>;

        /// Performs a one-step translation of a constant.
        ///  - When a constant refers to a named top-level constant, we want to use that, thus we translate the constant to a `ConstantExprKind::GlobalName`. This is captured by the variant `TranslateUnevalRes::GlobalName`.
        ///  - When a constant refers to a anonymous top-level constant, we evaluate it. If the evaluation fails, we report an error: we expect every AnonConst to be reducible. Otherwise, we return the variant `TranslateUnevalRes::EvaluatedConstant`.
        fn translate_uneval(
            &self,
            s: &impl UnderOwnerState<'tcx>,
            ucv: rustc_middle::ty::UnevaluatedConst<'tcx>,
            span: rustc_span::Span,
        ) -> TranslateUnevalRes<Self> {
            let tcx = s.base().tcx;
            if is_anon_const(ucv.def, tcx) {
                TranslateUnevalRes::EvaluatedConstant(self.eval_constant(s).unwrap_or_else(|| {
                    // TODO: This is triggered when compiling using `generic_const_exprs`
                    supposely_unreachable_fatal!(s, "TranslateUneval"; {self, ucv});
                }))
            } else {
                let param_env = s.param_env();
                let ty = s.base().tcx.type_of(ucv.def);
                let ty = tcx.instantiate_and_normalize_erasing_regions(ucv.args, param_env, ty);
                let kind = if let Some(assoc) = s.base().tcx.opt_associated_item(ucv.def) {
                    if assoc.trait_item_def_id.is_some() {
                        // This must be a trait declaration constant
                        trait_const_to_constant_expr_kind(s, ucv.def, ucv.args, &assoc)
                    } else {
                        // Constant appearing in an inherent impl block.

                        // Solve the trait obligations
                        let parent_def_id = tcx.parent(ucv.def);
                        let trait_refs =
                            solve_item_traits(s, param_env, parent_def_id, ucv.args, None);

                        // Convert
                        let id = ucv.def.sinto(s);
                        let generics = ucv.args.sinto(s);
                        ConstantExprKind::GlobalName {
                            id,
                            generics,
                            trait_refs,
                        }
                    }
                } else {
                    // Top-level constant.
                    assert!(ucv.args.is_empty(), "top-level constant has generics?");
                    let id = ucv.def.sinto(s);
                    ConstantExprKind::GlobalName {
                        id,
                        generics: vec![],
                        trait_refs: vec![],
                    }
                };
                let cv = kind.decorate(ty.sinto(s), span.sinto(s));
                TranslateUnevalRes::GlobalName(cv)
            }
        }
    }
    impl<'tcx> ConstantExt<'tcx> for ty::Const<'tcx> {
        fn eval_constant<S: UnderOwnerState<'tcx>>(&self, s: &S) -> Option<Self> {
            let (ty, evaluated) = self
                .eval(s.base().tcx, s.param_env(), rustc_span::DUMMY_SP)
                .ok()?;
            let evaluated = ty::Const::new(s.base().tcx, ty::ConstKind::Value(ty, evaluated));
            (&evaluated != self).then_some(evaluated)
        }
    }
    impl<'tcx> ConstantExt<'tcx> for mir::Const<'tcx> {
        fn eval_constant<S: UnderOwnerState<'tcx>>(&self, s: &S) -> Option<Self> {
            let evaluated = self
                .eval(s.base().tcx, s.param_env(), rustc_span::DUMMY_SP)
                .ok()?;
            let evaluated = mir::Const::Val(evaluated, self.ty());
            (&evaluated != self).then_some(evaluated)
        }
    }
    impl<'tcx, S: UnderOwnerState<'tcx>> SInto<S, ConstantExpr> for ty::Const<'tcx> {
        fn sinto(&self, s: &S) -> ConstantExpr {
            use rustc_middle::query::Key;
            let span = self.default_span(s.base().tcx);
            match self.kind() {
                ty::ConstKind::Param(p) => {
                    let ty = p.find_ty_from_env(s.param_env());
                    let kind = ConstantExprKind::ConstRef { id: p.sinto(s) };
                    kind.decorate(ty.sinto(s), span.sinto(s))
                }
                ty::ConstKind::Infer(..) => {
                    fatal!(s[span], "ty::ConstKind::Infer node? {:#?}", self)
                }

                ty::ConstKind::Unevaluated(ucv) => match self.translate_uneval(s, ucv, span) {
                    TranslateUnevalRes::EvaluatedConstant(c) => return c.sinto(s),
                    TranslateUnevalRes::GlobalName(c) => c,
                },
                ty::ConstKind::Value(ty, valtree) => valtree_to_constant_expr(s, valtree, ty, span),
                ty::ConstKind::Error(_) => fatal!(s[span], "ty::ConstKind::Error"),
                ty::ConstKind::Expr(e) => fatal!(s[span], "ty::ConstKind::Expr {:#?}", e),

                ty::ConstKind::Bound(i, bound) => {
                    supposely_unreachable_fatal!(s[span], "ty::ConstKind::Bound"; {i, bound});
                }
                _ => fatal!(s[span], "unexpected case"),
            }
        }
    }

    // #[tracing::instrument(skip(s))]
    pub(crate) fn valtree_to_constant_expr<'tcx, S: UnderOwnerState<'tcx>>(
        s: &S,
        valtree: rustc_middle::ty::ValTree<'tcx>,
        ty: rustc_middle::ty::Ty<'tcx>,
        span: rustc_span::Span,
    ) -> ConstantExpr {
        let kind = match (valtree, ty.kind()) {
        (_, ty::Ref(_, inner_ty, _)) => {
            ConstantExprKind::Borrow(valtree_to_constant_expr(s, valtree, *inner_ty, span))
        }
        (ty::ValTree::Branch(valtrees), ty::Str) => ConstantExprKind::Literal(
            ConstantLiteral::byte_str(valtrees.iter().map(|x| match x {
                ty::ValTree::Leaf(leaf) => leaf.to_u8(),
                _ => fatal!(s[span], "Expected a flat list of leaves while translating a str literal, got a arbitrary valtree.")
            }).collect(), StrStyle::Cooked))
        ,
        (ty::ValTree::Branch(_), ty::Array(..) | ty::Tuple(..) | ty::Adt(..)) => {
            let contents: rustc_middle::ty::DestructuredConst = s
                .base().tcx
                .destructure_const(ty::Const::new_value(s.base().tcx, valtree, ty));
            let fields = contents.fields.iter().copied();
            match ty.kind() {
                ty::Array(_, _) => ConstantExprKind::Array {
                    fields: fields
                        .map(|field| field.sinto(s))
                        .collect(),
                },
                ty::Tuple(_) => ConstantExprKind::Tuple {
                    fields: fields
                        .map(|field| field.sinto(s))
                        .collect(),
                },
                ty::Adt(def, _) => {
                    let variant_idx = contents
                        .variant
                        .s_expect(s, "destructed const of adt without variant idx");
                    let variant_def = &def.variant(variant_idx);

                    ConstantExprKind::Adt{
                        info: get_variant_information(def, variant_idx, s),
                        fields: fields.into_iter()
                            .zip(&variant_def.fields)
                            .map(|(value, field)| ConstantFieldExpr {
                                field: field.did.sinto(s),
                                value: value.sinto(s),
                            })
                        .collect(),
                    }
                }
                _ => unreachable!(),
            }
        }
        (ty::ValTree::Leaf(x), _) => ConstantExprKind::Literal (
            scalar_int_to_constant_literal(s, x, ty)
        ),
        _ => supposely_unreachable_fatal!(
            s[span], "valtree_to_expr";
            {valtree, ty}
        ),
    };
        kind.decorate(ty.sinto(s), span.sinto(s))
    }

    pub(crate) fn const_value_reference_to_constant_expr<'tcx, S: UnderOwnerState<'tcx>>(
        s: &S,
        ty: rustc_middle::ty::Ty<'tcx>,
        val: rustc_middle::mir::ConstValue<'tcx>,
        span: rustc_span::Span,
    ) -> ConstantExpr {
        let tcx = s.base().tcx;

        let dc = tcx
            .try_destructure_mir_constant_for_user_output(val, ty)
            .s_unwrap(s);

        // Iterate over the fields, which should be values
        assert!(dc.variant.is_none());

        // The type should be tuple
        let hax_ty = ty.sinto(s);
        match &hax_ty {
            Ty::Tuple(_) => (),
            _ => {
                fatal!(s[span], "Expected the type to be tuple: {:?}", val)
            }
        };

        // Below: we are mutually recursive with [const_value_to_constant_expr],
        // which takes a [Const] as input, but it should be
        // ok because we call it on a strictly smaller value.
        let fields: Vec<ConstantExpr> = dc
            .fields
            .iter()
            .copied()
            .map(|(val, ty)| const_value_to_constant_expr(s, ty, val, span))
            .collect();
        (ConstantExprKind::Tuple { fields }).decorate(hax_ty, span.sinto(s))
    }

    pub fn const_value_to_constant_expr<'tcx, S: UnderOwnerState<'tcx>>(
        s: &S,
        ty: rustc_middle::ty::Ty<'tcx>,
        val: rustc_middle::mir::ConstValue<'tcx>,
        span: rustc_span::Span,
    ) -> ConstantExpr {
        use rustc_middle::mir::ConstValue;
        match val {
            ConstValue::Scalar(scalar) => scalar_to_constant_expr(s, ty, &scalar, span),
            ConstValue::Indirect { .. } => const_value_reference_to_constant_expr(s, ty, val, span),
            ConstValue::Slice { data, meta } => {
                let end = meta.try_into().unwrap();
                // This is outside of the interpreter, so we are okay to use
                // `inspect_with_uninit_and_ptr_outside_interpreter`. Moreover this is a string/byte
                // literal, so we don't have to care about initialization.
                // This is copied from `ConstantValue::try_get_slice_bytes_for_diagnostics`, available
                // only in a more recent rustc version.
                let slice: &[u8] = data
                    .inner()
                    .inspect_with_uninit_and_ptr_outside_interpreter(0..end);
                ConstantExprKind::Literal(ConstantLiteral::byte_str(
                    slice.to_vec(),
                    StrStyle::Cooked,
                ))
                .decorate(ty.sinto(s), span.sinto(s))
            }
            ConstValue::ZeroSized { .. } => {
                // Should be unit
                let hty = ty.sinto(s);
                let cv = match &hty {
                    Ty::Tuple(tys) if tys.is_empty() => {
                        ConstantExprKind::Tuple { fields: Vec::new() }
                    }
                    Ty::Arrow(_) => match ty.kind() {
                        rustc_middle::ty::TyKind::FnDef(def_id, args) => {
                            let (def_id, generics, generics_impls, method_impl) =
                                get_function_from_def_id_and_generics(s, *def_id, args);

                            ConstantExprKind::FnPtr {
                                def_id,
                                generics,
                                generics_impls,
                                method_impl,
                            }
                        }
                        kind => {
                            fatal!(s[span], "Unexpected:"; {kind})
                        }
                    },
                    _ => {
                        fatal!(
                            s[span],
                            "Expected the type to be tuple or arrow";
                            {val, ty}
                        )
                    }
                };

                cv.decorate(hty, span.sinto(s))
            }
        }
    }
}
