open! Prelude

module%inlined_contents Make
    (F : Features.T
           with type raw_pointer = Features.Off.raw_pointer
            and type mutable_reference = Features.Off.mutable_reference) =
struct
  open Ast
  module FA = F

  module FB = struct
    include F
    include Features.Off.Mutable_pointer
    include Features.Off.Lifetime
    include Features.Off.Reference
  end

  include
    Phase_utils.MakeBase (F) (FB)
      (struct
        let phase_id = Diagnostics.Phase.DropReferences
      end)

  module UA = Ast_utils.Make (F)

  module Implem : ImplemT.T = struct
    let metadata = metadata

    module S = struct
      include Features.SUBTYPE.Id
    end

    [%%inline_defs dsafety_kind]

    let rec dty (span : span) (t : A.ty) : B.ty =
      match t with
      | [%inline_arms "dty.*" - TApp - TRef] -> auto
      | TApp { ident; args } ->
          TApp { ident; args = List.filter_map ~f:(dgeneric_value span) args }
      | TRef { typ; mut = Immutable; _ } -> dty span typ
      | TRef _ -> .

    and dgeneric_value (span : span) (g : A.generic_value) :
        B.generic_value option =
      match g with
      | GLifetime _ -> None
      | [%inline_arms "dgeneric_value.*" - GLifetime] ->
          map (Option.some : B.generic_value -> _)

    and dtrait_goal (span : span) (r : A.trait_goal) : B.trait_goal =
      {
        trait = r.trait;
        args = List.filter_map ~f:(dgeneric_value span) r.args;
      }

    and ddyn_trait_goal (span : span) (r : A.dyn_trait_goal) : B.dyn_trait_goal
        =
      {
        trait = r.trait;
        non_self_args = List.filter_map ~f:(dgeneric_value span) r.non_self_args;
      }

    and dpat' (span : span) (p : A.pat') : B.pat' =
      match p with
      | [%inline_arms "dpat'.*" - PBinding - PDeref] -> auto
      | PBinding { mut; var : Local_ident.t; typ; subpat; _ } ->
          PBinding
            {
              mut;
              mode = ByValue;
              var;
              typ = dty span typ;
              subpat =
                Option.map ~f:(fun (p, as_pat) -> (dpat p, as_pat)) subpat;
            }
      | PDeref { subpat; _ } -> (dpat subpat).p

    and dexpr' (span : span) (e : A.expr') : B.expr' =
      match (UA.unbox_underef_expr { e; span; typ = UA.never_typ }).e with
      | [%inline_arms
          If + Literal + Array + Block + QuestionMark + "dexpr'.Quote"] ->
          auto
      | Construct { constructor; is_record; is_struct; fields; base } ->
          Construct
            {
              constructor;
              is_record;
              is_struct;
              fields = List.map ~f:(fun (i, e) -> (i, dexpr e)) fields;
              base = Option.map ~f:(dexpr *** S.construct_base span) base;
            }
      | Match { scrutinee; arms } ->
          Match { scrutinee = dexpr scrutinee; arms = List.map ~f:darm arms }
      | Let { monadic; lhs; rhs; body } ->
          Let
            {
              monadic = Option.map ~f:(dsupported_monads span *** Fn.id) monadic;
              lhs = dpat lhs;
              rhs = dexpr rhs;
              body = dexpr body;
            }
      | LocalVar local_ident -> LocalVar local_ident
      | GlobalVar global_ident -> GlobalVar global_ident
      | Ascription { e = e'; typ } ->
          Ascription { e = dexpr e'; typ = dty span typ }
      | MacroInvokation { macro; args; witness } ->
          MacroInvokation { macro; args; witness }
      | Assign { lhs; e; witness } ->
          Assign { lhs = dlhs span lhs; e = dexpr e; witness }
      | [%inline_arms Loop + Continue + Break] ->
          auto (* TODO: inline more arms! *)
      | Return { e; witness } -> Return { e = dexpr e; witness }
      | Borrow { e; _ } -> (dexpr e).e
      | EffectAction { action; argument } ->
          EffectAction { action; argument = dexpr argument }
      | Closure { params; body; captures } ->
          Closure
            {
              params = List.map ~f:dpat params;
              body = dexpr body;
              captures = List.map ~f:dexpr captures;
            }
      | App { f; args; generic_args; trait; bounds_impls } ->
          let f = dexpr f in
          let args = List.map ~f:dexpr args in
          let dgeneric_args = List.filter_map ~f:(dgeneric_value span) in
          let trait = Option.map ~f:(dimpl_expr span *** dgeneric_args) trait in
          let generic_args = dgeneric_args generic_args in
          let bounds_impls = List.map ~f:(dimpl_expr span) bounds_impls in
          App { f; args; generic_args; trait; bounds_impls }
      | _ -> .
      [@@inline_ands bindings_of dexpr - dbinding_mode]

    let dgeneric_param (_span : span)
        ({ ident; kind; attrs; span } : A.generic_param) :
        B.generic_param option =
      let ( let* ) x f = Option.bind ~f x in
      let* kind =
        match kind with
        | GPLifetime _ -> None
        | GPType { default } ->
            Some (B.GPType { default = Option.map ~f:(dty span) default })
        | GPConst { typ } -> Some (B.GPConst { typ = dty span typ })
      in
      Some B.{ ident; kind; attrs; span }

    and dprojection_predicate (span : span) (r : A.projection_predicate) :
        B.projection_predicate =
      {
        impl = dimpl_expr span r.impl;
        assoc_item = r.assoc_item;
        typ = dty span r.typ;
      }

    let dgeneric_constraint (span : span) (p : A.generic_constraint) :
        B.generic_constraint option =
      match p with
      | GCLifetime _ -> None
      | GCType idents -> Some (B.GCType (dimpl_ident span idents))
      | GCProjection projection ->
          Some (B.GCProjection (dprojection_predicate span projection))

    let dgenerics (span : span) (g : A.generics) : B.generics =
      {
        params = List.filter_map ~f:(dgeneric_param span) g.params;
        constraints =
          List.filter_map ~f:(dgeneric_constraint span) g.constraints;
      }

    [%%inline_defs dparam + dvariant + dtrait_item + dimpl_item]

    let rec ditem = [%inline_body ditem]
    and ditem_unwrapped = [%inline_body ditem_unwrapped]

    and ditem' (span : span) (item : A.item') : B.item' =
      match item with
      | [%inline_arms "ditem'.*" - Impl] -> auto
      | Impl
          {
            generics;
            self_ty;
            of_trait = of_trait_id, of_trait_generics;
            items;
            parent_bounds;
            safety;
          } ->
          B.Impl
            {
              generics = dgenerics span generics;
              self_ty = dty span self_ty;
              of_trait =
                ( of_trait_id,
                  List.filter_map ~f:(dgeneric_value span) of_trait_generics );
              items = List.map ~f:dimpl_item items;
              parent_bounds =
                List.map ~f:(dimpl_expr span *** dimpl_ident span) parent_bounds;
              safety = dsafety_kind span safety;
            }

    [%%inline_defs ditems]
  end

  include Implem
end
[@@add "subtype.ml"]
