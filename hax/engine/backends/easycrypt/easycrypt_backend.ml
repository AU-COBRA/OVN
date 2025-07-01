(* -------------------------------------------------------------------- *)
open Hax_engine
open Base

(* -------------------------------------------------------------------- *)

include
  Backend.Make
    (struct
      open Features
      include Off
      include On.Loop
      include On.For_index_loop
      include On.Mutable_variable
      include On.Macro
      include On.Construct_base
    end)
    (struct
      let backend = Diagnostics.Backend.EasyCrypt
    end)

module BackendOptions = Backend.UnitBackendOptions
module AST = Ast.Make (InputLanguage)
module ECNamePolicy = Concrete_ident.DefaultNamePolicy
module U = Ast_utils.MakeWithNamePolicy (InputLanguage) (ECNamePolicy)
open AST

module RejectNotEC (FA : Features.T) = struct
  module FB = InputLanguage

  include
    Feature_gate.Make (FA) (FB)
      (struct
        module A = FA
        module B = FB
        include Feature_gate.DefaultSubtype

        let mutable_variable _ _ = Features.On.mutable_variable
        let loop _ _ = Features.On.loop
        let continue = reject
        let mutable_reference = reject
        let mutable_pointer = reject
        let reference = reject
        let slice = reject
        let raw_pointer = reject
        let early_exit = reject
        let question_mark = reject
        let break = reject
        let macro _ _ = Features.On.macro
        let as_pattern = reject
        let lifetime = reject
        let monadic_action = reject
        let monadic_binding = reject
        let arbitrary_lhs = reject
        let state_passing_loop = reject
        let nontrivial_lhs = reject
        let block = reject
        let for_loop = reject
        let while_loop = reject
        let quote = reject
        let dyn = reject
        let match_guard = reject
        let trait_item_default = reject
        let unsafe = reject
        let construct_base _ _ = Features.On.construct_base
        let for_index_loop _ _ = Features.On.for_index_loop

        let metadata =
          Phase_utils.Metadata.make (Reject (NotInBackendLang EasyCrypt))
      end)
end

type nmtree = { subnms : (string, nmtree) Map.Poly.t; items : AST.item list }

module NM = struct
  let empty : nmtree = { subnms = Map.Poly.empty; items = [] }

  let rec push_using_longname (the : nmtree) (nm : string list)
      (item : AST.item) =
    match nm with
    | [] -> { the with items = the.items @ [ item ] }
    | name :: nm ->
        let update (subnm : nmtree option) =
          let subnm = Option.value ~default:empty subnm in
          push_using_longname subnm nm item
        in

        { the with subnms = Map.Poly.update ~f:update the.subnms name }

  let push_using_namespace (the : nmtree) (nm : string * string list)
      (item : AST.item) =
    push_using_longname the (List.rev (fst nm :: snd nm)) item

  let push (the : nmtree) (item : AST.item) =
    push_using_namespace the
      (U.Concrete_ident_view.to_namespace item.ident)
      item
end

let suffix_of_size (size : Ast.size) =
  match size with
  | Ast.S8 -> "8"
  | Ast.S16 -> "16"
  | Ast.S32 -> "32"
  | Ast.S64 -> "64"
  | Ast.S128 -> "128"
  | Ast.SSize -> "P"

let suffix_of_signedness (s : Ast.signedness) =
  match s with Signed -> "S" | Unsigned -> "U"

let intmodule_of_kind (Ast.{ size; signedness } : Ast.int_kind) =
  Stdlib.Format.sprintf "W%s%s"
    (suffix_of_signedness signedness)
    (suffix_of_size size)

let translate' (_bo : BackendOptions.t) (items : AST.item list) :
    Types.file list =
  let items = List.fold_left ~init:NM.empty ~f:NM.push items in

  let rec doit (fmt : Formatter.t) (the : nmtree) =
    the.subnms
    |> Map.Poly.iteri ~f:(fun ~key ~data ->
           Stdlib.Format.fprintf fmt "theory %s.@." key;
           doit fmt data;
           Stdlib.Format.fprintf fmt "end.@.");

    let doitems (fmt : Formatter.t) =
      the.items
      |> List.iter ~f:(fun item ->
             match item.v with
             | Fn { name; generics; body; params }
               when List.is_empty generics.params ->
                 let name = U.Concrete_ident_view.to_definition_name name in

                 doit_fn fmt (name, params, body)
             | Fn _ -> assert false
             | TyAlias _ -> assert false
             | Type _ -> assert false
             | Trait _ -> assert false
             | Impl _ -> assert false
             | HaxError _ -> ()
             | IMacroInvokation _ -> ()
             | Use _ -> ()
             | Alias _ -> ()
             | NotImplementedYet -> ()
             | _ -> .)
    in

    if not (List.is_empty the.items) then
      Stdlib.Format.fprintf fmt "@[<v>module Procs = {@,  @[<v>%t@]@,}@]@,"
        doitems
  and doit_fn (fmt : Formatter.t) (name, params, body) =
    let pp_param (fmt : Formatter.t) (p : param) =
      match p.pat.p with
      | PBinding { var; typ; mode = ByValue; mut = Immutable; subpat = None } ->
          Stdlib.Format.fprintf fmt "%s : %a" var.name doit_type typ
      | _ -> assert false
    in

    Stdlib.Format.fprintf fmt "@[<v>proc %s(%a) = {@,  @[<v>%a@]@,}@]@\n@\n"
      name
      (Stdlib.Format.pp_print_list
         ~pp_sep:(fun fmt () -> Stdlib.Format.fprintf fmt ", ")
         pp_param)
      params doit_stmt body
  and doit_concrete_ident (fmt : Formatter.t) (p : Concrete_ident.t) =
    Stdlib.Format.fprintf fmt "%s" (U.Concrete_ident_view.to_definition_name p)
  and doit_type (fmt : Formatter.t) (typ : ty) =
    match typ with
    | TBool -> assert false
    | TChar -> assert false
    | TInt kind -> Stdlib.Format.fprintf fmt "%s.t" (intmodule_of_kind kind)
    | TFloat _ -> assert false
    | TStr -> assert false
    | TApp { ident = `Concrete ident; args = [] } ->
        doit_concrete_ident fmt ident
    | TApp { ident = `Concrete ident; args } ->
        Stdlib.Format.fprintf fmt "(%a) %a"
          (Stdlib.Format.pp_print_list
             ~pp_sep:(fun fmt () -> Stdlib.Format.fprintf fmt ", ")
             doit_type_arg)
          args doit_concrete_ident ident
    | TApp _ -> assert false
    | TArray _ -> assert false
    | TParam _ -> assert false
    | TArrow (_, _) -> assert false
    | TAssociatedType _ -> assert false
    | TOpaque _ -> assert false
    | _ -> .
  and doit_type_arg (fmt : Formatter.t) (tyarg : generic_value) =
    match tyarg with GType ty -> doit_type fmt ty | _ -> assert false
  and doit_stmt (fmt : Formatter.t) (expr : expr) =
    let foo () =
      Stdlib.Format.eprintf "%a@.@." pp_expr expr;
      assert false
    in

    match expr.e with
    | If { cond; then_; else_ = None } ->
        Stdlib.Format.fprintf fmt "@[<v>if (%a) {@,  @[<v>%a@]@,}@]" doit_expr
          cond doit_stmt then_
    | If _ -> assert false
    | Let
        {
          lhs =
            {
              p =
                PBinding
                  {
                    mut = _;
                    mode = ByValue;
                    var = { name; _ };
                    subpat = None;
                    _;
                  };
              _;
            };
          rhs;
          body;
          monadic = None;
        } ->
        Stdlib.Format.fprintf fmt "%s <- %a;@," name doit_expr rhs;
        Stdlib.Format.fprintf fmt "%a" doit_stmt body
    | Let
        {
          lhs = { p = PWild; typ = TApp { ident = `TupleType 0; args = [] }; _ };
          rhs;
          body;
          monadic = None;
        } ->
        Stdlib.Format.fprintf fmt "%a@," doit_stmt rhs;
        Stdlib.Format.fprintf fmt "%a" doit_stmt body
    | Let _ -> foo ()
    | Assign { lhs; e; _ } ->
        Stdlib.Format.fprintf fmt "%a <- %a;" doit_lhs lhs doit_expr e
    | Match _ -> foo ()
    | Loop
        {
          body;
          kind = ForIndexLoop { start; end_; var = { name; _ }; _ };
          state = None;
          _;
        } ->
        let _ = match start.typ with TInt kind -> kind | _ -> assert false in

        Stdlib.Format.fprintf fmt "%s <- %a;@," name doit_expr start;
        Stdlib.Format.fprintf fmt "@[<v>while (%s < %a) {@,  @[<v>%a%t@]@,}@]"
          name doit_expr end_ doit_stmt body (fun fmt ->
            Stdlib.Format.fprintf fmt "%s <- %s + 1;@," name name)
    | Loop _ -> foo ()
    | MacroInvokation _ -> foo ()
    | GlobalVar (`TupleCons 0) -> ()
    | Ascription _ | Array _ | Closure _ -> assert false
    | App _ | Literal _ | Construct _ | LocalVar _ | GlobalVar _ ->
        Stdlib.Format.fprintf fmt "return %a;" doit_expr expr
    | _ -> .
  and doit_lhs (fmt : Formatter.t) (lhs : lhs) =
    match lhs with
    | LhsFieldAccessor _ -> assert false
    | LhsArrayAccessor
        { e = LhsLocalVar { var = { name; _ }; _ }; index; typ = _; _ } ->
        Stdlib.Format.fprintf fmt "%s.[%a]" name doit_expr index
    | LhsLocalVar { var = { name; _ }; _ } ->
        Stdlib.Format.fprintf fmt "%s" name
    | _ -> .
  and doit_expr (fmt : Formatter.t) (expr : expr) =
    match expr.e with
    | If _ -> assert false
    | App { f = { e = GlobalVar ident; _ }; args = [ a; i ]; _ }
      when Ast.Global_ident.eq_name Core__ops__index__Index__index ident ->
        Stdlib.Format.fprintf fmt "(%a).[%a]" doit_expr a doit_expr i
    | App { f = { e = GlobalVar (`Concrete op); _ }; args = [ e1; e2 ]; _ }
      when Concrete_ident.(
             eq_name Core__ops__bit__BitXor__bitxor op
             || eq_name Core__ops__bit__BitAnd__bitand op
             || eq_name Core__ops__bit__BitOr__bitor op
             || eq_name Core__ops__arith__Add__add op
             || eq_name Core__ops__arith__Mul__mul op
             || eq_name Core__cmp__PartialEq__ne op
             || eq_name Core__cmp__PartialEq__eq op) ->
        Stdlib.Format.fprintf fmt "(%a) %s (%a)" doit_expr e1
          (match U.Concrete_ident_view.to_definition_name op with
          | "bitxor" -> "^"
          | "bitand" -> "&"
          | "bitor" -> "|"
          | "add" -> "+"
          | "mul" -> "*"
          | "eq" -> "="
          | "ne" -> "<>"
          | _ -> assert false)
          doit_expr e2
    | App { f = { e = GlobalVar (`Concrete ident); _ }; args = []; _ } ->
        Stdlib.Format.fprintf fmt "%a" doit_concrete_ident ident
    | App { f = { e = GlobalVar (`Concrete ident); _ }; args; _ } ->
        Stdlib.Format.fprintf fmt "%a %a" doit_concrete_ident ident
          (Stdlib.Format.pp_print_list
             ~pp_sep:(fun fmt () -> Stdlib.Format.fprintf fmt " ")
             (fun fmt e -> Stdlib.Format.fprintf fmt "(%a)" doit_expr e))
          args
    | App _ ->
        Stdlib.Format.eprintf "%a@.@." pp_expr expr;
        assert false
    | Literal (Int { value; kind; _ }) ->
        Stdlib.Format.fprintf fmt "%s.ofint %a" (intmodule_of_kind kind)
          String.pp value
    | Literal _ -> assert false
    | Array _ -> assert false
    | Construct
        {
          constructor = `Concrete ident;
          is_record = false;
          is_struct = false;
          base = None;
          fields = _;
        } ->
        Stdlib.Format.eprintf "%a." doit_concrete_ident ident
    | Construct _ -> assert false
    | Match _ -> assert false
    | Let _ -> assert false
    | LocalVar { name; _ } -> Stdlib.Format.fprintf fmt "%s" name
    | GlobalVar _ -> assert false
    | Ascription _ -> assert false
    | MacroInvokation _ -> assert false
    | Assign _ -> assert false
    | Loop _ -> assert false
    (* | ForLoop _ -> assert false *)
    | Closure _ -> assert false
    | _ -> .
  in

  doit Stdlib.Format.err_formatter items;
  []

let translate _ (bo : BackendOptions.t) (items : AST.item list) :
    Types.file list =
  try translate' bo items
  with Assert_failure (file, line, col) ->
    Diagnostics.failure ~context:(Backend FStar) ~span:(Span.dummy ())
      (AssertionFailure
         {
           details =
             "Assertion failed in " ^ file ^ ":" ^ Int.to_string line ^ ":"
             ^ Int.to_string col;
         })

open Phase_utils

module TransformToInputLanguage =
[%functor_application
Phases.Reject.RawOrMutPointer Features.Rust |> Phases.Reject.Unsafe
|> Phases.And_mut_defsite |> Phases.Reconstruct_asserts
|> Phases.Reconstruct_for_loops |> Phases.Direct_and_mut |> Phases.Drop_blocks
|> Phases.Reject.Continue |> Phases.Drop_references |> RejectNotEC]

let apply_phases (_bo : BackendOptions.t) (items : Ast.Rust.item list) :
    AST.item list =
  TransformToInputLanguage.ditems items
