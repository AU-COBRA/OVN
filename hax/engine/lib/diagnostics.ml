open! Prelude
module T = Types

module Backend = struct
  type t = Coq | SSProve | FStar | EasyCrypt | ProVerif
  [@@deriving show { with_path = false }, eq, yojson, compare, hash, sexp]
end

module Phase = struct
  module Rejection = struct
    type t =
      | NotInBackendLang of Backend.t
      | ArbitraryLhs
      | Continue
      | RawOrMutPointer
      | EarlyExit
      | AsPattern
      | Dyn
      | TraitItemDefault
      | Unsafe
    [@@deriving show { with_path = false }, eq, yojson, compare, hash, sexp]

    let display = function
      | NotInBackendLang backend -> "not_in_" ^ [%show: Backend.t] backend
      | x -> [%show: t] x
  end

  type t =
    | DirectAndMut
    | AndMutDefSite
    | Identity
    | DropReferences
    | DropBlocks
    | DropSizedTrait
    | DropMatchGuards
    | RefMut
    | ResugarAsserts
    | ResugarForLoops
    | ResugarWhileLoops
    | ResugarForIndexLoops
    | ResugarQuestionMarks
    | SimplifyQuestionMarks
    | Specialize
    | HoistSideEffects
    | HoistDisjunctions
    | LocalMutation
    | TrivializeAssignLhs
    | CfIntoMonads
    | FunctionalizeLoops
    | TraitsSpecs
    | SimplifyMatchReturn
    | SimplifyHoisting
    | DropNeedlessReturns
    | TransformHaxLibInline
    | NewtypeAsRefinement
    | DummyA
    | DummyB
    | DummyC
    | Reject of Rejection.t
  [@@deriving show { with_path = false }, eq, yojson, compare, hash, sexp]

  let display = function
    | Reject rejection -> "reject_" ^ Rejection.display rejection
    | x -> [%show: t] x
end

module Context = struct
  type t =
    | Phase of Phase.t
    | Backend of Backend.t
    | ThirImport
    | DebugPrintRust
    | GenericPrinter of string
    | Other of string
  [@@deriving show, eq, yojson, compare]

  let display = function
    | Phase p -> Phase.display p
    | Backend backend -> [%show: Backend.t] backend ^ " backend"
    | ThirImport -> "AST import"
    | DebugPrintRust -> "Rust debug printer"
    | GenericPrinter kind -> kind ^ " generic printer"
    | Other s -> "Other (" ^ s ^ ")"
end

type kind = T.kind [@@deriving show, eq]

let compare_kind (a : kind) (b : kind) =
  [%compare: string] ([%show: kind] a) ([%show: kind] b)

type thir_span = T.span [@@deriving show, eq]

let compare_thir_span (a : thir_span) (b : thir_span) =
  [%compare: string] ([%show: thir_span] a) ([%show: thir_span] b)

type t = { context : Context.t; kind : kind; span : thir_span list }
[@@deriving show, eq, compare]

let to_thir_diagnostic (d : t) : Types.diagnostics =
  { kind = d.kind; context = Context.display d.context; span = d.span }

(** Ask `cargo-hax` to pretty print a diagnostic *)
let ask_diagnostic_pretty_print diag : string =
  Hax_io.request (PrettyPrintDiagnostic diag)
    ~expected:"PrettyPrintedDiagnostic" (function
    | Types.PrettyPrintedDiagnostic s -> Some s
    | _ -> None)

let pretty_print : t -> string =
  to_thir_diagnostic >> ask_diagnostic_pretty_print

let pretty_print_context_kind : Context.t -> kind -> string =
 fun context kind ->
  let span = Span.to_thir (Span.dummy ()) in
  pretty_print { context; kind; span }

module Core : sig
  val raise_fatal_error : 'never. t -> 'never
  val report : t -> unit
  val try_ : 'x. (unit -> 'x) -> t list * 'x option
  val capture : 'a. (unit -> 'a) -> 'a * t list
end = struct
  (* a mutable state for collecting errors *)
  let state = ref []
  let report e = state := !state @ [ e ]

  exception Error

  let raise_fatal_error e =
    report e;
    raise Error

  let try_ f =
    let result = try Some (f ()) with Error -> None in
    (!state, result)

  let capture (type a) (f : unit -> a) : a * t list =
    let previous_state = !state in
    state := [];
    let result =
      let x = f () in
      (x, !state)
    in
    state := previous_state;
    result
end

include Core

let failure ~context ~span kind =
  Core.raise_fatal_error { context; kind; span = Span.to_thir span }

module SpanFreeError : sig
  type t = private Data of Context.t * kind [@@deriving show]

  exception Exn of t

  val payload : t -> Context.t * kind
  val raise : ?span:T.span list -> Context.t -> kind -> 'a
end = struct
  type t = Data of Context.t * kind [@@deriving show]

  exception Exn of t

  let payload (Data (ctx, kind)) = (ctx, kind)

  let raise_without_reporting (ctx : Context.t) (kind : kind) =
    raise (Exn (Data (ctx, kind)))

  let raise ?(span = []) (ctx : Context.t) (kind : kind) =
    report { span; kind; context = ctx };
    raise_without_reporting ctx kind
end
