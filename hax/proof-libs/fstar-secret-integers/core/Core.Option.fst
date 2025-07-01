module Core.Option

type t_Option t = | Option_Some of t | Option_None

let impl__and_then #t #t_Self (self: t_Option t_Self) (f: t_Self -> t_Option t): t_Option t = 
  match self with
  | Option_Some x -> f x
  | Option_None -> Option_None

let impl__unwrap #t (x: t_Option t {Option_Some? x}): t = Option_Some?._0 x

let impl__is_some #t_Self (self: t_Option t_Self): bool =  Option_Some? self

