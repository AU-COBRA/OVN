module Rust_primitives.Hax

open Rust_primitives.Integers
open Rust_primitives.Arrays

type t_Never = False
let never_to_any #t: t_Never -> t = (fun _ -> match () with)

let repeat (#t:Type0) (x: t) (len: usize): t_Array t len = 
  FStar.Seq.create (v len) x

open Core.Ops.Index
class update_at_tc self idx = {
  [@@@FStar.Tactics.Typeclasses.tcinstance]
  super_index: t_Index self idx;
  update_at: s: self -> i: idx {in_range s i} -> super_index.f_Output -> self;
}

open Core.Slice

instance impl__index t n: t_Index (t_Slice t) (pub_int_t n)
  = { f_Output = t;
      in_range = (fun (s: t_Slice t) (i: pub_int_t n) -> v i >= 0 && v i < Seq.length s);
      f_index = (fun s i -> Seq.index s (v i));
    }

instance impl__index_array t l n: t_Index (t_Array t l) (pub_int_t n)
  = { f_Output = t;
      in_range = (fun (s: t_Array t l) (i: pub_int_t n) -> v i >= 0 && v i < v l);
      f_index = (fun s i -> Seq.index s (v i));
    }

instance update_at_tc_slice t n: update_at_tc (t_Slice t) (pub_int_t n) = {
  super_index = FStar.Tactics.Typeclasses.solve <: t_Index (t_Slice t) (pub_int_t n);
  update_at = (fun arr i x -> FStar.Seq.upd arr (v i) x);
}

instance update_at_tc_array t l n: update_at_tc (t_Array t l) (pub_int_t n) = {
  super_index = FStar.Tactics.Typeclasses.solve <: t_Index (t_Array t l) (pub_int_t n);
  update_at = (fun arr i x -> FStar.Seq.upd arr (v i) x);
}


let (.[]<-) #self #idx {| update_at_tc self idx |} (s: self) (i: idx {in_range s i})
  = update_at s i

let array_of_list #t = Rust_primitives.Arrays.of_list #t

