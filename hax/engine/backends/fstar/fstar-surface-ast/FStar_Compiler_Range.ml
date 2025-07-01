open Prims
type file_name = Prims.string[@@deriving yojson,show]
type pos = {
  line: Prims.int ;
  col: Prims.int }[@@deriving yojson,show,yojson,show]
let (__proj__Mkpos__item__line : pos -> Prims.int) =
  fun projectee -> match projectee with | { line; col;_} -> line
let (__proj__Mkpos__item__col : pos -> Prims.int) =
  fun projectee -> match projectee with | { line; col;_} -> col
let (max : Prims.int -> Prims.int -> Prims.int) =
  fun i -> fun j -> if i < j then j else i
let (pos_geq : pos -> pos -> Prims.bool) =
  fun p1 ->
    fun p2 ->
      (p1.line > p2.line) || ((p1.line = p2.line) && (p1.col >= p2.col))
type rng = {
  file_name: file_name ;
  start_pos: pos ;
  end_pos: pos }[@@deriving yojson,show,yojson,show]
let (__proj__Mkrng__item__file_name : rng -> file_name) =
  fun projectee ->
    match projectee with
    | { file_name = file_name1; start_pos; end_pos;_} -> file_name1
let (__proj__Mkrng__item__start_pos : rng -> pos) =
  fun projectee ->
    match projectee with
    | { file_name = file_name1; start_pos; end_pos;_} -> start_pos
let (__proj__Mkrng__item__end_pos : rng -> pos) =
  fun projectee ->
    match projectee with
    | { file_name = file_name1; start_pos; end_pos;_} -> end_pos
type range = {
  def_range: rng ;
  use_range: rng }[@@deriving yojson,show,yojson,show]
let (__proj__Mkrange__item__def_range : range -> rng) =
  fun projectee ->
    match projectee with | { def_range; use_range;_} -> def_range
let (__proj__Mkrange__item__use_range : range -> rng) =
  fun projectee ->
    match projectee with | { def_range; use_range;_} -> use_range
let (dummy_pos : pos) = { line = Prims.int_zero; col = Prims.int_zero }
let (dummy_rng : rng) =
  { file_name = " dummy"; start_pos = dummy_pos; end_pos = dummy_pos }
let (dummyRange : range) = { def_range = dummy_rng; use_range = dummy_rng }
let (use_range : range -> rng) = fun r -> r.use_range
let (def_range : range -> rng) = fun r -> r.def_range
let (range_of_rng : rng -> rng -> range) =
  fun d -> fun u -> { def_range = d; use_range = u }
let (set_use_range : range -> rng -> range) =
  fun r2 ->
    fun use_rng ->
      if use_rng <> dummy_rng
      then { def_range = (r2.def_range); use_range = use_rng }
      else r2
let (set_def_range : range -> rng -> range) =
  fun r2 ->
    fun def_rng ->
      if def_rng <> dummy_rng
      then { def_range = def_rng; use_range = (r2.use_range) }
      else r2
let (mk_pos : Prims.int -> Prims.int -> pos) =
  fun l ->
    fun c -> { line = (max Prims.int_zero l); col = (max Prims.int_zero c) }
let (mk_rng : file_name -> pos -> pos -> rng) =
  fun file_name1 ->
    fun start_pos ->
      fun end_pos -> { file_name = file_name1; start_pos; end_pos }
let (mk_range : Prims.string -> pos -> pos -> range) =
  fun f -> fun b -> fun e -> let r = mk_rng f b e in range_of_rng r r
let (union_rng : rng -> rng -> rng) =
  fun r1 ->
    fun r2 ->
      if r1.file_name <> r2.file_name
      then r2
      else
        (let start_pos =
           if pos_geq r1.start_pos r2.start_pos
           then r2.start_pos
           else r1.start_pos in
         let end_pos =
           if pos_geq r1.end_pos r2.end_pos then r1.end_pos else r2.end_pos in
         mk_rng r1.file_name start_pos end_pos)
let (union_ranges : range -> range -> range) =
  fun r1 ->
    fun r2 ->
      let uu___ = union_rng r1.def_range r2.def_range in
      let uu___1 = union_rng r1.use_range r2.use_range in
      { def_range = uu___; use_range = uu___1 }
let (rng_included : rng -> rng -> Prims.bool) =
  fun r1 ->
    fun r2 ->
      if r1.file_name <> r2.file_name
      then false
      else
        (pos_geq r1.start_pos r2.start_pos) &&
          (pos_geq r2.end_pos r1.end_pos)
let (string_of_pos : pos -> Prims.string) =
  fun pos1 ->
    let uu___ = FStar_Compiler_Util.string_of_int pos1.line in
    let uu___1 = FStar_Compiler_Util.string_of_int pos1.col in
    FStar_Compiler_Util.format2 "%s,%s" uu___ uu___1
let (string_of_file_name : Prims.string -> Prims.string) =
  fun f ->
    f
let (file_of_range : range -> Prims.string) =
  fun r -> let f = (r.def_range).file_name in string_of_file_name f
let (set_file_of_range : range -> Prims.string -> range) =
  fun r ->
    fun f ->
      {
        def_range =
          (let uu___ = r.def_range in
           {
             file_name = f;
             start_pos = (uu___.start_pos);
             end_pos = (uu___.end_pos)
           });
        use_range = (r.use_range)
      }
let (string_of_rng : rng -> Prims.string) =
  fun r ->
    let uu___ = string_of_file_name r.file_name in
    let uu___1 = string_of_pos r.start_pos in
    let uu___2 = string_of_pos r.end_pos in
    FStar_Compiler_Util.format3 "%s(%s-%s)" uu___ uu___1 uu___2
let (string_of_def_range : range -> Prims.string) =
  fun r -> string_of_rng r.def_range
let (string_of_use_range : range -> Prims.string) =
  fun r -> string_of_rng r.use_range
let (string_of_range : range -> Prims.string) =
  fun r -> string_of_def_range r
let (start_of_range : range -> pos) = fun r -> (r.def_range).start_pos
let (end_of_range : range -> pos) = fun r -> (r.def_range).end_pos
let (file_of_use_range : range -> Prims.string) =
  fun r -> (r.use_range).file_name
let (start_of_use_range : range -> pos) = fun r -> (r.use_range).start_pos
let (end_of_use_range : range -> pos) = fun r -> (r.use_range).end_pos
let (line_of_pos : pos -> Prims.int) = fun p -> p.line
let (col_of_pos : pos -> Prims.int) = fun p -> p.col
let (end_range : range -> range) =
  fun r ->
    mk_range (r.def_range).file_name (r.def_range).end_pos
      (r.def_range).end_pos
let (compare_rng : rng -> rng -> Prims.int) =
  fun r1 ->
    fun r2 ->
      let fcomp = FStar_String.compare r1.file_name r2.file_name in
      if fcomp = Prims.int_zero
      then
        let start1 = r1.start_pos in
        let start2 = r2.start_pos in
        let lcomp = start1.line - start2.line in
        (if lcomp = Prims.int_zero then start1.col - start2.col else lcomp)
      else fcomp
let (compare : range -> range -> Prims.int) =
  fun r1 -> fun r2 -> compare_rng r1.def_range r2.def_range
let (compare_use_range : range -> range -> Prims.int) =
  fun r1 -> fun r2 -> compare_rng r1.use_range r2.use_range
let (range_before_pos : range -> pos -> Prims.bool) =
  fun m1 -> fun p -> let uu___ = end_of_range m1 in pos_geq p uu___
let (end_of_line : pos -> pos) =
  fun p -> { line = (p.line); col = FStar_Compiler_Util.max_int }
let (extend_to_end_of_line : range -> range) =
  fun r ->
    let uu___ = file_of_range r in
    let uu___1 = start_of_range r in
    let uu___2 = let uu___3 = end_of_range r in end_of_line uu___3 in
    mk_range uu___ uu___1 uu___2
