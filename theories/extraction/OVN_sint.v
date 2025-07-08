

From Coq Require Import Sint63.



Module OVN_Z <: OVNParams.
  Definition AddrSize : N := 64.
  Definition ContractAddrBase : N := AddrSize / 2.

  Definition T : Type := int.
  Definition ser_T : Serializable T. Admitted.
  Definition base : ChainBase := {|
    Address := N;
    address_eqb := N.eqb;
    address_eqb_spec := N.eqb_spec;
    address_is_contract a := (ContractAddrBase <=? a)%N
  |}.
(*   Definition base : ChainBase := {|
    Address := (BoundedN AddrSize);
    address_eqb := BoundedN.eqb;
    address_eqb_spec := BoundedN.eqb_spec;
    address_is_contract a := (ContractAddrBase <=? BoundedN.to_N a)%N
  |}. *)

  (* Definition modulus := 0. *)



  #[bypass_check(guard)]
  Program Fixpoint egcd_aux
          (n : int)
          (r0 a0 b0 r1 a1 b1 : int) {measure (Z.to_nat (to_Z n))} : int * int :=
    (if n =? 0
    then (0, 0)
    else
      let m := n - 1 in
      let (q, r) := diveucl r0 r1 in
      if eqb r 0
      then (a1, b1)
      else egcd_aux n r1 a1 b1 r (a0 - q*a1) (b0 - q*b1)
    )%sint63.
  Next Obligation.
  Admitted.
  Final Obligation.
  Admitted.

  Definition sgn (n : int) : int :=
    (if n =? 0
    then 0
    else (
      if 0 <=? n
      then 1
      else -1
    ))%sint63.

  (* returns (x, y) such that x*m + y*n = Z.gcd(x, y) *)
  Definition egcd (m n : int) : int * int :=
    (if eqb m 0 then
      (0, sgn n)
    else if eqb n 0 then
      (sgn m, 0)
    else
      (* let num_steps := (Z.log2 (abs m) + Z.log2 (abs n)) + 1 in *)
      let num_steps := ((abs m) + (abs n)) in
      if abs m <? abs n then
        let (x, y) := egcd_aux num_steps (abs n) 1 0 (abs m) 0 1 in
        (sgn m * y, sgn n * x)
      else
        let (x, y) := egcd_aux num_steps (abs m) 1 0 (abs n) 0 1 in
        (sgn m * x, sgn n * y))%uint63.

  Definition mod_inv (a : int) (p : int) : int :=
    let x := (egcd a p) in
    (fst x) mod p.

  Fixpoint mod_pow_pos_aux (a : int) (x : positive) (m : int) (r : int) : int :=
    match x with
    | x~0%positive => mod_pow_pos_aux (a * a mod m) x m r
    | x~1%positive => mod_pow_pos_aux (a * a mod m) x m (r * a mod m)
    | _ => r * a mod m
    end.

  Definition mod_pow_pos (a : int) (x : positive) (m : int) : int :=
    mod_pow_pos_aux a x m 1.

  Definition mod_pow (a x p : int) : int :=
    (if x =? 0
    then 1
    else (
      if 0 <=? x
      then mod_pow_pos a (Z.to_pos (to_Z x)) p
      else mod_inv (mod_pow_pos a (Z.to_pos (Z.abs (to_Z x))) p) p
    ))%sint63.

  Definition field_int : Field int :=
    (* let f_q := 250%Z (* 251 -1*) (* 89%Z  *)in *)
    (* let f_q := 4294967290%Z in *)
    (* let f_q := 18446744073709551557%sint63 in *)
    let f_q := 250%sint63 in
    let q := (* 88%Z *) f_q in
    {|
      f_q := f_q;
      f_zero := 0%sint63;
      f_one := 1%sint63;
      f_add x y :=
        (* let q := Z.sub f_q 1%Z in *)
        (* let x := Z.modulo x q in *)
        (* let y := Z.modulo y q in *)
        ((add x y) mod q)%sint63;
      f_opp x :=
        (* let q := Z.sub f_q 1%Z in *)
        (* let x := Z.modulo x q in *)
        sub q x;
      f_mul x y :=
        (* let q := Z.sub f_q 1%Z in *)
        (* let x := Z.modulo x q in *)
        (* let y := Z.modulo y q in *)
        ((mul x y) mod q)%sint63;
      f_inv x :=
        (* let q := Z.sub f_q 1%Z in *)
        mod_inv x q;
    |}.

  Definition group_int : Group int :=
    let g_f := field_int in
    (* let g_g := 6%Z (* 3%Z  *)in *)
    (* let g_g := 22%sint63 in *)
    let g_g := 6%sint63 in
    let q := (* 88%Z *) g_f.(f_q) in
    let g_prod x y :=
      (* let q := Z.sub g_f.(f_q) 1%Z in *)
      (* let x := Z.modulo x q in *)
      (* let y := Z.modulo y q in *)
      ((mul x y) mod q)%sint63 in
    let g_pow x y :=
      (* let q := Z.sub g_f.(f_q) 1%Z in *)
      mod_pow x y q in
  {|
    g_f := g_f;
    g_g := g_g;
    g_g_pow x := g_pow g_g x;
    g_pow := g_pow;
    g_one := 1%sint63;
    g_prod := g_prod;
    g_inv x :=
      (* let q := Z.sub g_f.(f_q) 1%Z in *)
      mod_inv x q;
    hash := fun a => 14%sint63;
  |}.

  Definition group : Group T := group_int.

  Definition t_eqb := eqb.
  Definition t_eqb_spec : forall x y, Bool.reflect (x = y) (t_eqb x y). Admitted.

End OVN_Z.

Module OVN_89 := OVN OVN_Z.
Import OVN_89.


(* Goal
  let secrets0 := (
    (* secret key*)
    30%Z,
    (* vote *)
    true,
    (* randomness *)
    3%Z,
    1%Z,
    1%Z,
    1%Z) in
  let mk_reg (n : nat) (s : Z * bool * Z * Z * Z * Z) :=
  let '(x, v, sr, orw, orr, ord) := s in
  let private := {|
    rp_xi := x;
    rp_zkp_random := sr;
  |} in
  let (g_pow_xi, zkp_xi) := register_to_vote_private private in
  {|
    rp_i := n;
    rp_g_pow_xi := g_pow_xi;
    rp_zkp_xi := zkp_xi;
  |} in
  let reg_0 := mk_reg 0 secrets0 in
  let param := reg_0 in
  validate_schorr_zkp param.(rp_g_pow_xi) param.(rp_zkp_xi) = Ok tt.
  cbn -[validate_schorr_zkp register_to_vote_private].
  unfold register_to_vote_private.
  compute -[validate_schorr_zkp].
  compute -[Z.eqb]. *)


Definition ovn_test :=
  (* Call contexts *)
  let dummy_chain := {|
    chain_height := 0;
    current_slot := 0;
    finalized_height := 0;
  |} in
  let mk_ctx m := {|
    ctx_origin := m;
    ctx_from := m;
    ctx_contract_address := 0%N;
    ctx_contract_balance := 0%Z;
    ctx_amount := 0%Z;
  |} in
  let dummy_ctx_user_0 := mk_ctx 0%N in
  let dummy_ctx_user_1 := mk_ctx 1%N in
  let dummy_ctx_user_2 := mk_ctx 2%N in
  let dummy_ctx_user_3 := mk_ctx 3%N in
  let dummy_ctx_user_4 := mk_ctx 4%N in

  (* Set up contract *)
  let setup := {|
    participants := 5;
    voter_addrs := [0%N; 1%N; 2%N; 3%N; 4%N];
  |} in
  do st0 <- ovn_init dummy_chain dummy_ctx_user_0 setup;

  (* Private data *)
  (* secret key, vote, randomness *)
(*   let secrets0 := (
    (* secret key*)
    30542234%Z,
    (* vote *)
    true,
    (* randomness *)
    32436542%Z,
    45722%Z,
    19%Z,
    95505332%Z) in
  let secrets1 := (
    (* secret key*)
    6723632%Z,
    (* vote *)
    true,
    (* randomness *)
    694283%Z,
    55453%Z,
    114514544%Z,
    1323134%Z) in
  let secrets2 := (
    (* secret key*)
    917474%Z,
    (* vote *)
    false,
    (* randomness *)
    422344%Z,
    1422424%Z,
    11344%Z,
    113443%Z) in
  let secrets3 := (
    (* secret key*)
    354372337%Z,
    (* vote *)
    true,
    (* randomness *)
    435454545%Z,
    1242552%Z,
    15653%Z,
    1555%Z) in
  let secrets4 := (
    (* secret key*)
    2355%Z,
    (* vote *)
    false,
    (* randomness *)
    644%Z,
    2451%Z,
    14444%Z,
    12554%Z) in *)
  let secrets0 := (
    (* secret key*)
    30%sint63,
    (* vote *)
    true,
    (* randomness *)
    3%sint63,
    5%sint63,
    19%sint63,
    4%sint63) in
  let secrets1 := (
    (* secret key*)
    12%sint63,
    (* vote *)
    true,
    (* randomness *)
    3%sint63,
    1%sint63,
    1%sint63,
    1%sint63) in
  let secrets2 := (
    (* secret key*)
    9%sint63,
    (* vote *)
    false,
    (* randomness *)
    4%sint63,
    1%sint63,
    1%sint63,
    1%sint63) in
  let secrets3 := (
    (* secret key*)
    37%sint63,
    (* vote *)
    true,
    (* randomness *)
    5%sint63,
    1%sint63,
    1%sint63,
    1%sint63) in
  let secrets4 := (
    (* secret key*)
    23%sint63,
    (* vote *)
    false,
    (* randomness *)
    6%sint63,
    1%sint63,
    1%sint63,
    1%sint63) in

  (* Registration params *)
  let mk_reg (n : nat) (s : int * bool * int * int * int * int) :=
    let '(x, v, sr, orw, orr, ord) := s in
    let private := {|
      rp_xi := x;
      rp_zkp_random := sr;
    |} in
    let (g_pow_xi, zkp_xi) := register_to_vote_private private in
    {|
      rp_i := n;
      rp_g_pow_xi := g_pow_xi;
      rp_zkp_xi := zkp_xi;
    |} in
  let reg_0 := mk_reg 0 secrets0 in
  let reg_1 := mk_reg 1 secrets1 in
  let reg_2 := mk_reg 2 secrets2 in
  let reg_3 := mk_reg 3 secrets3 in
  let reg_4 := mk_reg 4 secrets4 in

  (* Register *)
  do '(st1, _) <- ovn_receive dummy_chain dummy_ctx_user_0 st0 (Some (msg_register reg_0));
  do '(st2, _) <- ovn_receive dummy_chain dummy_ctx_user_1 st1 (Some (msg_register reg_1));
  do '(st3, _) <- ovn_receive dummy_chain dummy_ctx_user_2 st2 (Some (msg_register reg_2));
  do '(st4, _) <- ovn_receive dummy_chain dummy_ctx_user_3 st3 (Some (msg_register reg_3));
  do '(st5, _) <- ovn_receive dummy_chain dummy_ctx_user_4 st4 (Some (msg_register reg_4));

  (* Public keys *)
  let g_pow_xis := filter_some st5.(public_keys) in

  (* Commit params *)
  let mk_com (n : nat) (s : int * bool * int * int * int * int) :=
    let '(x, v, sr, orw, orr, ord) := s in
    let private := {|
      cp_i_ := n;
      cp_xi := x;
      cp_zkp_random_w := orw;
      cp_zkp_random_r := orr;
      cp_zkp_random_d := ord;
      cp_vote := v;
    |} in
    let commit_vi := commit_to_vote_private private g_pow_xis in
    {|
      cp_i := n;
      cp_commit_vi := commit_vi;
    |} in
  let com_0 := mk_com 0 secrets0 in
  let com_1 := mk_com 1 secrets1 in
  let com_2 := mk_com 2 secrets2 in
  let com_3 := mk_com 3 secrets3 in
  let com_4 := mk_com 4 secrets4 in

  (* Commit *)
  do '(st6, _) <- ovn_receive dummy_chain dummy_ctx_user_0 st5 (Some (msg_commit com_0));
  do '(st7, _) <- ovn_receive dummy_chain dummy_ctx_user_1 st6 (Some (msg_commit com_1));
  do '(st8, _) <- ovn_receive dummy_chain dummy_ctx_user_2 st7 (Some (msg_commit com_2));
  do '(st9, _) <- ovn_receive dummy_chain dummy_ctx_user_3 st8 (Some (msg_commit com_3));
  do '(st10, _) <- ovn_receive dummy_chain dummy_ctx_user_4 st9 (Some (msg_commit com_4));

  (* Vote params *)
  let mk_vote (n : nat) (s : int * bool * int * int * int * int) :=
    let '(x, v, sr, orw, orr, ord) := s in
    let private := {|
      vp_i_ := n;
      vp_xi := x;
      vp_zkp_random_w := orw;
      vp_zkp_random_r := orr;
      vp_zkp_random_d := ord;
      vp_vote := v;
    |} in
    let (zkp_vi, g_pow_xi_yi_vi) := cast_vote_private private g_pow_xis in
    {|
      vp_i := n;
      vp_zkp_vi := zkp_vi;
      vp_g_pow_xi_yi_vi := g_pow_xi_yi_vi;
    |} in
  let vote_0 := mk_vote 0 secrets0 in
  let vote_1 := mk_vote 1 secrets1 in
  let vote_2 := mk_vote 2 secrets2 in
  let vote_3 := mk_vote 3 secrets3 in
  let vote_4 := mk_vote 4 secrets4 in
(*
  Ok st10.
  Goal ovn_test = Err 0.
  vm_compute.
  Admitted.

  Goal
  let state :=   {|
    voters :=
      [0%N; 1%N; 2%N; 3%N; 4%N];
    voters_n := 5;
    public_keys :=
      [Some 26%Z; Some 86%Z;
       Some 196%Z; Some 86%Z;
       Some 66%Z];
    schnorr_zkps :=
      [Some
         {|
           schnorr_zkp_u := 216%Z;
           schnorr_zkp_c := 14%Z;
           schnorr_zkp_z := 173%Z
         |};
       Some
         {|
           schnorr_zkp_u := 216%Z;
           schnorr_zkp_c := 14%Z;
           schnorr_zkp_z := 171%Z
         |};
       Some
         {|
           schnorr_zkp_u := 46%Z;
           schnorr_zkp_c := 14%Z;
           schnorr_zkp_z := 130%Z
         |};
       Some
         {|
           schnorr_zkp_u := 26%Z;
           schnorr_zkp_c := 14%Z;
           schnorr_zkp_z := 23%Z
         |};
       Some
         {|
           schnorr_zkp_u := 156%Z;
           schnorr_zkp_c := 14%Z;
           schnorr_zkp_z := 78%Z
         |}];
    commits :=
      [Some 14%Z; Some 14%Z;
       Some 14%Z; Some 14%Z;
       Some 14%Z];
    ballots :=
      [None; None; None; None; None];
    or_zkps :=
      [None; None; None; None; None];
    register_count := 5;
    commit_count := 5;
    vote_count := 0;
    tally := None
  |} in
  let pks := filter_some state.(public_keys) in
  let secrets0 := (
    (* secret key*)
    30%Z,
    (* vote *)
    true,
    (* randomness *)
    3%Z,
    5%Z,
    19%Z,
    4%Z) in
  let mk_vote (n : nat) (s : Z * bool * Z * Z * Z * Z) :=
    let '(x, v, sr, orw, orr, ord) := s in
    let private := {|
      vp_i_ := n;
      vp_xi := x;
      vp_zkp_random_w := orw;
      vp_zkp_random_r := orr;
      vp_zkp_random_d := ord;
      vp_vote := v;
    |} in
    let (zkp_vi, g_pow_xi_yi_vi) := cast_vote_private private pks in
    {|
      vp_i := n;
      vp_zkp_vi := zkp_vi;
      vp_g_pow_xi_yi_vi := g_pow_xi_yi_vi;
    |} in
  let vote_0 := mk_vote 0 secrets0 in
  let param := vote_0 in

  let g_pow_yi := compute_g_pow_yi param.(vp_i) pks in
  validate_or_zkp g_pow_yi param.(vp_zkp_vi) = Ok tt.
  Timeout 30 compute -[validate_or_zkp].
  unfold validate_or_zkp.
  Timeout 30 compute -[andb OVN_Z.t_eqb].

  let pks := filter_some state.(public_keys) in
  let g_pow_yi := compute_g_pow_yi param.(vp_i) pks in
  do _ <- validate_or_zkp g_pow_yi param.(vp_zkp_vi);*)




  (* Vote *)
  (* do '(st3, _) <- ovn_receive dummy_chain dummy_ctx_user_0 st2 (Some (msg_vote vote_0)); *)
  do '(st11, _) <- ovn_receive dummy_chain dummy_ctx_user_0 st10 (Some (msg_vote vote_0));
  do '(st12, _) <- ovn_receive dummy_chain dummy_ctx_user_1 st11 (Some (msg_vote vote_1));
  do '(st13, _) <- ovn_receive dummy_chain dummy_ctx_user_2 st12 (Some (msg_vote vote_2));
  do '(st14, _) <- ovn_receive dummy_chain dummy_ctx_user_3 st13 (Some (msg_vote vote_3));
  do '(st15, _) <- ovn_receive dummy_chain dummy_ctx_user_4 st14 (Some (msg_vote vote_4));


  (* Tally *)
  do '(st16, _) <- ovn_receive dummy_chain dummy_ctx_user_0 st15 (Some msg_tally);
  Ok st16.(tally).


  (* Timeout 10 Eval vm_compute in ovn_test. *)
(*
  Goal
    let state := {|
      voters := [0%N; 1%N; 2%N; 3%N; 4%N];
      voters_n := 5;
      public_keys :=
        [Some 26%Z; Some 86%Z; Some 196%Z; Some 86%Z; Some 66%Z];
      schnorr_zkps :=
        [Some
           {|
             schnorr_zkp_u := 216%Z;
             schnorr_zkp_c := 14%Z;
             schnorr_zkp_z := 173%Z
           |};
         Some
           {|
             schnorr_zkp_u := 216%Z;
             schnorr_zkp_c := 14%Z;
             schnorr_zkp_z := 171%Z
           |};
         Some
           {|
             schnorr_zkp_u := 46%Z;
             schnorr_zkp_c := 14%Z;
             schnorr_zkp_z := 130%Z
           |};
         Some
           {|
             schnorr_zkp_u := 26%Z;
             schnorr_zkp_c := 14%Z;
             schnorr_zkp_z := 23%Z
           |};
         Some
           {|
             schnorr_zkp_u := 156%Z;
             schnorr_zkp_c := 14%Z;
             schnorr_zkp_z := 78%Z
           |}];
      commits := [Some 14%Z; Some 14%Z; Some 14%Z; Some 14%Z; Some 14%Z];
      ballots :=
        [Some 94%Z; Some 136%Z; Some 192%Z; Some 92%Z; Some 146%Z];
      or_zkps :=
        [Some
           {|
             or_zkp_x := 26%Z;
             or_zkp_y := 94%Z;
             or_zkp_a1 := 96%Z;
             or_zkp_b1 := 188%Z;
             or_zkp_a2 := 26%Z;
             or_zkp_b2 := 232%Z;
             or_zkp_c := 14%Z;
             or_zkp_d1 := 4%Z;
             or_zkp_d2 := 10%Z;
             or_zkp_r1 := 19%Z;
             or_zkp_r2 := 205%Z
           |};
         Some
           {|
             or_zkp_x := 86%Z;
             or_zkp_y := 136%Z;
             or_zkp_a1 := 16%Z;
             or_zkp_b1 := 232%Z;
             or_zkp_a2 := 6%Z;
             or_zkp_b2 := 112%Z;
             or_zkp_c := 14%Z;
             or_zkp_d1 := 1%Z;
             or_zkp_d2 := 13%Z;
             or_zkp_r1 := 1%Z;
             or_zkp_r2 := 95%Z
           |};
         Some
           {|
             or_zkp_x := 196%Z;
             or_zkp_y := 192%Z;
             or_zkp_a1 := 6%Z;
             or_zkp_b1 := 122%Z;
             or_zkp_a2 := 176%Z;
             or_zkp_b2 := 58%Z;
             or_zkp_c := 14%Z;
             or_zkp_d1 := 13%Z;
             or_zkp_d2 := 1%Z;
             or_zkp_r1 := 134%Z;
             or_zkp_r2 := 1%Z
           |};
         Some
           {|
             or_zkp_x := 86%Z;
             or_zkp_y := 92%Z;
             or_zkp_a1 := 16%Z;
             or_zkp_b1 := 244%Z;
             or_zkp_a2 := 6%Z;
             or_zkp_b2 := 182%Z;
             or_zkp_c := 14%Z;
             or_zkp_d1 := 1%Z;
             or_zkp_d2 := 13%Z;
             or_zkp_r1 := 1%Z;
             or_zkp_r2 := 20%Z
           |};
         Some
           {|
             or_zkp_x := 66%Z;
             or_zkp_y := 146%Z;
             or_zkp_a1 := 6%Z;
             or_zkp_b1 := 16%Z;
             or_zkp_a2 := 146%Z;
             or_zkp_b2 := 112%Z;
             or_zkp_c := 14%Z;
             or_zkp_d1 := 13%Z;
             or_zkp_d2 := 1%Z;
             or_zkp_r1 := 202%Z;
             or_zkp_r2 := 1%Z
           |}];
      register_count := 5;
      commit_count := 5;
      vote_count := 5;
      tally := Some 0
    |} in
  let vote_result := compute_ballot_product state.(ballots) in
  let res := bruteforce_tally state.(voters_n) f_zero vote_result in
  res = 0.
  Timeout 20 compute -[bruteforce_tally].
  unfold bruteforce_tally.
  compute [f_one f_add].
  Timeout 20 compute -[g_g_pow OVN_Z.t_eqb].
  cbn.

  compute -[OVN_Z.t_eqb].*)

(*   do '(st1, _) <- ovn_receive dummy_chain dummy_ctx_user_0 st0 (Some msg_tally);
  Ok st1.(tally). *)

(* Timeout 10 Eval vm_compute in ovn_test. *)

(* Definition test := @Ok _ unit (Some 2). *)
(* Definition test := @Err unit unit tt. *)

Set Warnings "-primitive-turned-into-axiom".
From CertiCoq.Plugin Require Import CertiCoq.

(* CertiCoq Compile Wasm test. *)
CertiCoq Compile Wasm ovn_test.
