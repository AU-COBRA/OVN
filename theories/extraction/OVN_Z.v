From Coq Require Import List.
From Coq Require Import ZArith.
From Coq Require Import Lia.
From ConCert.Utils Require Import Extras.
From ConCert.Utils Require Import RecordUpdate.
From ConCert.Execution Require Import Blockchain.
From ConCert.Execution Require Import Containers.
From ConCert.Execution Require Import Monad.
From ConCert.Execution Require Import ResultMonad.
From ConCert.Execution Require Import Serializable.
From ConCert.Execution Require Import ContractCommon. Import AddressMap.
From OVN Require Import ConCert_ovn.

Import ListNotations.


Module OVN_Z <: OVNParams.
  Definition AddrSize : N := 64.
  Definition ContractAddrBase : N := AddrSize / 2.

  Definition T : Type := Z.
  Definition ser_T : Serializable T := int_serializable.
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




  Fixpoint egcd_aux
          (n : nat)
          (r0 a0 b0 r1 a1 b1 : Z) {struct n} : Z * Z :=
    (match n with
    | 0%nat => (0, 0)
    | S n => let (q, r) := Z.div_eucl r0 r1 in
            if r =? 0 then
              (a1, b1)
            else
              egcd_aux n r1 a1 b1 r (a0 - q*a1) (b0 - q*b1)
    end)%Z.

  (* returns (x, y) such that x*m + y*n = Z.gcd(x, y) *)
  Definition egcd (m n : Z) : Z * Z :=
    (if m =? 0 then
      (0, Z.sgn n)
    else if n =? 0 then
      (Z.sgn m, 0)
    else
      let num_steps := S (Z.to_nat (Z.log2 (Z.abs m) + Z.log2 (Z.abs n))) in
      if Z.abs m <? Z.abs n then
        let (x, y) := egcd_aux num_steps (Z.abs n) 1 0 (Z.abs m) 0 1 in
        (Z.sgn m * y, Z.sgn n * x)
      else
        let (x, y) := egcd_aux num_steps (Z.abs m) 1 0 (Z.abs n) 0 1 in
        (Z.sgn m * x, Z.sgn n * y))%Z.

  Definition mod_inv (a : Z) (p : Z) : Z :=
    let x := (egcd a p) in
    (fst x) mod p.

  Fixpoint mod_pow_pos_aux (a : Z) (x : positive) (m : Z) (r : Z) : Z :=
    match x with
    | x~0%positive => mod_pow_pos_aux (a * a mod m) x m r
    | x~1%positive => mod_pow_pos_aux (a * a mod m) x m (r * a mod m)
    | _ => r * a mod m
    end.

  Definition mod_pow_pos (a : Z) (x : positive) (m : Z) : Z :=
    mod_pow_pos_aux a x m 1.

  Definition mod_pow (a x p : Z) : Z :=
    match x with
    | Z0 => a ^ 0 mod p
    | Zpos x => mod_pow_pos a x p
    | Zneg x => mod_inv (mod_pow_pos a x p) p
    end.

  Definition field_Z : Field Z :=
    (* let f_q := 250%Z (* 251 -1*) (* 89%Z  *)in *)
    (* let f_q := 4294967290%Z in *)
    let f_q := 18446744073709551557%Z in
    let q := (* 88%Z *) f_q in
    {|
      f_q := f_q;
      f_zero := 0%Z;
      f_one := 1%Z;
      f_add x y :=
        (* let q := Z.sub f_q 1%Z in *)
        (* let x := Z.modulo x q in *)
        (* let y := Z.modulo y q in *)
        Z.modulo (Z.add x y) q;
      f_opp x :=
        (* let q := Z.sub f_q 1%Z in *)
        (* let x := Z.modulo x q in *)
        Z.sub q x;
      f_mul x y :=
        (* let q := Z.sub f_q 1%Z in *)
        (* let x := Z.modulo x q in *)
        (* let y := Z.modulo y q in *)
        Z.modulo (Z.mul x y) q;
      f_inv x :=
        (* let q := Z.sub f_q 1%Z in *)
        mod_inv x q;
    |}.

  Definition group_Z : Group Z :=
    let g_f := field_Z in
    (* let g_g := 6%Z (* 3%Z  *)in *)
    let g_g := 22%Z in
    let q := (* 88%Z *) g_f.(f_q) in
    let g_prod x y :=
      (* let q := Z.sub g_f.(f_q) 1%Z in *)
      (* let x := Z.modulo x q in *)
      (* let y := Z.modulo y q in *)
      Z.modulo (Z.mul x y) q in
    let g_pow x y :=
      (* let q := Z.sub g_f.(f_q) 1%Z in *)
      mod_pow x y q in
  {|
    g_f := g_f;
    g_g := g_g;
    g_g_pow x := g_pow g_g x;
    g_pow := g_pow;
    g_one := 1%Z;
    g_prod := g_prod;
    g_inv x :=
      (* let q := Z.sub g_f.(f_q) 1%Z in *)
      mod_inv x q;
    hash := fun a => 14%Z;
  |}.

  Definition group : Group T := group_Z.

  Definition t_eqb := Z.eqb.
  Definition t_eqb_spec := Z.eqb_spec.

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
  let secrets0 := (
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
    12554%Z) in
(*   let secrets0 := (
    (* secret key*)
    30%Z,
    (* vote *)
    true,
    (* randomness *)
    3%Z,
    5%Z,
    19%Z,
    4%Z) in
  let secrets1 := (
    (* secret key*)
    12%Z,
    (* vote *)
    true,
    (* randomness *)
    3%Z,
    1%Z,
    1%Z,
    1%Z) in
  let secrets2 := (
    (* secret key*)
    9%Z,
    (* vote *)
    false,
    (* randomness *)
    4%Z,
    1%Z,
    1%Z,
    1%Z) in
  let secrets3 := (
    (* secret key*)
    37%Z,
    (* vote *)
    true,
    (* randomness *)
    5%Z,
    1%Z,
    1%Z,
    1%Z) in
  let secrets4 := (
    (* secret key*)
    23%Z,
    (* vote *)
    false,
    (* randomness *)
    6%Z,
    1%Z,
    1%Z,
    1%Z) in *)

  (* Registration params *)
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
  let mk_com (n : nat) (s : Z * bool * Z * Z * Z * Z) :=
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
