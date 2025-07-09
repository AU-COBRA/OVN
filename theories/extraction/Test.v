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
From OVN Require Import OVN_uint.
From Coq Require Import Uint63.

Import ListNotations.


Module OVN_Uint63' := OVN_Uint63 G_9223372036854775783.
(* Module OVN_Uint63' := OVN_Uint63 G_4294967291. *)
(* Module OVN_Uint63' := OVN_Uint63 G_251. *)
Import OVN_Uint63'.



Definition T : Type := int.

Definition ovn_test_5 :=
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
    305422%uint63,
    (* vote *)
    true,
    (* randomness *)
    3243652%uint63,
    45722%uint63,
    19%uint63,
    955053%uint63) in
  let secrets1 := (
    (* secret key*)
    672363%uint63,
    (* vote *)
    true,
    (* randomness *)
    694283%uint63,
    55453%uint63,
    1145145%uint63,
    132313%uint63) in
  let secrets2 := (
    (* secret key*)
    91747%uint63,
    (* vote *)
    false,
    (* randomness *)
    422344%uint63,
    14224%uint63,
    11344%uint63,
    113443%uint63) in
  let secrets3 := (
    (* secret key*)
    354372%uint63,
    (* vote *)
    true,
    (* randomness *)
    435454%uint63,
    1242552%uint63,
    15653%uint63,
    1555%uint63) in
  let secrets4 := (
    (* secret key*)
    2355%uint63,
    (* vote *)
    false,
    (* randomness *)
    644%uint63,
    2451%uint63,
    1444%uint63,
    12554%uint63) in

  (* Registration params *)
  let mk_reg (n : nat) (s : T * bool * T * T * T * T) :=
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
  let mk_com (n : nat) (s : T * bool * T * T * T * T) :=
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
  let mk_vote (n : nat) (s : T * bool * T * T * T * T) :=
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

  (* Vote *)
  do '(st11, _) <- ovn_receive dummy_chain dummy_ctx_user_0 st10 (Some (msg_vote vote_0));
  do '(st12, _) <- ovn_receive dummy_chain dummy_ctx_user_1 st11 (Some (msg_vote vote_1));
  do '(st13, _) <- ovn_receive dummy_chain dummy_ctx_user_2 st12 (Some (msg_vote vote_2));
  do '(st14, _) <- ovn_receive dummy_chain dummy_ctx_user_3 st13 (Some (msg_vote vote_3));
  do '(st15, _) <- ovn_receive dummy_chain dummy_ctx_user_4 st14 (Some (msg_vote vote_4));

  (* Tally *)
  do '(st16, _) <- ovn_receive dummy_chain dummy_ctx_user_0 st15 (Some msg_tally);
  Ok st16.(tally).

Definition ovn_test_10 :=
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
  let dummy_ctx_user_5 := mk_ctx 5%N in
  let dummy_ctx_user_6 := mk_ctx 6%N in
  let dummy_ctx_user_7 := mk_ctx 7%N in
  let dummy_ctx_user_8 := mk_ctx 8%N in
  let dummy_ctx_user_9 := mk_ctx 9%N in

  (* Set up contract *)
  let setup := {|
    participants := 10;
    voter_addrs := [0; 1; 2; 3; 4; 5; 6; 7; 8; 9]%N;
  |} in
  do st0 <- ovn_init dummy_chain dummy_ctx_user_0 setup;

  (* Private data *)
  (* secret key, vote, randomness *)
  let secrets0 := (
    (* secret key*)
    305422%uint63,
    (* vote *)
    true,
    (* randomness *)
    3243652%uint63,
    45722%uint63,
    19%uint63,
    955053%uint63) in
  let secrets1 := (
    (* secret key*)
    672363%uint63,
    (* vote *)
    true,
    (* randomness *)
    694283%uint63,
    55453%uint63,
    1145145%uint63,
    132313%uint63) in
  let secrets2 := (
    (* secret key*)
    91747%uint63,
    (* vote *)
    false,
    (* randomness *)
    422344%uint63,
    14224%uint63,
    11344%uint63,
    113443%uint63) in
  let secrets3 := (
    (* secret key*)
    354372%uint63,
    (* vote *)
    true,
    (* randomness *)
    435454%uint63,
    1242552%uint63,
    15653%uint63,
    1555%uint63) in
  let secrets4 := (
    (* secret key*)
    2355%uint63,
    (* vote *)
    false,
    (* randomness *)
    644%uint63,
    2451%uint63,
    1444%uint63,
    12554%uint63) in

  (* Registration params *)
  let mk_reg (n : nat) (s : T * bool * T * T * T * T) :=
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
  let reg_5 := mk_reg 5 secrets0 in
  let reg_6 := mk_reg 6 secrets1 in
  let reg_7 := mk_reg 7 secrets2 in
  let reg_8 := mk_reg 8 secrets3 in
  let reg_9 := mk_reg 9 secrets4 in

  (* Register *)
  do '(st1, _) <- ovn_receive dummy_chain dummy_ctx_user_0 st0 (Some (msg_register reg_0));
  do '(st2, _) <- ovn_receive dummy_chain dummy_ctx_user_1 st1 (Some (msg_register reg_1));
  do '(st3, _) <- ovn_receive dummy_chain dummy_ctx_user_2 st2 (Some (msg_register reg_2));
  do '(st4, _) <- ovn_receive dummy_chain dummy_ctx_user_3 st3 (Some (msg_register reg_3));
  do '(st5, _) <- ovn_receive dummy_chain dummy_ctx_user_4 st4 (Some (msg_register reg_4));
  do '(st6, _) <- ovn_receive dummy_chain dummy_ctx_user_5 st5 (Some (msg_register reg_5));
  do '(st7, _) <- ovn_receive dummy_chain dummy_ctx_user_6 st6 (Some (msg_register reg_6));
  do '(st8, _) <- ovn_receive dummy_chain dummy_ctx_user_7 st7 (Some (msg_register reg_7));
  do '(st9, _) <- ovn_receive dummy_chain dummy_ctx_user_8 st8 (Some (msg_register reg_8));
  do '(st10, _) <- ovn_receive dummy_chain dummy_ctx_user_9 st9 (Some (msg_register reg_9));

  (* Public keys *)
  let g_pow_xis := filter_some st10.(public_keys) in

  (* Commit params *)
  let mk_com (n : nat) (s : T * bool * T * T * T * T) :=
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
  let com_5 := mk_com 5 secrets0 in
  let com_6 := mk_com 6 secrets1 in
  let com_7 := mk_com 7 secrets2 in
  let com_8 := mk_com 8 secrets3 in
  let com_9 := mk_com 9 secrets4 in

  (* Commit *)
  do '(st11, _) <- ovn_receive dummy_chain dummy_ctx_user_0 st10 (Some (msg_commit com_0));
  do '(st12, _) <- ovn_receive dummy_chain dummy_ctx_user_1 st11 (Some (msg_commit com_1));
  do '(st13, _) <- ovn_receive dummy_chain dummy_ctx_user_2 st12 (Some (msg_commit com_2));
  do '(st14, _) <- ovn_receive dummy_chain dummy_ctx_user_3 st13 (Some (msg_commit com_3));
  do '(st15, _) <- ovn_receive dummy_chain dummy_ctx_user_4 st14 (Some (msg_commit com_4));
  do '(st16, _) <- ovn_receive dummy_chain dummy_ctx_user_5 st15 (Some (msg_commit com_5));
  do '(st17, _) <- ovn_receive dummy_chain dummy_ctx_user_6 st16 (Some (msg_commit com_6));
  do '(st18, _) <- ovn_receive dummy_chain dummy_ctx_user_7 st17 (Some (msg_commit com_7));
  do '(st19, _) <- ovn_receive dummy_chain dummy_ctx_user_8 st18 (Some (msg_commit com_8));
  do '(st20, _) <- ovn_receive dummy_chain dummy_ctx_user_9 st19 (Some (msg_commit com_9));

  (* Vote params *)
  let mk_vote (n : nat) (s : T * bool * T * T * T * T) :=
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
  let vote_5 := mk_vote 5 secrets0 in
  let vote_6 := mk_vote 6 secrets1 in
  let vote_7 := mk_vote 7 secrets2 in
  let vote_8 := mk_vote 8 secrets3 in
  let vote_9 := mk_vote 9 secrets4 in

  (* Vote *)
  do '(st21, _) <- ovn_receive dummy_chain dummy_ctx_user_0 st20 (Some (msg_vote vote_0));
  do '(st22, _) <- ovn_receive dummy_chain dummy_ctx_user_1 st21 (Some (msg_vote vote_1));
  do '(st23, _) <- ovn_receive dummy_chain dummy_ctx_user_2 st22 (Some (msg_vote vote_2));
  do '(st24, _) <- ovn_receive dummy_chain dummy_ctx_user_3 st23 (Some (msg_vote vote_3));
  do '(st25, _) <- ovn_receive dummy_chain dummy_ctx_user_4 st24 (Some (msg_vote vote_4));
  do '(st26, _) <- ovn_receive dummy_chain dummy_ctx_user_5 st25 (Some (msg_vote vote_5));
  do '(st27, _) <- ovn_receive dummy_chain dummy_ctx_user_6 st26 (Some (msg_vote vote_6));
  do '(st28, _) <- ovn_receive dummy_chain dummy_ctx_user_7 st27 (Some (msg_vote vote_7));
  do '(st29, _) <- ovn_receive dummy_chain dummy_ctx_user_8 st28 (Some (msg_vote vote_8));
  do '(st30, _) <- ovn_receive dummy_chain dummy_ctx_user_9 st29 (Some (msg_vote vote_9));

  (* Tally *)
  do '(st31, _) <- ovn_receive dummy_chain dummy_ctx_user_0 st30 (Some msg_tally);
  Ok st31.(tally).

Definition ovn_test_20 :=
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
  let dummy_ctx_user_5 := mk_ctx 5%N in
  let dummy_ctx_user_6 := mk_ctx 6%N in
  let dummy_ctx_user_7 := mk_ctx 7%N in
  let dummy_ctx_user_8 := mk_ctx 8%N in
  let dummy_ctx_user_9 := mk_ctx 9%N in
  let dummy_ctx_user_10 := mk_ctx 10%N in
  let dummy_ctx_user_11 := mk_ctx 11%N in
  let dummy_ctx_user_12 := mk_ctx 12%N in
  let dummy_ctx_user_13 := mk_ctx 13%N in
  let dummy_ctx_user_14 := mk_ctx 14%N in
  let dummy_ctx_user_15 := mk_ctx 15%N in
  let dummy_ctx_user_16 := mk_ctx 16%N in
  let dummy_ctx_user_17 := mk_ctx 17%N in
  let dummy_ctx_user_18 := mk_ctx 18%N in
  let dummy_ctx_user_19 := mk_ctx 19%N in

  (* Set up contract *)
  let setup := {|
    participants := 20;
    voter_addrs := [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19]%N;
  |} in
  do st0 <- ovn_init dummy_chain dummy_ctx_user_0 setup;

  (* Private data *)
  (* secret key, vote, randomness *)
  let secrets0 := (
    (* secret key*)
    305422%uint63,
    (* vote *)
    true,
    (* randomness *)
    3243652%uint63,
    45722%uint63,
    19%uint63,
    955053%uint63) in
  let secrets1 := (
    (* secret key*)
    672363%uint63,
    (* vote *)
    true,
    (* randomness *)
    694283%uint63,
    55453%uint63,
    1145145%uint63,
    132313%uint63) in
  let secrets2 := (
    (* secret key*)
    91747%uint63,
    (* vote *)
    false,
    (* randomness *)
    422344%uint63,
    14224%uint63,
    11344%uint63,
    113443%uint63) in
  let secrets3 := (
    (* secret key*)
    354372%uint63,
    (* vote *)
    true,
    (* randomness *)
    435454%uint63,
    1242552%uint63,
    15653%uint63,
    1555%uint63) in
  let secrets4 := (
    (* secret key*)
    2355%uint63,
    (* vote *)
    false,
    (* randomness *)
    644%uint63,
    2451%uint63,
    1444%uint63,
    12554%uint63) in

  (* Registration params *)
  let mk_reg (n : nat) (s : T * bool * T * T * T * T) :=
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
  let reg_5 := mk_reg 5 secrets0 in
  let reg_6 := mk_reg 6 secrets1 in
  let reg_7 := mk_reg 7 secrets2 in
  let reg_8 := mk_reg 8 secrets3 in
  let reg_9 := mk_reg 9 secrets4 in
  let reg_10 := mk_reg 10 secrets0 in
  let reg_11 := mk_reg 11 secrets1 in
  let reg_12 := mk_reg 12 secrets2 in
  let reg_13 := mk_reg 13 secrets3 in
  let reg_14 := mk_reg 14 secrets4 in
  let reg_15 := mk_reg 15 secrets0 in
  let reg_16 := mk_reg 16 secrets1 in
  let reg_17 := mk_reg 17 secrets2 in
  let reg_18 := mk_reg 18 secrets3 in
  let reg_19 := mk_reg 19 secrets4 in

  (* Register *)
  do '(st1, _) <- ovn_receive dummy_chain dummy_ctx_user_0 st0 (Some (msg_register reg_0));
  do '(st2, _) <- ovn_receive dummy_chain dummy_ctx_user_1 st1 (Some (msg_register reg_1));
  do '(st3, _) <- ovn_receive dummy_chain dummy_ctx_user_2 st2 (Some (msg_register reg_2));
  do '(st4, _) <- ovn_receive dummy_chain dummy_ctx_user_3 st3 (Some (msg_register reg_3));
  do '(st5, _) <- ovn_receive dummy_chain dummy_ctx_user_4 st4 (Some (msg_register reg_4));
  do '(st6, _) <- ovn_receive dummy_chain dummy_ctx_user_5 st5 (Some (msg_register reg_5));
  do '(st7, _) <- ovn_receive dummy_chain dummy_ctx_user_6 st6 (Some (msg_register reg_6));
  do '(st8, _) <- ovn_receive dummy_chain dummy_ctx_user_7 st7 (Some (msg_register reg_7));
  do '(st9, _) <- ovn_receive dummy_chain dummy_ctx_user_8 st8 (Some (msg_register reg_8));
  do '(st10, _) <- ovn_receive dummy_chain dummy_ctx_user_9 st9 (Some (msg_register reg_9));
  do '(st11, _) <- ovn_receive dummy_chain dummy_ctx_user_10 st10 (Some (msg_register reg_10));
  do '(st12, _) <- ovn_receive dummy_chain dummy_ctx_user_11 st11 (Some (msg_register reg_11));
  do '(st13, _) <- ovn_receive dummy_chain dummy_ctx_user_12 st12 (Some (msg_register reg_12));
  do '(st14, _) <- ovn_receive dummy_chain dummy_ctx_user_13 st13 (Some (msg_register reg_13));
  do '(st15, _) <- ovn_receive dummy_chain dummy_ctx_user_14 st14 (Some (msg_register reg_14));
  do '(st16, _) <- ovn_receive dummy_chain dummy_ctx_user_15 st15 (Some (msg_register reg_15));
  do '(st17, _) <- ovn_receive dummy_chain dummy_ctx_user_16 st16 (Some (msg_register reg_16));
  do '(st18, _) <- ovn_receive dummy_chain dummy_ctx_user_17 st17 (Some (msg_register reg_17));
  do '(st19, _) <- ovn_receive dummy_chain dummy_ctx_user_18 st18 (Some (msg_register reg_18));
  do '(st20, _) <- ovn_receive dummy_chain dummy_ctx_user_19 st19 (Some (msg_register reg_19));

  (* Public keys *)
  let g_pow_xis := filter_some st20.(public_keys) in

  (* Commit params *)
  let mk_com (n : nat) (s : T * bool * T * T * T * T) :=
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
  let com_5 := mk_com 5 secrets0 in
  let com_6 := mk_com 6 secrets1 in
  let com_7 := mk_com 7 secrets2 in
  let com_8 := mk_com 8 secrets3 in
  let com_9 := mk_com 9 secrets4 in
  let com_10 := mk_com 10 secrets0 in
  let com_11 := mk_com 11 secrets1 in
  let com_12 := mk_com 12 secrets2 in
  let com_13 := mk_com 13 secrets3 in
  let com_14 := mk_com 14 secrets4 in
  let com_15 := mk_com 15 secrets0 in
  let com_16 := mk_com 16 secrets1 in
  let com_17 := mk_com 17 secrets2 in
  let com_18 := mk_com 18 secrets3 in
  let com_19 := mk_com 19 secrets4 in

  (* Commit *)
  do '(st21, _) <- ovn_receive dummy_chain dummy_ctx_user_0 st20 (Some (msg_commit com_0));
  do '(st22, _) <- ovn_receive dummy_chain dummy_ctx_user_1 st21 (Some (msg_commit com_1));
  do '(st23, _) <- ovn_receive dummy_chain dummy_ctx_user_2 st22 (Some (msg_commit com_2));
  do '(st24, _) <- ovn_receive dummy_chain dummy_ctx_user_3 st23 (Some (msg_commit com_3));
  do '(st25, _) <- ovn_receive dummy_chain dummy_ctx_user_4 st24 (Some (msg_commit com_4));
  do '(st26, _) <- ovn_receive dummy_chain dummy_ctx_user_5 st25 (Some (msg_commit com_5));
  do '(st27, _) <- ovn_receive dummy_chain dummy_ctx_user_6 st26 (Some (msg_commit com_6));
  do '(st28, _) <- ovn_receive dummy_chain dummy_ctx_user_7 st27 (Some (msg_commit com_7));
  do '(st29, _) <- ovn_receive dummy_chain dummy_ctx_user_8 st28 (Some (msg_commit com_8));
  do '(st30, _) <- ovn_receive dummy_chain dummy_ctx_user_9 st29 (Some (msg_commit com_9));
  do '(st31, _) <- ovn_receive dummy_chain dummy_ctx_user_10 st30 (Some (msg_commit com_10));
  do '(st32, _) <- ovn_receive dummy_chain dummy_ctx_user_11 st31 (Some (msg_commit com_11));
  do '(st33, _) <- ovn_receive dummy_chain dummy_ctx_user_12 st32 (Some (msg_commit com_12));
  do '(st34, _) <- ovn_receive dummy_chain dummy_ctx_user_13 st33 (Some (msg_commit com_13));
  do '(st35, _) <- ovn_receive dummy_chain dummy_ctx_user_14 st34 (Some (msg_commit com_14));
  do '(st36, _) <- ovn_receive dummy_chain dummy_ctx_user_15 st35 (Some (msg_commit com_15));
  do '(st37, _) <- ovn_receive dummy_chain dummy_ctx_user_16 st36 (Some (msg_commit com_16));
  do '(st38, _) <- ovn_receive dummy_chain dummy_ctx_user_17 st37 (Some (msg_commit com_17));
  do '(st39, _) <- ovn_receive dummy_chain dummy_ctx_user_18 st38 (Some (msg_commit com_18));
  do '(st40, _) <- ovn_receive dummy_chain dummy_ctx_user_19 st39 (Some (msg_commit com_19));

  (* Vote params *)
  let mk_vote (n : nat) (s : T * bool * T * T * T * T) :=
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
  let vote_5 := mk_vote 5 secrets0 in
  let vote_6 := mk_vote 6 secrets1 in
  let vote_7 := mk_vote 7 secrets2 in
  let vote_8 := mk_vote 8 secrets3 in
  let vote_9 := mk_vote 9 secrets4 in
  let vote_10 := mk_vote 10 secrets0 in
  let vote_11 := mk_vote 11 secrets1 in
  let vote_12 := mk_vote 12 secrets2 in
  let vote_13 := mk_vote 13 secrets3 in
  let vote_14 := mk_vote 14 secrets4 in
  let vote_15 := mk_vote 15 secrets0 in
  let vote_16 := mk_vote 16 secrets1 in
  let vote_17 := mk_vote 17 secrets2 in
  let vote_18 := mk_vote 18 secrets3 in
  let vote_19 := mk_vote 19 secrets4 in

  (* Vote *)
  do '(st41, _) <- ovn_receive dummy_chain dummy_ctx_user_0 st40 (Some (msg_vote vote_0));
  do '(st42, _) <- ovn_receive dummy_chain dummy_ctx_user_1 st41 (Some (msg_vote vote_1));
  do '(st43, _) <- ovn_receive dummy_chain dummy_ctx_user_2 st42 (Some (msg_vote vote_2));
  do '(st44, _) <- ovn_receive dummy_chain dummy_ctx_user_3 st43 (Some (msg_vote vote_3));
  do '(st45, _) <- ovn_receive dummy_chain dummy_ctx_user_4 st44 (Some (msg_vote vote_4));
  do '(st46, _) <- ovn_receive dummy_chain dummy_ctx_user_5 st45 (Some (msg_vote vote_5));
  do '(st47, _) <- ovn_receive dummy_chain dummy_ctx_user_6 st46 (Some (msg_vote vote_6));
  do '(st48, _) <- ovn_receive dummy_chain dummy_ctx_user_7 st47 (Some (msg_vote vote_7));
  do '(st49, _) <- ovn_receive dummy_chain dummy_ctx_user_8 st48 (Some (msg_vote vote_8));
  do '(st50, _) <- ovn_receive dummy_chain dummy_ctx_user_9 st49 (Some (msg_vote vote_9));
  do '(st51, _) <- ovn_receive dummy_chain dummy_ctx_user_10 st50 (Some (msg_vote vote_10));
  do '(st52, _) <- ovn_receive dummy_chain dummy_ctx_user_11 st51 (Some (msg_vote vote_11));
  do '(st53, _) <- ovn_receive dummy_chain dummy_ctx_user_12 st52 (Some (msg_vote vote_12));
  do '(st54, _) <- ovn_receive dummy_chain dummy_ctx_user_13 st53 (Some (msg_vote vote_13));
  do '(st55, _) <- ovn_receive dummy_chain dummy_ctx_user_14 st54 (Some (msg_vote vote_14));
  do '(st56, _) <- ovn_receive dummy_chain dummy_ctx_user_15 st55 (Some (msg_vote vote_15));
  do '(st57, _) <- ovn_receive dummy_chain dummy_ctx_user_16 st56 (Some (msg_vote vote_16));
  do '(st58, _) <- ovn_receive dummy_chain dummy_ctx_user_17 st57 (Some (msg_vote vote_17));
  do '(st59, _) <- ovn_receive dummy_chain dummy_ctx_user_18 st58 (Some (msg_vote vote_18));
  do '(st60, _) <- ovn_receive dummy_chain dummy_ctx_user_19 st59 (Some (msg_vote vote_19));

  (* Tally *)
  do '(st61, _) <- ovn_receive dummy_chain dummy_ctx_user_0 st60 (Some msg_tally);
  Ok st61.(tally).



Definition ovn_test_100 :=
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
  let dummy_ctx_user_5 := mk_ctx 5%N in
  let dummy_ctx_user_6 := mk_ctx 6%N in
  let dummy_ctx_user_7 := mk_ctx 7%N in
  let dummy_ctx_user_8 := mk_ctx 8%N in
  let dummy_ctx_user_9 := mk_ctx 9%N in
  let dummy_ctx_user_10 := mk_ctx 10%N in
  let dummy_ctx_user_11 := mk_ctx 11%N in
  let dummy_ctx_user_12 := mk_ctx 12%N in
  let dummy_ctx_user_13 := mk_ctx 13%N in
  let dummy_ctx_user_14 := mk_ctx 14%N in
  let dummy_ctx_user_15 := mk_ctx 15%N in
  let dummy_ctx_user_16 := mk_ctx 16%N in
  let dummy_ctx_user_17 := mk_ctx 17%N in
  let dummy_ctx_user_18 := mk_ctx 18%N in
  let dummy_ctx_user_19 := mk_ctx 19%N in
  let dummy_ctx_user_20 := mk_ctx 20%N in
  let dummy_ctx_user_21 := mk_ctx 21%N in
  let dummy_ctx_user_22 := mk_ctx 22%N in
  let dummy_ctx_user_23 := mk_ctx 23%N in
  let dummy_ctx_user_24 := mk_ctx 24%N in
  let dummy_ctx_user_25 := mk_ctx 25%N in
  let dummy_ctx_user_26 := mk_ctx 26%N in
  let dummy_ctx_user_27 := mk_ctx 27%N in
  let dummy_ctx_user_28 := mk_ctx 28%N in
  let dummy_ctx_user_29 := mk_ctx 29%N in
  let dummy_ctx_user_30 := mk_ctx 30%N in
  let dummy_ctx_user_31 := mk_ctx 31%N in
  let dummy_ctx_user_32 := mk_ctx 32%N in
  let dummy_ctx_user_33 := mk_ctx 33%N in
  let dummy_ctx_user_34 := mk_ctx 34%N in
  let dummy_ctx_user_35 := mk_ctx 35%N in
  let dummy_ctx_user_36 := mk_ctx 36%N in
  let dummy_ctx_user_37 := mk_ctx 37%N in
  let dummy_ctx_user_38 := mk_ctx 38%N in
  let dummy_ctx_user_39 := mk_ctx 39%N in
  let dummy_ctx_user_40 := mk_ctx 40%N in
  let dummy_ctx_user_41 := mk_ctx 41%N in
  let dummy_ctx_user_42 := mk_ctx 42%N in
  let dummy_ctx_user_43 := mk_ctx 43%N in
  let dummy_ctx_user_44 := mk_ctx 44%N in
  let dummy_ctx_user_45 := mk_ctx 45%N in
  let dummy_ctx_user_46 := mk_ctx 46%N in
  let dummy_ctx_user_47 := mk_ctx 47%N in
  let dummy_ctx_user_48 := mk_ctx 48%N in
  let dummy_ctx_user_49 := mk_ctx 49%N in
  let dummy_ctx_user_50 := mk_ctx 50%N in
  let dummy_ctx_user_51 := mk_ctx 51%N in
  let dummy_ctx_user_52 := mk_ctx 52%N in
  let dummy_ctx_user_53 := mk_ctx 53%N in
  let dummy_ctx_user_54 := mk_ctx 54%N in
  let dummy_ctx_user_55 := mk_ctx 55%N in
  let dummy_ctx_user_56 := mk_ctx 56%N in
  let dummy_ctx_user_57 := mk_ctx 57%N in
  let dummy_ctx_user_58 := mk_ctx 58%N in
  let dummy_ctx_user_59 := mk_ctx 59%N in
  let dummy_ctx_user_60 := mk_ctx 60%N in
  let dummy_ctx_user_61 := mk_ctx 61%N in
  let dummy_ctx_user_62 := mk_ctx 62%N in
  let dummy_ctx_user_63 := mk_ctx 63%N in
  let dummy_ctx_user_64 := mk_ctx 64%N in
  let dummy_ctx_user_65 := mk_ctx 65%N in
  let dummy_ctx_user_66 := mk_ctx 66%N in
  let dummy_ctx_user_67 := mk_ctx 67%N in
  let dummy_ctx_user_68 := mk_ctx 68%N in
  let dummy_ctx_user_69 := mk_ctx 69%N in
  let dummy_ctx_user_70 := mk_ctx 70%N in
  let dummy_ctx_user_71 := mk_ctx 71%N in
  let dummy_ctx_user_72 := mk_ctx 72%N in
  let dummy_ctx_user_73 := mk_ctx 73%N in
  let dummy_ctx_user_74 := mk_ctx 74%N in
  let dummy_ctx_user_75 := mk_ctx 75%N in
  let dummy_ctx_user_76 := mk_ctx 76%N in
  let dummy_ctx_user_77 := mk_ctx 77%N in
  let dummy_ctx_user_78 := mk_ctx 78%N in
  let dummy_ctx_user_79 := mk_ctx 79%N in
  let dummy_ctx_user_80 := mk_ctx 80%N in
  let dummy_ctx_user_81 := mk_ctx 81%N in
  let dummy_ctx_user_82 := mk_ctx 82%N in
  let dummy_ctx_user_83 := mk_ctx 83%N in
  let dummy_ctx_user_84 := mk_ctx 84%N in
  let dummy_ctx_user_85 := mk_ctx 85%N in
  let dummy_ctx_user_86 := mk_ctx 86%N in
  let dummy_ctx_user_87 := mk_ctx 87%N in
  let dummy_ctx_user_88 := mk_ctx 88%N in
  let dummy_ctx_user_89 := mk_ctx 89%N in
  let dummy_ctx_user_90 := mk_ctx 90%N in
  let dummy_ctx_user_91 := mk_ctx 91%N in
  let dummy_ctx_user_92 := mk_ctx 92%N in
  let dummy_ctx_user_93 := mk_ctx 93%N in
  let dummy_ctx_user_94 := mk_ctx 94%N in
  let dummy_ctx_user_95 := mk_ctx 95%N in
  let dummy_ctx_user_96 := mk_ctx 96%N in
  let dummy_ctx_user_97 := mk_ctx 97%N in
  let dummy_ctx_user_98 := mk_ctx 98%N in
  let dummy_ctx_user_99 := mk_ctx 99%N in

  (* Set up contract *)
  let setup := {|
    participants := 100;
    voter_addrs := [0; 1; 2; 3; 4; 5; 6; 7; 8; 9;
                    10; 11; 12; 13; 14; 15; 16; 17; 18; 19;
                    20; 21; 22; 23; 24; 25; 26; 27; 28; 29;
                    30; 31; 32; 33; 34; 35; 36; 37; 38; 39;
                    40; 41; 42; 43; 44; 45; 46; 47; 48; 49;
                    50; 51; 52; 53; 54; 55; 56; 57; 58; 59;
                    60; 61; 62; 63; 64; 65; 66; 67; 68; 69;
                    70; 71; 72; 73; 74; 75; 76; 77; 78; 79;
                    80; 81; 82; 83; 84; 85; 86; 87; 88; 89;
                    90; 91; 92; 93; 94; 95; 96; 97; 98; 99]%N;
  |} in
  do st0 <- ovn_init dummy_chain dummy_ctx_user_0 setup;

  (* Private data *)
  (* secret key, vote, randomness *)
  let secrets0 := (
    (* secret key*)
    305422%uint63,
    (* vote *)
    true,
    (* randomness *)
    3243652%uint63,
    45722%uint63,
    19%uint63,
    955053%uint63) in
  let secrets1 := (
    (* secret key*)
    672363%uint63,
    (* vote *)
    true,
    (* randomness *)
    694283%uint63,
    55453%uint63,
    1145145%uint63,
    132313%uint63) in
  let secrets2 := (
    (* secret key*)
    91747%uint63,
    (* vote *)
    false,
    (* randomness *)
    422344%uint63,
    14224%uint63,
    11344%uint63,
    113443%uint63) in
  let secrets3 := (
    (* secret key*)
    354372%uint63,
    (* vote *)
    true,
    (* randomness *)
    435454%uint63,
    1242552%uint63,
    15653%uint63,
    1555%uint63) in
  let secrets4 := (
    (* secret key*)
    2355%uint63,
    (* vote *)
    false,
    (* randomness *)
    644%uint63,
    2451%uint63,
    1444%uint63,
    12554%uint63) in

  (* Registration params *)
  let mk_reg (n : nat) (s : T * bool * T * T * T * T) :=
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
  let reg_5 := mk_reg 5 secrets0 in
  let reg_6 := mk_reg 6 secrets1 in
  let reg_7 := mk_reg 7 secrets2 in
  let reg_8 := mk_reg 8 secrets3 in
  let reg_9 := mk_reg 9 secrets4 in
  let reg_10 := mk_reg 10 secrets0 in
  let reg_11 := mk_reg 11 secrets1 in
  let reg_12 := mk_reg 12 secrets2 in
  let reg_13 := mk_reg 13 secrets3 in
  let reg_14 := mk_reg 14 secrets4 in
  let reg_15 := mk_reg 15 secrets0 in
  let reg_16 := mk_reg 16 secrets1 in
  let reg_17 := mk_reg 17 secrets2 in
  let reg_18 := mk_reg 18 secrets3 in
  let reg_19 := mk_reg 19 secrets4 in
  let reg_20 := mk_reg 20 secrets0 in
  let reg_21 := mk_reg 21 secrets1 in
  let reg_22 := mk_reg 22 secrets2 in
  let reg_23 := mk_reg 23 secrets3 in
  let reg_24 := mk_reg 24 secrets4 in
  let reg_25 := mk_reg 25 secrets0 in
  let reg_26 := mk_reg 26 secrets1 in
  let reg_27 := mk_reg 27 secrets2 in
  let reg_28 := mk_reg 28 secrets3 in
  let reg_29 := mk_reg 29 secrets4 in
  let reg_30 := mk_reg 30 secrets0 in
  let reg_31 := mk_reg 31 secrets1 in
  let reg_32 := mk_reg 32 secrets2 in
  let reg_33 := mk_reg 33 secrets3 in
  let reg_34 := mk_reg 34 secrets4 in
  let reg_35 := mk_reg 35 secrets0 in
  let reg_36 := mk_reg 36 secrets1 in
  let reg_37 := mk_reg 37 secrets2 in
  let reg_38 := mk_reg 38 secrets3 in
  let reg_39 := mk_reg 39 secrets4 in
  let reg_40 := mk_reg 40 secrets0 in
  let reg_41 := mk_reg 41 secrets1 in
  let reg_42 := mk_reg 42 secrets2 in
  let reg_43 := mk_reg 43 secrets3 in
  let reg_44 := mk_reg 44 secrets4 in
  let reg_45 := mk_reg 45 secrets0 in
  let reg_46 := mk_reg 46 secrets1 in
  let reg_47 := mk_reg 47 secrets2 in
  let reg_48 := mk_reg 48 secrets3 in
  let reg_49 := mk_reg 49 secrets4 in
  let reg_50 := mk_reg 50 secrets0 in
  let reg_51 := mk_reg 51 secrets1 in
  let reg_52 := mk_reg 52 secrets2 in
  let reg_53 := mk_reg 53 secrets3 in
  let reg_54 := mk_reg 54 secrets4 in
  let reg_55 := mk_reg 55 secrets0 in
  let reg_56 := mk_reg 56 secrets1 in
  let reg_57 := mk_reg 57 secrets2 in
  let reg_58 := mk_reg 58 secrets3 in
  let reg_59 := mk_reg 59 secrets4 in
  let reg_60 := mk_reg 60 secrets0 in
  let reg_61 := mk_reg 61 secrets1 in
  let reg_62 := mk_reg 62 secrets2 in
  let reg_63 := mk_reg 63 secrets3 in
  let reg_64 := mk_reg 64 secrets4 in
  let reg_65 := mk_reg 65 secrets0 in
  let reg_66 := mk_reg 66 secrets1 in
  let reg_67 := mk_reg 67 secrets2 in
  let reg_68 := mk_reg 68 secrets3 in
  let reg_69 := mk_reg 69 secrets4 in
  let reg_70 := mk_reg 70 secrets0 in
  let reg_71 := mk_reg 71 secrets1 in
  let reg_72 := mk_reg 72 secrets2 in
  let reg_73 := mk_reg 73 secrets3 in
  let reg_74 := mk_reg 74 secrets4 in
  let reg_75 := mk_reg 75 secrets0 in
  let reg_76 := mk_reg 76 secrets1 in
  let reg_77 := mk_reg 77 secrets2 in
  let reg_78 := mk_reg 78 secrets3 in
  let reg_79 := mk_reg 79 secrets4 in
  let reg_80 := mk_reg 80 secrets0 in
  let reg_81 := mk_reg 81 secrets1 in
  let reg_82 := mk_reg 82 secrets2 in
  let reg_83 := mk_reg 83 secrets3 in
  let reg_84 := mk_reg 84 secrets4 in
  let reg_85 := mk_reg 85 secrets0 in
  let reg_86 := mk_reg 86 secrets1 in
  let reg_87 := mk_reg 87 secrets2 in
  let reg_88 := mk_reg 88 secrets3 in
  let reg_89 := mk_reg 89 secrets4 in
  let reg_90 := mk_reg 90 secrets0 in
  let reg_91 := mk_reg 91 secrets1 in
  let reg_92 := mk_reg 92 secrets2 in
  let reg_93 := mk_reg 93 secrets3 in
  let reg_94 := mk_reg 94 secrets4 in
  let reg_95 := mk_reg 95 secrets0 in
  let reg_96 := mk_reg 96 secrets1 in
  let reg_97 := mk_reg 97 secrets2 in
  let reg_98 := mk_reg 98 secrets3 in
  let reg_99 := mk_reg 99 secrets4 in

  (* Register *)
  do '(st1, _) <- ovn_receive dummy_chain dummy_ctx_user_0 st0 (Some (msg_register reg_0));
  do '(st2, _) <- ovn_receive dummy_chain dummy_ctx_user_1 st1 (Some (msg_register reg_1));
  do '(st3, _) <- ovn_receive dummy_chain dummy_ctx_user_2 st2 (Some (msg_register reg_2));
  do '(st4, _) <- ovn_receive dummy_chain dummy_ctx_user_3 st3 (Some (msg_register reg_3));
  do '(st5, _) <- ovn_receive dummy_chain dummy_ctx_user_4 st4 (Some (msg_register reg_4));
  do '(st6, _) <- ovn_receive dummy_chain dummy_ctx_user_5 st5 (Some (msg_register reg_5));
  do '(st7, _) <- ovn_receive dummy_chain dummy_ctx_user_6 st6 (Some (msg_register reg_6));
  do '(st8, _) <- ovn_receive dummy_chain dummy_ctx_user_7 st7 (Some (msg_register reg_7));
  do '(st9, _) <- ovn_receive dummy_chain dummy_ctx_user_8 st8 (Some (msg_register reg_8));
  do '(st10, _) <- ovn_receive dummy_chain dummy_ctx_user_9 st9 (Some (msg_register reg_9));
  do '(st11, _) <- ovn_receive dummy_chain dummy_ctx_user_10 st10 (Some (msg_register reg_10));
  do '(st12, _) <- ovn_receive dummy_chain dummy_ctx_user_11 st11 (Some (msg_register reg_11));
  do '(st13, _) <- ovn_receive dummy_chain dummy_ctx_user_12 st12 (Some (msg_register reg_12));
  do '(st14, _) <- ovn_receive dummy_chain dummy_ctx_user_13 st13 (Some (msg_register reg_13));
  do '(st15, _) <- ovn_receive dummy_chain dummy_ctx_user_14 st14 (Some (msg_register reg_14));
  do '(st16, _) <- ovn_receive dummy_chain dummy_ctx_user_15 st15 (Some (msg_register reg_15));
  do '(st17, _) <- ovn_receive dummy_chain dummy_ctx_user_16 st16 (Some (msg_register reg_16));
  do '(st18, _) <- ovn_receive dummy_chain dummy_ctx_user_17 st17 (Some (msg_register reg_17));
  do '(st19, _) <- ovn_receive dummy_chain dummy_ctx_user_18 st18 (Some (msg_register reg_18));
  do '(st20, _) <- ovn_receive dummy_chain dummy_ctx_user_19 st19 (Some (msg_register reg_19));
  do '(st21, _) <- ovn_receive dummy_chain dummy_ctx_user_20 st20 (Some (msg_register reg_20));
  do '(st22, _) <- ovn_receive dummy_chain dummy_ctx_user_21 st21 (Some (msg_register reg_21));
  do '(st23, _) <- ovn_receive dummy_chain dummy_ctx_user_22 st22 (Some (msg_register reg_22));
  do '(st24, _) <- ovn_receive dummy_chain dummy_ctx_user_23 st23 (Some (msg_register reg_23));
  do '(st25, _) <- ovn_receive dummy_chain dummy_ctx_user_24 st24 (Some (msg_register reg_24));
  do '(st26, _) <- ovn_receive dummy_chain dummy_ctx_user_25 st25 (Some (msg_register reg_25));
  do '(st27, _) <- ovn_receive dummy_chain dummy_ctx_user_26 st26 (Some (msg_register reg_26));
  do '(st28, _) <- ovn_receive dummy_chain dummy_ctx_user_27 st27 (Some (msg_register reg_27));
  do '(st29, _) <- ovn_receive dummy_chain dummy_ctx_user_28 st28 (Some (msg_register reg_28));
  do '(st30, _) <- ovn_receive dummy_chain dummy_ctx_user_29 st29 (Some (msg_register reg_29));
  do '(st31, _) <- ovn_receive dummy_chain dummy_ctx_user_30 st30 (Some (msg_register reg_30));
  do '(st32, _) <- ovn_receive dummy_chain dummy_ctx_user_31 st31 (Some (msg_register reg_31));
  do '(st33, _) <- ovn_receive dummy_chain dummy_ctx_user_32 st32 (Some (msg_register reg_32));
  do '(st34, _) <- ovn_receive dummy_chain dummy_ctx_user_33 st33 (Some (msg_register reg_33));
  do '(st35, _) <- ovn_receive dummy_chain dummy_ctx_user_34 st34 (Some (msg_register reg_34));
  do '(st36, _) <- ovn_receive dummy_chain dummy_ctx_user_35 st35 (Some (msg_register reg_35));
  do '(st37, _) <- ovn_receive dummy_chain dummy_ctx_user_36 st36 (Some (msg_register reg_36));
  do '(st38, _) <- ovn_receive dummy_chain dummy_ctx_user_37 st37 (Some (msg_register reg_37));
  do '(st39, _) <- ovn_receive dummy_chain dummy_ctx_user_38 st38 (Some (msg_register reg_38));
  do '(st40, _) <- ovn_receive dummy_chain dummy_ctx_user_39 st39 (Some (msg_register reg_39));
  do '(st41, _) <- ovn_receive dummy_chain dummy_ctx_user_40 st40 (Some (msg_register reg_40));
  do '(st42, _) <- ovn_receive dummy_chain dummy_ctx_user_41 st41 (Some (msg_register reg_41));
  do '(st43, _) <- ovn_receive dummy_chain dummy_ctx_user_42 st42 (Some (msg_register reg_42));
  do '(st44, _) <- ovn_receive dummy_chain dummy_ctx_user_43 st43 (Some (msg_register reg_43));
  do '(st45, _) <- ovn_receive dummy_chain dummy_ctx_user_44 st44 (Some (msg_register reg_44));
  do '(st46, _) <- ovn_receive dummy_chain dummy_ctx_user_45 st45 (Some (msg_register reg_45));
  do '(st47, _) <- ovn_receive dummy_chain dummy_ctx_user_46 st46 (Some (msg_register reg_46));
  do '(st48, _) <- ovn_receive dummy_chain dummy_ctx_user_47 st47 (Some (msg_register reg_47));
  do '(st49, _) <- ovn_receive dummy_chain dummy_ctx_user_48 st48 (Some (msg_register reg_48));
  do '(st50, _) <- ovn_receive dummy_chain dummy_ctx_user_49 st49 (Some (msg_register reg_49));
  do '(st51, _) <- ovn_receive dummy_chain dummy_ctx_user_50 st50 (Some (msg_register reg_50));
  do '(st52, _) <- ovn_receive dummy_chain dummy_ctx_user_51 st51 (Some (msg_register reg_51));
  do '(st53, _) <- ovn_receive dummy_chain dummy_ctx_user_52 st52 (Some (msg_register reg_52));
  do '(st54, _) <- ovn_receive dummy_chain dummy_ctx_user_53 st53 (Some (msg_register reg_53));
  do '(st55, _) <- ovn_receive dummy_chain dummy_ctx_user_54 st54 (Some (msg_register reg_54));
  do '(st56, _) <- ovn_receive dummy_chain dummy_ctx_user_55 st55 (Some (msg_register reg_55));
  do '(st57, _) <- ovn_receive dummy_chain dummy_ctx_user_56 st56 (Some (msg_register reg_56));
  do '(st58, _) <- ovn_receive dummy_chain dummy_ctx_user_57 st57 (Some (msg_register reg_57));
  do '(st59, _) <- ovn_receive dummy_chain dummy_ctx_user_58 st58 (Some (msg_register reg_58));
  do '(st60, _) <- ovn_receive dummy_chain dummy_ctx_user_59 st59 (Some (msg_register reg_59));
  do '(st61, _) <- ovn_receive dummy_chain dummy_ctx_user_60 st60 (Some (msg_register reg_60));
  do '(st62, _) <- ovn_receive dummy_chain dummy_ctx_user_61 st61 (Some (msg_register reg_61));
  do '(st63, _) <- ovn_receive dummy_chain dummy_ctx_user_62 st62 (Some (msg_register reg_62));
  do '(st64, _) <- ovn_receive dummy_chain dummy_ctx_user_63 st63 (Some (msg_register reg_63));
  do '(st65, _) <- ovn_receive dummy_chain dummy_ctx_user_64 st64 (Some (msg_register reg_64));
  do '(st66, _) <- ovn_receive dummy_chain dummy_ctx_user_65 st65 (Some (msg_register reg_65));
  do '(st67, _) <- ovn_receive dummy_chain dummy_ctx_user_66 st66 (Some (msg_register reg_66));
  do '(st68, _) <- ovn_receive dummy_chain dummy_ctx_user_67 st67 (Some (msg_register reg_67));
  do '(st69, _) <- ovn_receive dummy_chain dummy_ctx_user_68 st68 (Some (msg_register reg_68));
  do '(st70, _) <- ovn_receive dummy_chain dummy_ctx_user_69 st69 (Some (msg_register reg_69));
  do '(st71, _) <- ovn_receive dummy_chain dummy_ctx_user_70 st70 (Some (msg_register reg_70));
  do '(st72, _) <- ovn_receive dummy_chain dummy_ctx_user_71 st71 (Some (msg_register reg_71));
  do '(st73, _) <- ovn_receive dummy_chain dummy_ctx_user_72 st72 (Some (msg_register reg_72));
  do '(st74, _) <- ovn_receive dummy_chain dummy_ctx_user_73 st73 (Some (msg_register reg_73));
  do '(st75, _) <- ovn_receive dummy_chain dummy_ctx_user_74 st74 (Some (msg_register reg_74));
  do '(st76, _) <- ovn_receive dummy_chain dummy_ctx_user_75 st75 (Some (msg_register reg_75));
  do '(st77, _) <- ovn_receive dummy_chain dummy_ctx_user_76 st76 (Some (msg_register reg_76));
  do '(st78, _) <- ovn_receive dummy_chain dummy_ctx_user_77 st77 (Some (msg_register reg_77));
  do '(st79, _) <- ovn_receive dummy_chain dummy_ctx_user_78 st78 (Some (msg_register reg_78));
  do '(st80, _) <- ovn_receive dummy_chain dummy_ctx_user_79 st79 (Some (msg_register reg_79));
  do '(st81, _) <- ovn_receive dummy_chain dummy_ctx_user_80 st80 (Some (msg_register reg_80));
  do '(st82, _) <- ovn_receive dummy_chain dummy_ctx_user_81 st81 (Some (msg_register reg_81));
  do '(st83, _) <- ovn_receive dummy_chain dummy_ctx_user_82 st82 (Some (msg_register reg_82));
  do '(st84, _) <- ovn_receive dummy_chain dummy_ctx_user_83 st83 (Some (msg_register reg_83));
  do '(st85, _) <- ovn_receive dummy_chain dummy_ctx_user_84 st84 (Some (msg_register reg_84));
  do '(st86, _) <- ovn_receive dummy_chain dummy_ctx_user_85 st85 (Some (msg_register reg_85));
  do '(st87, _) <- ovn_receive dummy_chain dummy_ctx_user_86 st86 (Some (msg_register reg_86));
  do '(st88, _) <- ovn_receive dummy_chain dummy_ctx_user_87 st87 (Some (msg_register reg_87));
  do '(st89, _) <- ovn_receive dummy_chain dummy_ctx_user_88 st88 (Some (msg_register reg_88));
  do '(st90, _) <- ovn_receive dummy_chain dummy_ctx_user_89 st89 (Some (msg_register reg_89));
  do '(st91, _) <- ovn_receive dummy_chain dummy_ctx_user_90 st90 (Some (msg_register reg_90));
  do '(st92, _) <- ovn_receive dummy_chain dummy_ctx_user_91 st91 (Some (msg_register reg_91));
  do '(st93, _) <- ovn_receive dummy_chain dummy_ctx_user_92 st92 (Some (msg_register reg_92));
  do '(st94, _) <- ovn_receive dummy_chain dummy_ctx_user_93 st93 (Some (msg_register reg_93));
  do '(st95, _) <- ovn_receive dummy_chain dummy_ctx_user_94 st94 (Some (msg_register reg_94));
  do '(st96, _) <- ovn_receive dummy_chain dummy_ctx_user_95 st95 (Some (msg_register reg_95));
  do '(st97, _) <- ovn_receive dummy_chain dummy_ctx_user_96 st96 (Some (msg_register reg_96));
  do '(st98, _) <- ovn_receive dummy_chain dummy_ctx_user_97 st97 (Some (msg_register reg_97));
  do '(st99, _) <- ovn_receive dummy_chain dummy_ctx_user_98 st98 (Some (msg_register reg_98));
  do '(st100, _) <- ovn_receive dummy_chain dummy_ctx_user_99 st99 (Some (msg_register reg_99));

  (* Public keys *)
  let g_pow_xis := filter_some st100.(public_keys) in

  (* Commit params *)
  let mk_com (n : nat) (s : T * bool * T * T * T * T) :=
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
  let com_5 := mk_com 5 secrets0 in
  let com_6 := mk_com 6 secrets1 in
  let com_7 := mk_com 7 secrets2 in
  let com_8 := mk_com 8 secrets3 in
  let com_9 := mk_com 9 secrets4 in
  let com_10 := mk_com 10 secrets0 in
  let com_11 := mk_com 11 secrets1 in
  let com_12 := mk_com 12 secrets2 in
  let com_13 := mk_com 13 secrets3 in
  let com_14 := mk_com 14 secrets4 in
  let com_15 := mk_com 15 secrets0 in
  let com_16 := mk_com 16 secrets1 in
  let com_17 := mk_com 17 secrets2 in
  let com_18 := mk_com 18 secrets3 in
  let com_19 := mk_com 19 secrets4 in
  let com_20 := mk_com 20 secrets0 in
  let com_21 := mk_com 21 secrets1 in
  let com_22 := mk_com 22 secrets2 in
  let com_23 := mk_com 23 secrets3 in
  let com_24 := mk_com 24 secrets4 in
  let com_25 := mk_com 25 secrets0 in
  let com_26 := mk_com 26 secrets1 in
  let com_27 := mk_com 27 secrets2 in
  let com_28 := mk_com 28 secrets3 in
  let com_29 := mk_com 29 secrets4 in
  let com_30 := mk_com 30 secrets0 in
  let com_31 := mk_com 31 secrets1 in
  let com_32 := mk_com 32 secrets2 in
  let com_33 := mk_com 33 secrets3 in
  let com_34 := mk_com 34 secrets4 in
  let com_35 := mk_com 35 secrets0 in
  let com_36 := mk_com 36 secrets1 in
  let com_37 := mk_com 37 secrets2 in
  let com_38 := mk_com 38 secrets3 in
  let com_39 := mk_com 39 secrets4 in
  let com_40 := mk_com 40 secrets0 in
  let com_41 := mk_com 41 secrets1 in
  let com_42 := mk_com 42 secrets2 in
  let com_43 := mk_com 43 secrets3 in
  let com_44 := mk_com 44 secrets4 in
  let com_45 := mk_com 45 secrets0 in
  let com_46 := mk_com 46 secrets1 in
  let com_47 := mk_com 47 secrets2 in
  let com_48 := mk_com 48 secrets3 in
  let com_49 := mk_com 49 secrets4 in
  let com_50 := mk_com 50 secrets0 in
  let com_51 := mk_com 51 secrets1 in
  let com_52 := mk_com 52 secrets2 in
  let com_53 := mk_com 53 secrets3 in
  let com_54 := mk_com 54 secrets4 in
  let com_55 := mk_com 55 secrets0 in
  let com_56 := mk_com 56 secrets1 in
  let com_57 := mk_com 57 secrets2 in
  let com_58 := mk_com 58 secrets3 in
  let com_59 := mk_com 59 secrets4 in
  let com_60 := mk_com 60 secrets0 in
  let com_61 := mk_com 61 secrets1 in
  let com_62 := mk_com 62 secrets2 in
  let com_63 := mk_com 63 secrets3 in
  let com_64 := mk_com 64 secrets4 in
  let com_65 := mk_com 65 secrets0 in
  let com_66 := mk_com 66 secrets1 in
  let com_67 := mk_com 67 secrets2 in
  let com_68 := mk_com 68 secrets3 in
  let com_69 := mk_com 69 secrets4 in
  let com_70 := mk_com 70 secrets0 in
  let com_71 := mk_com 71 secrets1 in
  let com_72 := mk_com 72 secrets2 in
  let com_73 := mk_com 73 secrets3 in
  let com_74 := mk_com 74 secrets4 in
  let com_75 := mk_com 75 secrets0 in
  let com_76 := mk_com 76 secrets1 in
  let com_77 := mk_com 77 secrets2 in
  let com_78 := mk_com 78 secrets3 in
  let com_79 := mk_com 79 secrets4 in
  let com_80 := mk_com 80 secrets0 in
  let com_81 := mk_com 81 secrets1 in
  let com_82 := mk_com 82 secrets2 in
  let com_83 := mk_com 83 secrets3 in
  let com_84 := mk_com 84 secrets4 in
  let com_85 := mk_com 85 secrets0 in
  let com_86 := mk_com 86 secrets1 in
  let com_87 := mk_com 87 secrets2 in
  let com_88 := mk_com 88 secrets3 in
  let com_89 := mk_com 89 secrets4 in
  let com_90 := mk_com 90 secrets0 in
  let com_91 := mk_com 91 secrets1 in
  let com_92 := mk_com 92 secrets2 in
  let com_93 := mk_com 93 secrets3 in
  let com_94 := mk_com 94 secrets4 in
  let com_95 := mk_com 95 secrets0 in
  let com_96 := mk_com 96 secrets1 in
  let com_97 := mk_com 97 secrets2 in
  let com_98 := mk_com 98 secrets3 in
  let com_99 := mk_com 99 secrets4 in

  (* Commit *)
  do '(st101, _) <- ovn_receive dummy_chain dummy_ctx_user_0 st100 (Some (msg_commit com_0));
  do '(st102, _) <- ovn_receive dummy_chain dummy_ctx_user_1 st101 (Some (msg_commit com_1));
  do '(st103, _) <- ovn_receive dummy_chain dummy_ctx_user_2 st102 (Some (msg_commit com_2));
  do '(st104, _) <- ovn_receive dummy_chain dummy_ctx_user_3 st103 (Some (msg_commit com_3));
  do '(st105, _) <- ovn_receive dummy_chain dummy_ctx_user_4 st104 (Some (msg_commit com_4));
  do '(st106, _) <- ovn_receive dummy_chain dummy_ctx_user_5 st105 (Some (msg_commit com_5));
  do '(st107, _) <- ovn_receive dummy_chain dummy_ctx_user_6 st106 (Some (msg_commit com_6));
  do '(st108, _) <- ovn_receive dummy_chain dummy_ctx_user_7 st107 (Some (msg_commit com_7));
  do '(st109, _) <- ovn_receive dummy_chain dummy_ctx_user_8 st108 (Some (msg_commit com_8));
  do '(st110, _) <- ovn_receive dummy_chain dummy_ctx_user_9 st109 (Some (msg_commit com_9));
  do '(st111, _) <- ovn_receive dummy_chain dummy_ctx_user_10 st110 (Some (msg_commit com_10));
  do '(st112, _) <- ovn_receive dummy_chain dummy_ctx_user_11 st111 (Some (msg_commit com_11));
  do '(st113, _) <- ovn_receive dummy_chain dummy_ctx_user_12 st112 (Some (msg_commit com_12));
  do '(st114, _) <- ovn_receive dummy_chain dummy_ctx_user_13 st113 (Some (msg_commit com_13));
  do '(st115, _) <- ovn_receive dummy_chain dummy_ctx_user_14 st114 (Some (msg_commit com_14));
  do '(st116, _) <- ovn_receive dummy_chain dummy_ctx_user_15 st115 (Some (msg_commit com_15));
  do '(st117, _) <- ovn_receive dummy_chain dummy_ctx_user_16 st116 (Some (msg_commit com_16));
  do '(st118, _) <- ovn_receive dummy_chain dummy_ctx_user_17 st117 (Some (msg_commit com_17));
  do '(st119, _) <- ovn_receive dummy_chain dummy_ctx_user_18 st118 (Some (msg_commit com_18));
  do '(st120, _) <- ovn_receive dummy_chain dummy_ctx_user_19 st119 (Some (msg_commit com_19));
  do '(st121, _) <- ovn_receive dummy_chain dummy_ctx_user_20 st120 (Some (msg_commit com_20));
  do '(st122, _) <- ovn_receive dummy_chain dummy_ctx_user_21 st121 (Some (msg_commit com_21));
  do '(st123, _) <- ovn_receive dummy_chain dummy_ctx_user_22 st122 (Some (msg_commit com_22));
  do '(st124, _) <- ovn_receive dummy_chain dummy_ctx_user_23 st123 (Some (msg_commit com_23));
  do '(st125, _) <- ovn_receive dummy_chain dummy_ctx_user_24 st124 (Some (msg_commit com_24));
  do '(st126, _) <- ovn_receive dummy_chain dummy_ctx_user_25 st125 (Some (msg_commit com_25));
  do '(st127, _) <- ovn_receive dummy_chain dummy_ctx_user_26 st126 (Some (msg_commit com_26));
  do '(st128, _) <- ovn_receive dummy_chain dummy_ctx_user_27 st127 (Some (msg_commit com_27));
  do '(st129, _) <- ovn_receive dummy_chain dummy_ctx_user_28 st128 (Some (msg_commit com_28));
  do '(st130, _) <- ovn_receive dummy_chain dummy_ctx_user_29 st129 (Some (msg_commit com_29));
  do '(st131, _) <- ovn_receive dummy_chain dummy_ctx_user_30 st130 (Some (msg_commit com_30));
  do '(st132, _) <- ovn_receive dummy_chain dummy_ctx_user_31 st131 (Some (msg_commit com_31));
  do '(st133, _) <- ovn_receive dummy_chain dummy_ctx_user_32 st132 (Some (msg_commit com_32));
  do '(st134, _) <- ovn_receive dummy_chain dummy_ctx_user_33 st133 (Some (msg_commit com_33));
  do '(st135, _) <- ovn_receive dummy_chain dummy_ctx_user_34 st134 (Some (msg_commit com_34));
  do '(st136, _) <- ovn_receive dummy_chain dummy_ctx_user_35 st135 (Some (msg_commit com_35));
  do '(st137, _) <- ovn_receive dummy_chain dummy_ctx_user_36 st136 (Some (msg_commit com_36));
  do '(st138, _) <- ovn_receive dummy_chain dummy_ctx_user_37 st137 (Some (msg_commit com_37));
  do '(st139, _) <- ovn_receive dummy_chain dummy_ctx_user_38 st138 (Some (msg_commit com_38));
  do '(st140, _) <- ovn_receive dummy_chain dummy_ctx_user_39 st139 (Some (msg_commit com_39));
  do '(st141, _) <- ovn_receive dummy_chain dummy_ctx_user_40 st140 (Some (msg_commit com_40));
  do '(st142, _) <- ovn_receive dummy_chain dummy_ctx_user_41 st141 (Some (msg_commit com_41));
  do '(st143, _) <- ovn_receive dummy_chain dummy_ctx_user_42 st142 (Some (msg_commit com_42));
  do '(st144, _) <- ovn_receive dummy_chain dummy_ctx_user_43 st143 (Some (msg_commit com_43));
  do '(st145, _) <- ovn_receive dummy_chain dummy_ctx_user_44 st144 (Some (msg_commit com_44));
  do '(st146, _) <- ovn_receive dummy_chain dummy_ctx_user_45 st145 (Some (msg_commit com_45));
  do '(st147, _) <- ovn_receive dummy_chain dummy_ctx_user_46 st146 (Some (msg_commit com_46));
  do '(st148, _) <- ovn_receive dummy_chain dummy_ctx_user_47 st147 (Some (msg_commit com_47));
  do '(st149, _) <- ovn_receive dummy_chain dummy_ctx_user_48 st148 (Some (msg_commit com_48));
  do '(st150, _) <- ovn_receive dummy_chain dummy_ctx_user_49 st149 (Some (msg_commit com_49));
  do '(st151, _) <- ovn_receive dummy_chain dummy_ctx_user_50 st150 (Some (msg_commit com_50));
  do '(st152, _) <- ovn_receive dummy_chain dummy_ctx_user_51 st151 (Some (msg_commit com_51));
  do '(st153, _) <- ovn_receive dummy_chain dummy_ctx_user_52 st152 (Some (msg_commit com_52));
  do '(st154, _) <- ovn_receive dummy_chain dummy_ctx_user_53 st153 (Some (msg_commit com_53));
  do '(st155, _) <- ovn_receive dummy_chain dummy_ctx_user_54 st154 (Some (msg_commit com_54));
  do '(st156, _) <- ovn_receive dummy_chain dummy_ctx_user_55 st155 (Some (msg_commit com_55));
  do '(st157, _) <- ovn_receive dummy_chain dummy_ctx_user_56 st156 (Some (msg_commit com_56));
  do '(st158, _) <- ovn_receive dummy_chain dummy_ctx_user_57 st157 (Some (msg_commit com_57));
  do '(st159, _) <- ovn_receive dummy_chain dummy_ctx_user_58 st158 (Some (msg_commit com_58));
  do '(st160, _) <- ovn_receive dummy_chain dummy_ctx_user_59 st159 (Some (msg_commit com_59));
  do '(st161, _) <- ovn_receive dummy_chain dummy_ctx_user_60 st160 (Some (msg_commit com_60));
  do '(st162, _) <- ovn_receive dummy_chain dummy_ctx_user_61 st161 (Some (msg_commit com_61));
  do '(st163, _) <- ovn_receive dummy_chain dummy_ctx_user_62 st162 (Some (msg_commit com_62));
  do '(st164, _) <- ovn_receive dummy_chain dummy_ctx_user_63 st163 (Some (msg_commit com_63));
  do '(st165, _) <- ovn_receive dummy_chain dummy_ctx_user_64 st164 (Some (msg_commit com_64));
  do '(st166, _) <- ovn_receive dummy_chain dummy_ctx_user_65 st165 (Some (msg_commit com_65));
  do '(st167, _) <- ovn_receive dummy_chain dummy_ctx_user_66 st166 (Some (msg_commit com_66));
  do '(st168, _) <- ovn_receive dummy_chain dummy_ctx_user_67 st167 (Some (msg_commit com_67));
  do '(st169, _) <- ovn_receive dummy_chain dummy_ctx_user_68 st168 (Some (msg_commit com_68));
  do '(st170, _) <- ovn_receive dummy_chain dummy_ctx_user_69 st169 (Some (msg_commit com_69));
  do '(st171, _) <- ovn_receive dummy_chain dummy_ctx_user_70 st170 (Some (msg_commit com_70));
  do '(st172, _) <- ovn_receive dummy_chain dummy_ctx_user_71 st171 (Some (msg_commit com_71));
  do '(st173, _) <- ovn_receive dummy_chain dummy_ctx_user_72 st172 (Some (msg_commit com_72));
  do '(st174, _) <- ovn_receive dummy_chain dummy_ctx_user_73 st173 (Some (msg_commit com_73));
  do '(st175, _) <- ovn_receive dummy_chain dummy_ctx_user_74 st174 (Some (msg_commit com_74));
  do '(st176, _) <- ovn_receive dummy_chain dummy_ctx_user_75 st175 (Some (msg_commit com_75));
  do '(st177, _) <- ovn_receive dummy_chain dummy_ctx_user_76 st176 (Some (msg_commit com_76));
  do '(st178, _) <- ovn_receive dummy_chain dummy_ctx_user_77 st177 (Some (msg_commit com_77));
  do '(st179, _) <- ovn_receive dummy_chain dummy_ctx_user_78 st178 (Some (msg_commit com_78));
  do '(st180, _) <- ovn_receive dummy_chain dummy_ctx_user_79 st179 (Some (msg_commit com_79));
  do '(st181, _) <- ovn_receive dummy_chain dummy_ctx_user_80 st180 (Some (msg_commit com_80));
  do '(st182, _) <- ovn_receive dummy_chain dummy_ctx_user_81 st181 (Some (msg_commit com_81));
  do '(st183, _) <- ovn_receive dummy_chain dummy_ctx_user_82 st182 (Some (msg_commit com_82));
  do '(st184, _) <- ovn_receive dummy_chain dummy_ctx_user_83 st183 (Some (msg_commit com_83));
  do '(st185, _) <- ovn_receive dummy_chain dummy_ctx_user_84 st184 (Some (msg_commit com_84));
  do '(st186, _) <- ovn_receive dummy_chain dummy_ctx_user_85 st185 (Some (msg_commit com_85));
  do '(st187, _) <- ovn_receive dummy_chain dummy_ctx_user_86 st186 (Some (msg_commit com_86));
  do '(st188, _) <- ovn_receive dummy_chain dummy_ctx_user_87 st187 (Some (msg_commit com_87));
  do '(st189, _) <- ovn_receive dummy_chain dummy_ctx_user_88 st188 (Some (msg_commit com_88));
  do '(st190, _) <- ovn_receive dummy_chain dummy_ctx_user_89 st189 (Some (msg_commit com_89));
  do '(st191, _) <- ovn_receive dummy_chain dummy_ctx_user_90 st190 (Some (msg_commit com_90));
  do '(st192, _) <- ovn_receive dummy_chain dummy_ctx_user_91 st191 (Some (msg_commit com_91));
  do '(st193, _) <- ovn_receive dummy_chain dummy_ctx_user_92 st192 (Some (msg_commit com_92));
  do '(st194, _) <- ovn_receive dummy_chain dummy_ctx_user_93 st193 (Some (msg_commit com_93));
  do '(st195, _) <- ovn_receive dummy_chain dummy_ctx_user_94 st194 (Some (msg_commit com_94));
  do '(st196, _) <- ovn_receive dummy_chain dummy_ctx_user_95 st195 (Some (msg_commit com_95));
  do '(st197, _) <- ovn_receive dummy_chain dummy_ctx_user_96 st196 (Some (msg_commit com_96));
  do '(st198, _) <- ovn_receive dummy_chain dummy_ctx_user_97 st197 (Some (msg_commit com_97));
  do '(st199, _) <- ovn_receive dummy_chain dummy_ctx_user_98 st198 (Some (msg_commit com_98));
  do '(st200, _) <- ovn_receive dummy_chain dummy_ctx_user_99 st199 (Some (msg_commit com_99));

  (* Vote params *)
  let mk_vote (n : nat) (s : T * bool * T * T * T * T) :=
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
  let vote_5 := mk_vote 5 secrets0 in
  let vote_6 := mk_vote 6 secrets1 in
  let vote_7 := mk_vote 7 secrets2 in
  let vote_8 := mk_vote 8 secrets3 in
  let vote_9 := mk_vote 9 secrets4 in
  let vote_10 := mk_vote 10 secrets0 in
  let vote_11 := mk_vote 11 secrets1 in
  let vote_12 := mk_vote 12 secrets2 in
  let vote_13 := mk_vote 13 secrets3 in
  let vote_14 := mk_vote 14 secrets4 in
  let vote_15 := mk_vote 15 secrets0 in
  let vote_16 := mk_vote 16 secrets1 in
  let vote_17 := mk_vote 17 secrets2 in
  let vote_18 := mk_vote 18 secrets3 in
  let vote_19 := mk_vote 19 secrets4 in
  let vote_20 := mk_vote 20 secrets0 in
  let vote_21 := mk_vote 21 secrets1 in
  let vote_22 := mk_vote 22 secrets2 in
  let vote_23 := mk_vote 23 secrets3 in
  let vote_24 := mk_vote 24 secrets4 in
  let vote_25 := mk_vote 25 secrets0 in
  let vote_26 := mk_vote 26 secrets1 in
  let vote_27 := mk_vote 27 secrets2 in
  let vote_28 := mk_vote 28 secrets3 in
  let vote_29 := mk_vote 29 secrets4 in
  let vote_30 := mk_vote 30 secrets0 in
  let vote_31 := mk_vote 31 secrets1 in
  let vote_32 := mk_vote 32 secrets2 in
  let vote_33 := mk_vote 33 secrets3 in
  let vote_34 := mk_vote 34 secrets4 in
  let vote_35 := mk_vote 35 secrets0 in
  let vote_36 := mk_vote 36 secrets1 in
  let vote_37 := mk_vote 37 secrets2 in
  let vote_38 := mk_vote 38 secrets3 in
  let vote_39 := mk_vote 39 secrets4 in
  let vote_40 := mk_vote 40 secrets0 in
  let vote_41 := mk_vote 41 secrets1 in
  let vote_42 := mk_vote 42 secrets2 in
  let vote_43 := mk_vote 43 secrets3 in
  let vote_44 := mk_vote 44 secrets4 in
  let vote_45 := mk_vote 45 secrets0 in
  let vote_46 := mk_vote 46 secrets1 in
  let vote_47 := mk_vote 47 secrets2 in
  let vote_48 := mk_vote 48 secrets3 in
  let vote_49 := mk_vote 49 secrets4 in
  let vote_50 := mk_vote 50 secrets0 in
  let vote_51 := mk_vote 51 secrets1 in
  let vote_52 := mk_vote 52 secrets2 in
  let vote_53 := mk_vote 53 secrets3 in
  let vote_54 := mk_vote 54 secrets4 in
  let vote_55 := mk_vote 55 secrets0 in
  let vote_56 := mk_vote 56 secrets1 in
  let vote_57 := mk_vote 57 secrets2 in
  let vote_58 := mk_vote 58 secrets3 in
  let vote_59 := mk_vote 59 secrets4 in
  let vote_60 := mk_vote 60 secrets0 in
  let vote_61 := mk_vote 61 secrets1 in
  let vote_62 := mk_vote 62 secrets2 in
  let vote_63 := mk_vote 63 secrets3 in
  let vote_64 := mk_vote 64 secrets4 in
  let vote_65 := mk_vote 65 secrets0 in
  let vote_66 := mk_vote 66 secrets1 in
  let vote_67 := mk_vote 67 secrets2 in
  let vote_68 := mk_vote 68 secrets3 in
  let vote_69 := mk_vote 69 secrets4 in
  let vote_70 := mk_vote 70 secrets0 in
  let vote_71 := mk_vote 71 secrets1 in
  let vote_72 := mk_vote 72 secrets2 in
  let vote_73 := mk_vote 73 secrets3 in
  let vote_74 := mk_vote 74 secrets4 in
  let vote_75 := mk_vote 75 secrets0 in
  let vote_76 := mk_vote 76 secrets1 in
  let vote_77 := mk_vote 77 secrets2 in
  let vote_78 := mk_vote 78 secrets3 in
  let vote_79 := mk_vote 79 secrets4 in
  let vote_80 := mk_vote 80 secrets0 in
  let vote_81 := mk_vote 81 secrets1 in
  let vote_82 := mk_vote 82 secrets2 in
  let vote_83 := mk_vote 83 secrets3 in
  let vote_84 := mk_vote 84 secrets4 in
  let vote_85 := mk_vote 85 secrets0 in
  let vote_86 := mk_vote 86 secrets1 in
  let vote_87 := mk_vote 87 secrets2 in
  let vote_88 := mk_vote 88 secrets3 in
  let vote_89 := mk_vote 89 secrets4 in
  let vote_90 := mk_vote 90 secrets0 in
  let vote_91 := mk_vote 91 secrets1 in
  let vote_92 := mk_vote 92 secrets2 in
  let vote_93 := mk_vote 93 secrets3 in
  let vote_94 := mk_vote 94 secrets4 in
  let vote_95 := mk_vote 95 secrets0 in
  let vote_96 := mk_vote 96 secrets1 in
  let vote_97 := mk_vote 97 secrets2 in
  let vote_98 := mk_vote 98 secrets3 in
  let vote_99 := mk_vote 99 secrets4 in

  (* Vote *)
  do '(st201, _) <- ovn_receive dummy_chain dummy_ctx_user_0 st200 (Some (msg_vote vote_0));
  do '(st202, _) <- ovn_receive dummy_chain dummy_ctx_user_1 st201 (Some (msg_vote vote_1));
  do '(st203, _) <- ovn_receive dummy_chain dummy_ctx_user_2 st202 (Some (msg_vote vote_2));
  do '(st204, _) <- ovn_receive dummy_chain dummy_ctx_user_3 st203 (Some (msg_vote vote_3));
  do '(st205, _) <- ovn_receive dummy_chain dummy_ctx_user_4 st204 (Some (msg_vote vote_4));
  do '(st206, _) <- ovn_receive dummy_chain dummy_ctx_user_5 st205 (Some (msg_vote vote_5));
  do '(st207, _) <- ovn_receive dummy_chain dummy_ctx_user_6 st206 (Some (msg_vote vote_6));
  do '(st208, _) <- ovn_receive dummy_chain dummy_ctx_user_7 st207 (Some (msg_vote vote_7));
  do '(st209, _) <- ovn_receive dummy_chain dummy_ctx_user_8 st208 (Some (msg_vote vote_8));
  do '(st210, _) <- ovn_receive dummy_chain dummy_ctx_user_9 st209 (Some (msg_vote vote_9));
  do '(st211, _) <- ovn_receive dummy_chain dummy_ctx_user_10 st210 (Some (msg_vote vote_10));
  do '(st212, _) <- ovn_receive dummy_chain dummy_ctx_user_11 st211 (Some (msg_vote vote_11));
  do '(st213, _) <- ovn_receive dummy_chain dummy_ctx_user_12 st212 (Some (msg_vote vote_12));
  do '(st214, _) <- ovn_receive dummy_chain dummy_ctx_user_13 st213 (Some (msg_vote vote_13));
  do '(st215, _) <- ovn_receive dummy_chain dummy_ctx_user_14 st214 (Some (msg_vote vote_14));
  do '(st216, _) <- ovn_receive dummy_chain dummy_ctx_user_15 st215 (Some (msg_vote vote_15));
  do '(st217, _) <- ovn_receive dummy_chain dummy_ctx_user_16 st216 (Some (msg_vote vote_16));
  do '(st218, _) <- ovn_receive dummy_chain dummy_ctx_user_17 st217 (Some (msg_vote vote_17));
  do '(st219, _) <- ovn_receive dummy_chain dummy_ctx_user_18 st218 (Some (msg_vote vote_18));
  do '(st220, _) <- ovn_receive dummy_chain dummy_ctx_user_19 st219 (Some (msg_vote vote_19));
  do '(st221, _) <- ovn_receive dummy_chain dummy_ctx_user_20 st220 (Some (msg_vote vote_20));
  do '(st222, _) <- ovn_receive dummy_chain dummy_ctx_user_21 st221 (Some (msg_vote vote_21));
  do '(st223, _) <- ovn_receive dummy_chain dummy_ctx_user_22 st222 (Some (msg_vote vote_22));
  do '(st224, _) <- ovn_receive dummy_chain dummy_ctx_user_23 st223 (Some (msg_vote vote_23));
  do '(st225, _) <- ovn_receive dummy_chain dummy_ctx_user_24 st224 (Some (msg_vote vote_24));
  do '(st226, _) <- ovn_receive dummy_chain dummy_ctx_user_25 st225 (Some (msg_vote vote_25));
  do '(st227, _) <- ovn_receive dummy_chain dummy_ctx_user_26 st226 (Some (msg_vote vote_26));
  do '(st228, _) <- ovn_receive dummy_chain dummy_ctx_user_27 st227 (Some (msg_vote vote_27));
  do '(st229, _) <- ovn_receive dummy_chain dummy_ctx_user_28 st228 (Some (msg_vote vote_28));
  do '(st230, _) <- ovn_receive dummy_chain dummy_ctx_user_29 st229 (Some (msg_vote vote_29));
  do '(st231, _) <- ovn_receive dummy_chain dummy_ctx_user_30 st230 (Some (msg_vote vote_30));
  do '(st232, _) <- ovn_receive dummy_chain dummy_ctx_user_31 st231 (Some (msg_vote vote_31));
  do '(st233, _) <- ovn_receive dummy_chain dummy_ctx_user_32 st232 (Some (msg_vote vote_32));
  do '(st234, _) <- ovn_receive dummy_chain dummy_ctx_user_33 st233 (Some (msg_vote vote_33));
  do '(st235, _) <- ovn_receive dummy_chain dummy_ctx_user_34 st234 (Some (msg_vote vote_34));
  do '(st236, _) <- ovn_receive dummy_chain dummy_ctx_user_35 st235 (Some (msg_vote vote_35));
  do '(st237, _) <- ovn_receive dummy_chain dummy_ctx_user_36 st236 (Some (msg_vote vote_36));
  do '(st238, _) <- ovn_receive dummy_chain dummy_ctx_user_37 st237 (Some (msg_vote vote_37));
  do '(st239, _) <- ovn_receive dummy_chain dummy_ctx_user_38 st238 (Some (msg_vote vote_38));
  do '(st240, _) <- ovn_receive dummy_chain dummy_ctx_user_39 st239 (Some (msg_vote vote_39));
  do '(st241, _) <- ovn_receive dummy_chain dummy_ctx_user_40 st240 (Some (msg_vote vote_40));
  do '(st242, _) <- ovn_receive dummy_chain dummy_ctx_user_41 st241 (Some (msg_vote vote_41));
  do '(st243, _) <- ovn_receive dummy_chain dummy_ctx_user_42 st242 (Some (msg_vote vote_42));
  do '(st244, _) <- ovn_receive dummy_chain dummy_ctx_user_43 st243 (Some (msg_vote vote_43));
  do '(st245, _) <- ovn_receive dummy_chain dummy_ctx_user_44 st244 (Some (msg_vote vote_44));
  do '(st246, _) <- ovn_receive dummy_chain dummy_ctx_user_45 st245 (Some (msg_vote vote_45));
  do '(st247, _) <- ovn_receive dummy_chain dummy_ctx_user_46 st246 (Some (msg_vote vote_46));
  do '(st248, _) <- ovn_receive dummy_chain dummy_ctx_user_47 st247 (Some (msg_vote vote_47));
  do '(st249, _) <- ovn_receive dummy_chain dummy_ctx_user_48 st248 (Some (msg_vote vote_48));
  do '(st250, _) <- ovn_receive dummy_chain dummy_ctx_user_49 st249 (Some (msg_vote vote_49));
  do '(st251, _) <- ovn_receive dummy_chain dummy_ctx_user_50 st250 (Some (msg_vote vote_50));
  do '(st252, _) <- ovn_receive dummy_chain dummy_ctx_user_51 st251 (Some (msg_vote vote_51));
  do '(st253, _) <- ovn_receive dummy_chain dummy_ctx_user_52 st252 (Some (msg_vote vote_52));
  do '(st254, _) <- ovn_receive dummy_chain dummy_ctx_user_53 st253 (Some (msg_vote vote_53));
  do '(st255, _) <- ovn_receive dummy_chain dummy_ctx_user_54 st254 (Some (msg_vote vote_54));
  do '(st256, _) <- ovn_receive dummy_chain dummy_ctx_user_55 st255 (Some (msg_vote vote_55));
  do '(st257, _) <- ovn_receive dummy_chain dummy_ctx_user_56 st256 (Some (msg_vote vote_56));
  do '(st258, _) <- ovn_receive dummy_chain dummy_ctx_user_57 st257 (Some (msg_vote vote_57));
  do '(st259, _) <- ovn_receive dummy_chain dummy_ctx_user_58 st258 (Some (msg_vote vote_58));
  do '(st260, _) <- ovn_receive dummy_chain dummy_ctx_user_59 st259 (Some (msg_vote vote_59));
  do '(st261, _) <- ovn_receive dummy_chain dummy_ctx_user_60 st260 (Some (msg_vote vote_60));
  do '(st262, _) <- ovn_receive dummy_chain dummy_ctx_user_61 st261 (Some (msg_vote vote_61));
  do '(st263, _) <- ovn_receive dummy_chain dummy_ctx_user_62 st262 (Some (msg_vote vote_62));
  do '(st264, _) <- ovn_receive dummy_chain dummy_ctx_user_63 st263 (Some (msg_vote vote_63));
  do '(st265, _) <- ovn_receive dummy_chain dummy_ctx_user_64 st264 (Some (msg_vote vote_64));
  do '(st266, _) <- ovn_receive dummy_chain dummy_ctx_user_65 st265 (Some (msg_vote vote_65));
  do '(st267, _) <- ovn_receive dummy_chain dummy_ctx_user_66 st266 (Some (msg_vote vote_66));
  do '(st268, _) <- ovn_receive dummy_chain dummy_ctx_user_67 st267 (Some (msg_vote vote_67));
  do '(st269, _) <- ovn_receive dummy_chain dummy_ctx_user_68 st268 (Some (msg_vote vote_68));
  do '(st270, _) <- ovn_receive dummy_chain dummy_ctx_user_69 st269 (Some (msg_vote vote_69));
  do '(st271, _) <- ovn_receive dummy_chain dummy_ctx_user_70 st270 (Some (msg_vote vote_70));
  do '(st272, _) <- ovn_receive dummy_chain dummy_ctx_user_71 st271 (Some (msg_vote vote_71));
  do '(st273, _) <- ovn_receive dummy_chain dummy_ctx_user_72 st272 (Some (msg_vote vote_72));
  do '(st274, _) <- ovn_receive dummy_chain dummy_ctx_user_73 st273 (Some (msg_vote vote_73));
  do '(st275, _) <- ovn_receive dummy_chain dummy_ctx_user_74 st274 (Some (msg_vote vote_74));
  do '(st276, _) <- ovn_receive dummy_chain dummy_ctx_user_75 st275 (Some (msg_vote vote_75));
  do '(st277, _) <- ovn_receive dummy_chain dummy_ctx_user_76 st276 (Some (msg_vote vote_76));
  do '(st278, _) <- ovn_receive dummy_chain dummy_ctx_user_77 st277 (Some (msg_vote vote_77));
  do '(st279, _) <- ovn_receive dummy_chain dummy_ctx_user_78 st278 (Some (msg_vote vote_78));
  do '(st280, _) <- ovn_receive dummy_chain dummy_ctx_user_79 st279 (Some (msg_vote vote_79));
  do '(st281, _) <- ovn_receive dummy_chain dummy_ctx_user_80 st280 (Some (msg_vote vote_80));
  do '(st282, _) <- ovn_receive dummy_chain dummy_ctx_user_81 st281 (Some (msg_vote vote_81));
  do '(st283, _) <- ovn_receive dummy_chain dummy_ctx_user_82 st282 (Some (msg_vote vote_82));
  do '(st284, _) <- ovn_receive dummy_chain dummy_ctx_user_83 st283 (Some (msg_vote vote_83));
  do '(st285, _) <- ovn_receive dummy_chain dummy_ctx_user_84 st284 (Some (msg_vote vote_84));
  do '(st286, _) <- ovn_receive dummy_chain dummy_ctx_user_85 st285 (Some (msg_vote vote_85));
  do '(st287, _) <- ovn_receive dummy_chain dummy_ctx_user_86 st286 (Some (msg_vote vote_86));
  do '(st288, _) <- ovn_receive dummy_chain dummy_ctx_user_87 st287 (Some (msg_vote vote_87));
  do '(st289, _) <- ovn_receive dummy_chain dummy_ctx_user_88 st288 (Some (msg_vote vote_88));
  do '(st290, _) <- ovn_receive dummy_chain dummy_ctx_user_89 st289 (Some (msg_vote vote_89));
  do '(st291, _) <- ovn_receive dummy_chain dummy_ctx_user_90 st290 (Some (msg_vote vote_90));
  do '(st292, _) <- ovn_receive dummy_chain dummy_ctx_user_91 st291 (Some (msg_vote vote_91));
  do '(st293, _) <- ovn_receive dummy_chain dummy_ctx_user_92 st292 (Some (msg_vote vote_92));
  do '(st294, _) <- ovn_receive dummy_chain dummy_ctx_user_93 st293 (Some (msg_vote vote_93));
  do '(st295, _) <- ovn_receive dummy_chain dummy_ctx_user_94 st294 (Some (msg_vote vote_94));
  do '(st296, _) <- ovn_receive dummy_chain dummy_ctx_user_95 st295 (Some (msg_vote vote_95));
  do '(st297, _) <- ovn_receive dummy_chain dummy_ctx_user_96 st296 (Some (msg_vote vote_96));
  do '(st298, _) <- ovn_receive dummy_chain dummy_ctx_user_97 st297 (Some (msg_vote vote_97));
  do '(st299, _) <- ovn_receive dummy_chain dummy_ctx_user_98 st298 (Some (msg_vote vote_98));
  do '(st300, _) <- ovn_receive dummy_chain dummy_ctx_user_99 st299 (Some (msg_vote vote_99));

  (* Tally *)
  do '(st301, _) <- ovn_receive dummy_chain dummy_ctx_user_0 st300 (Some msg_tally);
  Ok st301.(tally).





Set Warnings "-primitive-turned-into-axiom".
From CertiCoq.Plugin Require Import CertiCoq.

CertiCoq Compile Wasm ovn_test_5.
CertiCoq Compile Wasm ovn_test_10.
CertiCoq Compile Wasm ovn_test_20.
CertiCoq Compile Wasm ovn_test_100.
