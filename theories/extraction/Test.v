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





Set Warnings "-primitive-turned-into-axiom".
From CertiCoq.Plugin Require Import CertiCoq.

CertiCoq Compile Wasm ovn_test_5.
CertiCoq Compile Wasm ovn_test_10.
CertiCoq Compile Wasm ovn_test_20.
