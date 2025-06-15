From mathcomp Require Import all_ssreflect fingroup.fingroup ssreflect.
Set Warnings "-notation-overridden,-ambiguous-paths".
From SSProve.Crypt Require Import choice_type Package Prelude.
Import PackageNotation.
From extructures Require Import ord fset.
From mathcomp Require Import word_ssrZ word.
(* From Jasmin Require Import word. *)

From Coq Require Import ZArith.
From Coq Require Import Strings.String.
Import List.ListNotations.
Open Scope list_scope.
Open Scope Z_scope.
Open Scope bool_scope.

From Hacspec Require Import ChoiceEquality.
From Hacspec Require Import LocationUtility.
From Hacspec Require Import Hacspec_Lib_Comparable.
From Hacspec Require Import Hacspec_Lib_Pre.
From Hacspec Require Import Hacspec_Lib.

Open Scope hacspec_scope.
Import choice.Choice.Exports.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".
Set Primitive Projections.

Obligation Tactic := (* try timeout 8 *) solve_ssprove_obligations.

From OVN Require Import Hacspec_ovn.
From OVN Require Import Hacspec_helpers.

From HB Require Import structures.

From SSProve.Crypt Require Import jasmin_word.

From OVN Require Import Schnorr SigmaProtocol.

From SSProve.Relational Require Import OrderEnrichedCategory GenericRulesSimple.

Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp Require Import all_ssreflect all_algebra reals distr realsum
  fingroup.fingroup solvable.cyclic prime ssrnat ssreflect ssrfun ssrbool ssrnum
  eqtype choice seq.
Set Warnings "notation-overridden,ambiguous-paths".

From SSProve.Mon Require Import SPropBase.

From SSProve.Crypt Require Import Axioms ChoiceAsOrd SubDistr Couplings
  UniformDistrLemmas FreeProbProg Theta_dens RulesStateProb UniformStateProb
  pkg_core_definition choice_type pkg_composition pkg_rhl Package Prelude.

From Coq Require Import Utf8.
From extructures Require Import ord fset fmap.

From Equations Require Import Equations.
Require Equations.Prop.DepElim.

Set Equations With UIP.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".
Set Primitive Projections.

Local Open Scope ring_scope.
Import GroupScope GRing.Theory.

Import PackageNotation.

From OVN Require Import Hacspec_ovn.
From OVN Require Import Hacspec_helpers.
From OVN Require Import Hacspec_ovn_group_and_field.
From OVN Require Import Hacspec_ovn_sigma_setup.
From OVN Require Import Hacspec_ovn_schnorr.
From OVN Require Import Hacspec_ovn_or.

Module OVN_proof (HOP : HacspecOvnParameter) (HOGaFP : HacspecOvnGroupAndFieldParameter HOP) (HOGaFE : HacspecOvnGroupAndFieldExtra HOP HOGaFP) (HGPA : HacspecGroupParamAxiom HOP HOGaFP HOGaFE).
  Module Schnorr_ZKP := OVN_schnorr_proof HOP HOGaFP HOGaFE HGPA.
  Module OR_ZKP := OVN_or_proof HOP HOGaFP HOGaFE HGPA.

  Include HGPA.

  From OVN Require Import OVN.

  Module OVN_GroupParam <: OVN.GroupParam.

    Definition n : nat := is_pure HOP.n.
    Lemma n_pos : Positive n. Proof. apply HOP.n_pos. Qed.

    Include HGPA.GaFP.HacspecGroup.
  End OVN_GroupParam.

  Module OVN_Param <: OVNParam.
    Definition N : nat := is_pure HOP.n.
    Lemma N_pos : Positive N. Proof. apply HOP.n_pos. Qed.
  End OVN_Param.

  Module OVN_proofs := OVN OVN_GroupParam OVN_Param.

  Module OVN_or <: OVN_proofs.CDSParams.
    Include OR_ZKP.proof_args.MyParam.
    Definition State : finType := 'unit.
    Instance State_pos : Positive #|State| := eq_ind_r [eta Positive] (erefl : Positive 1) card_unit.
  End OVN_or.

  Module OVN_old_proofs := OVN_proofs.OVN OVN_or OR_ZKP.proof_args.MyAlg.

  Import HOGaFE.GroupAndField.OVN.
  (* Import HOGaFE.GroupAndField. *)
  (* Import HOGaFE. *)
  Import HGPA.GaFP.
  Import HGPA.GaFP.HacspecGroup.
  From SSProve.Crypt Require Import choice_type Package Prelude.
  Import PackageNotation.

  Lemma cyclic_group_to_exponent :
    forall x,
    ∃ i : nat, x = g ^+ i /\ i < #[g].
  Proof.
    intros.

    assert (x \in <[g]>).
    {
      unfold HacspecGroup.gT in x.
      unfold HacspecGroup.g.
      setoid_rewrite <- HOGaFE.v_G_g_gen.
      simpl.
      apply in_setT.
    }

    (* destruct (ssrbool.elimT (cycleP HacspecGroup.g x) H). *)
    pose (cyclePmin H).
    destruct s ; subst.
    exists x0.
    easy.
  Qed.

  Definition full_protocol_transcript : choice_type :=
    (* Round 1 *)
    nseq t_SchnorrZKPCommit OVN_Param.N (* schnorr_zkp *) ×
    nseq v_G OVN_Param.N × (* ddh_pk *)  (* g^{x_i} hiding x_i by DDH *)

    (* Round 2 *)
    nseq v_G OVN_Param.N × (* commit *)

    (* Round 3 *)
    nseq t_OrZKPCommit OVN_Param.N × (* or *)
    nseq v_G OVN_Param.N (* vote *)

    (* Round 4 - Check values *).

  Definition protocol_input : choice_type :=
    (* Round 1 *)
    'nat × (* i *)

    (* Round 2 *)
    nseq v_G OVN_Param.N × (* commit *)

    (* Round 3 *)
    nseq t_OrZKPCommit OVN_Param.N × (* or *)
    nseq v_G OVN_Param.N (* vote *)

    (* Round 4 - Check values *).

  Ltac split_advantage O :=
    try apply (AdvantageE_le_0 _ _ _ ) ;
    eapply Order.le_trans ; [ apply Advantage_triangle with (R := O) | ] ;
    replace (AdvantageE _ _ _) with (@GRing.zero R) ; [
        replace (AdvantageE _ _ _) with (@GRing.zero R) ; [ rewrite add0r ; easy | symmetry ] |
        symmetry ] ; revgoals.


  Lemma nseq_n_pos :
    forall A n,
      Positive n ->
      match
      nseq_ A n
    with
    | 'unit => True
    | chMap (chFin n0) C =>
        match pos n0 with
        | 0%N => False
        | _.+1 => C = A
        end
    | chMap 'nat C | chList C => C = A
    | _ => False
         end.
  Proof.
    intros.
    simpl.
    destruct n0.
    - done.
    - reflexivity.
  Defined.

  (** Should be hax library definitions *)

  Lemma array_update_eq : forall {A : choice_type} (b5 : both (nseq_ A (from_uint_size (is_pure n)))) b (i : int32),
      (Z.to_nat (unsigned i) < (from_uint_size (is_pure n)))%coq_nat ->
      is_pure (array_index
                 (update_at_usize b5 (ret_both i) b)
                 (ret_both i)) =
        is_pure b.
  Proof.
    intros A.
    intros.

    unfold update_at_usize at 1.
    unfold lift3_both at 1.
    unfold array_index at 1.
    unfold lift2_both at 1 2.
    simpl.

    simpl in *.
    epose proof (wrepr_unsigned (is_pure HOP.n)).
    epose HOP.n_pos.
    rewrite <- (Z2Nat.id (unsigned (is_pure n))) in H0.
    2: apply wunsigned_range.
    rewrite <- H0 in p ; clear H0.

    destruct (Z.to_nat (unsigned (is_pure n))).
    1: discriminate.

    clear p.


    unfold Hacspec_Lib_Pre.array_upd.
    unfold array_upd_clause_1.
    unfold array_upd_clause_1_clause_1.

    unfold Hacspec_Lib_Pre.array_index at 1.

    destruct lt_dec.
    {
      unfold array_index_clause_2.
      destruct le_lt_dec ; [ easy | ].
      rewrite setmE.
      epose (proj1 (ord_ext
                      (Z.to_nat (unsigned i))
                      (Z.to_nat (unsigned i))) erefl).
      apply (ssrbool.introT eqP) in e.
      rewrite e.
      simpl.
      reflexivity.

      Unshelve.
      2,3: apply /ltP ; apply H.
    }
    {
      contradiction.
    }
  Qed.

  Lemma array_update_neq : forall {A : choice_type} (b5 : both (nseq_ A (from_uint_size (is_pure n)))) b (i x : int32),
      (Z.to_nat (unsigned i) < (from_uint_size (is_pure n)))%coq_nat ->
      (Z.to_nat (unsigned x) <> Z.to_nat (unsigned i)) ->
      is_pure (array_index
                 (update_at_usize b5 (ret_both i) b)
                 (ret_both x)) =
        is_pure (array_index b5 (ret_both x)).
  Proof.
    intros A.
    intros.

    unfold update_at_usize at 1.
    unfold lift3_both at 1.
    unfold array_index at 1 2.
    unfold lift2_both at 1 2 3.
    simpl.

    simpl in *.
    epose proof (wrepr_unsigned (is_pure HOP.n)).
    epose HOP.n_pos.
    rewrite <- (Z2Nat.id (unsigned (is_pure n))) in H1.
    2: apply wunsigned_range.
    rewrite <- H1 in p ; clear H1.

    destruct (Z.to_nat (unsigned (is_pure n))).
    1: discriminate.

    clear p.


    unfold Hacspec_Lib_Pre.array_upd.
    unfold array_upd_clause_1.
    unfold array_upd_clause_1_clause_1.

    unfold Hacspec_Lib_Pre.array_index at 1 2.

    destruct lt_dec.
    {
      unfold array_index_clause_2.
      destruct le_lt_dec ; [ easy | ].
      {
        rewrite setmE.

        replace (_ == _) with false.
        {
          reflexivity.
        }
        symmetry.
        apply /eqP.
        red ; intros.
        apply ord_ext in H1.
        apply H0.
        easy.
      }
    }
    {
      contradiction.
    }
  Qed.

  Lemma n_seq_array_or_seq_simpl : forall {A : choice_type} {n : nat} (b5 : both (nseq_ A n.+1)),
      (n_seq_array_or_seq b5 (nseq_n_pos A n.+1 erefl)) = b5.
  Proof.
    intros.
    unfold nseq_n_pos.
    cbn.
    assert (positive_eqP {| pos := n0.+1; cond_pos := erefl |} _ (eqxx _) = erefl).
    {
      easy.
    }
    rewrite H.
    reflexivity.
  Qed.

  Lemma n_seq_array_or_seq_simpl_pos : forall {A : choice_type} {n : nat} (b5 : both (nseq_ A n)),
      (Positive n)%R ->
      match n as k return both (nseq_ A k) -> _ with
      | 0%nat => fun _ => False
      | S n0 => fun b5 => n_seq_array_or_seq b5 (nseq_n_pos A n0.+1 erefl) = b5
      end b5.
  Proof.
    intros.
    destruct n0.
    - discriminate.
    - apply (n_seq_array_or_seq_simpl b5).
  Defined.

  Lemma pos_pos : Positive (from_uint_size (is_pure n)).
  Proof. apply n_pos. Qed.

  Lemma compute_g_pow_yi_update_eq : forall (b5 : both (nseq_ v_G (from_uint_size (is_pure n)))) b (i : int32),
      (Z.to_nat (unsigned i) < from_uint_size (is_pure n))%coq_nat ->
      is_pure (compute_g_pow_yi
                 (ret_both i)
                 (update_at_usize b5 (ret_both i) b)) =
        is_pure (compute_g_pow_yi
                   (ret_both i)
                   b5
          ).
  Proof.
    intros.

    (* unfold update_at_usize at 1. *)
    (* unfold lift3_both at 1. *)
    unfold compute_g_pow_yi at 1 2.
    (* unfold lift2_both at 1 2. *)
    simpl.

    repeat unfold let_both at 1.
    set (fun _ => _).
    set (fun _ => _).
    set (fun _ => _).

    assert (forall (x : both int32), Z.to_nat (unsigned (is_pure x)) ≠ Z.to_nat (unsigned i) -> forall y, is_pure (y0 x y) = is_pure (y1 x y)).
    {
      intros.
      subst y0 y1.
      simpl.
      rewrite !(hacspec_function_guarantees2 f_prod y2).
      f_equal.
      f_equal.
      f_equal.
      f_equal.

      rewrite hacspec_function_guarantees.
      rewrite array_update_neq ; easy.
    }

    (* TODO: fold stuff *)
    simpl.

    assert (
        forall {A B} {L : both (chList B)} {f g : both B -> both A -> both A} {a : both A},
        (forall (x : both _) y, is_pure x \in is_pure L -> is_pure (f x y) = is_pure (g x y)) ->
        is_pure (foldi_both_list L f a) =
              is_pure (foldi_both_list L g a)).
    {
      intros.
      unfold foldi_both_list at 1 2.
      simpl.

      destruct L as [[L_pure L_state] [L_valid_code L_valid_both] L_eq].
      simpl in *.
      clear -H1.

      rewrite !(hacspec_function_guarantees _ (lift_both _)).
      simpl.
      rewrite <- !(hacspec_function_guarantees).

      generalize dependent a.
      induction L_pure ; intros.
      - reflexivity.
      - simpl.
        rewrite IHL_pure.
        {
          rewrite !(hacspec_function_guarantees _ (lift_both _)).
          rewrite H1.
          {
            simpl.
            reflexivity.
          }
          simpl.
          rewrite in_cons.
          rewrite eqxx.
          reflexivity.
        }
        {
          intros.
          apply H1.
          rewrite in_cons.
          rewrite H ; apply /orP ; right ; reflexivity.
        }
    }

    rewrite !(hacspec_function_guarantees2 _ (foldi_both_list _ _ _)).
    erewrite !(H1 _ _ _ y0 y1) ; [ reflexivity | intros .. ].
    1:{
      eapply H0 ; red ; intros ; clear -H H2 H3.
      subst y.
      unfold Build_Range , prod_both at 1 in H2 ; simpl in H2.

      apply f_equal with (f := Z.of_nat) in H3.
      rewrite !Z2Nat.id in H3 ; [ | apply wunsigned_range.. ].
      apply f_equal with (f := wrepr U32) in H3.
      rewrite !wrepr_unsigned in H3.
      rewrite H3 in H2 ; clear H3.

      apply (ssrbool.elimT mapP) in H2.
      destruct H2.
      rewrite H1 in H H0 ; clear H1.

      rewrite mem_iota in H0.

      set (Z.to_nat (unsigned (is_pure (_ .+ _)))) in H0.
      set (Z.to_nat _) in H0.

      assert (n0 < n1)%N by easy.
      rewrite subnKC in H0.
      2: easy.

      clear -H0.

      apply (ssrbool.elimT andP) in H0.
      destruct H0.

      assert (x0 < n0)%N.
      2: easy.
      {
        unfold n0.
        setoid_rewrite wunsigned_repr.
        simpl.
        rewrite Zmod_small.
        {
          unfold urepr.
          simpl.
          rewrite Z2Nat.inj_add.
          {
            rewrite Z2Nat.inj_mod.
            {
              rewrite Nat2Z.id.
              rewrite Nat.mod_small.
              {
                easy.
              }
              {
                eapply lt_trans.
                1: apply /ltP ; apply H0.
                subst n1.
                apply Z2Nat.inj_lt.
                1: apply wunsigned_range.
                1: easy.
                apply wunsigned_range.
              }
            }
            {
              apply Zle_0_nat.
            }
            {
              easy.
            }
          }
          {
            now apply Z_mod_lt.
          }
          {
            easy.
          }
        }
        {
          split.
          {
            apply Z.add_nonneg_nonneg.
            2: easy.
            setoid_rewrite wunsigned_repr.
            now apply Z_mod_lt.
          }
          {
            unfold urepr.
            simpl.

            rewrite Zmod_small.
            2:{
              split.
              1: apply Zle_0_nat.
              apply Z.lt_trans with (Z.of_nat n1).
              2:{
                subst n1.
                rewrite Z2Nat.id ; apply wunsigned_range.
              }
              now apply Nat2Z.inj_lt.
            }

            eapply Z.lt_le_trans with (m := Z.of_nat n1.+1).
            1:{
              rewrite Nat2Z.inj_succ.
              unfold urepr.
              simpl "\val".
              apply Zsucc_lt_compat.
              apply Nat2Z.inj_lt.
              apply /ltP.
              assumption.
            }
            rewrite Nat2Z.inj_succ.
            apply Zlt_le_succ.
            rewrite Z2Nat.id ; apply wunsigned_range.
          }
        }
      }
    }
    1:{
      eapply H0 ; red ; intros ; clear -H H2 H3.
      subst y.
      unfold Build_Range , prod_both at 1 in H2 ; simpl in H2.

      apply f_equal with (f := Z.of_nat) in H3.
      rewrite !Z2Nat.id in H3 ; [ | apply wunsigned_range.. ].
      apply f_equal with (f := wrepr U32) in H3.
      rewrite !wrepr_unsigned in H3.
      rewrite H3 in H2 ; clear H3.

      apply (ssrbool.elimT mapP) in H2.
      destruct H2.
      rewrite H1 in H H0 ; clear H1.

      rewrite mem_iota in H0.

      simpl in H0.
      rewrite wunsigned_repr in H0.
      rewrite Zmod_small in H0. 2: easy.
      rewrite add0n in H0.
      setoid_rewrite subn0 in H0.
      clear -H0.

      rewrite wunsigned_repr in H0.
      rewrite Z2Nat.inj_mod in H0.
      2: apply Zle_0_nat.
      2: easy.
      rewrite Nat2Z.id in H0.
      set (Z.to_nat _) in H0.

      epose (Nat.Div0.mod_le x0 n0).
      apply (ssrbool.elimT ltP) in H0.
      epose proof (Nat.lt_le_trans _ _ _ H0 l).
      clear -H.
      easy.
    }
  Qed.

  (*** Solution *)

  (** DL *)

  Notation " 'chDLInput' " :=
    (f_Z)
    (in custom pack_type at level 2).

  Notation " 'chDLOutput' " :=
    (v_G)
    (in custom pack_type at level 2).

  Definition DL : nat := 101.

  Program Definition dl_real :
    package fset0
      [interface]
      [interface
         #val #[ DL ] : chDLInput → chDLOutput
      ]
    :=
    [package
        #def #[ DL ] (xi : chDLInput) : chDLOutput
        {
          (* xi ← sample (uniform #|'Z_q|) ;; let xi := WitnessToField (otf xi) in *)
          ret (g ^+ FieldToWitness xi)
        }
    ].
  Fail Next Obligation.

  Program Definition dl_ideal :
    package fset0
      [interface]
      [interface
         #val #[ DL ] : chDLInput → chDLOutput
      ]
    :=
    [package
        #def #[ DL ] (_ : chDLInput) : chDLOutput
        {
          xi ← sample (uniform #|'Z_q|) ;; let xi := WitnessToField (otf xi) in
          ret (g ^+ FieldToWitness xi)
        }
    ].
  Fail Next Obligation.

  Notation " 'chDLRandom' " :=
    (v_G × v_Z)
    (in custom pack_type at level 2).

  Definition DL_RANDOM : nat := 102.

  Program Definition dl_random :
    package fset0
      [interface
         #val #[ DL ] : chDLInput → chDLOutput
      ]
      [interface
         #val #[ DL_RANDOM ] : 'unit → chDLRandom
      ]
    :=
    [package
        #def #[ DL_RANDOM ] (_ : 'unit) : chDLRandom
        {
          #import {sig #[ DL ] : chDLInput → chDLOutput }
          as DL ;;
          xi ← sample (uniform #|'Z_q|) ;;
          let xi := WitnessToField (otf xi) in
          h ← DL xi ;;
          ret (h, xi : f_Z)
        }
    ].
  Fail Next Obligation.

  Definition dl_game :
    loc_GamePair [interface
         #val #[ DL ] : chDLInput → chDLOutput
      ] :=
    λ b,
      if b then {locpackage dl_ideal} else {locpackage dl_real}.

  Definition dl_real_ : loc_package [interface] [interface #val #[ DL_RANDOM ] : 'unit → chDLRandom] := {locpackage (pack dl_random ∘ pack dl_real) #with ltac:(unshelve solve_valid_package ; apply fsubsetxx)} .

  Definition dl_ideal_ : loc_package [interface] [interface #val #[ DL_RANDOM ] : 'unit → chDLRandom] := {locpackage (pack dl_random ∘ pack dl_ideal) #with ltac:(unshelve solve_valid_package ; apply fsubsetxx)} .

  Definition DL_game :
    loc_GamePair [interface
         #val #[ DL_RANDOM ] : 'unit → chDLRandom
      ] :=
    λ b,
      if b then dl_ideal_ else dl_real_.

  (* (∀ D, DDH.ϵ_DDH D <= ϵ_DDH) *)
  Definition ϵ_DL := Advantage DL_game.

  (** Schnorr *) (* TODO: move to schnorr file *)
  Notation " 'schnorrInput' " :=
    (f_Z × v_G)
      (in custom pack_type at level 2).

  Notation " 'schnorrOutput' " :=
    (t_SchnorrZKPCommit)
      (in custom pack_type at level 2).

  Definition SCHNORR : nat := 212.

  Program Definition schnorr_real :
    package fset0
      [interface]
      [interface #val #[ SCHNORR ] : schnorrInput → schnorrOutput]
    :=
    [package
       #def #[ SCHNORR ] ('(xi, h) : schnorrInput) : schnorrOutput
       {
         #assert Schnorr_ZKP.Schnorr.MyParam.R h (FieldToWitness xi) ;;
         ri ← sample (uniform #|'Z_q|) ;; let ri := WitnessToField (otf ri) in
         is_state (schnorr_zkp (ret_both ri) (ret_both h) (ret_both xi))
       }
    ].
  Next Obligation.
    intros.
    ssprove_valid.
    destruct x as [xi h].
    ssprove_valid.
    1: apply valid_scheme ; rewrite <- fset0E ; apply (ChoiceEquality.is_valid_code (both_prog_valid _)).
  Qed.
  Fail Next Obligation.

  Notation " 'schnorrMidInp' " :=
    (Schnorr_ZKP.Schnorr.MyAlg.choiceStatement × Schnorr_ZKP.Schnorr.MyAlg.choiceWitness)
      (in custom pack_type at level 2).

  Notation " 'schnorrMidOut' " :=
    (Schnorr_ZKP.Schnorr.MyAlg.choiceTranscript)
    (in custom pack_type at level 2).

  Program Definition schnorr_mid :
    package fset0
      [interface #val #[ Schnorr_ZKP.Schnorr.Sigma.RUN ] : schnorrMidInp → schnorrMidOut ]
      [interface #val #[ SCHNORR ] : schnorrInput → schnorrOutput]
    :=
    [package
       #def #[ SCHNORR ] ('(xi, h) : schnorrInput) : schnorrOutput
       {
         #import {sig #[ Schnorr_ZKP.Schnorr.Sigma.RUN ] : schnorrMidInp → schnorrMidOut }
         as schnorr ;;
         '(_,u,e,z) ← schnorr (fto (h : gT), fto (FieldToWitness xi)) ;;
         ret (otf u : v_G, WitnessToField (otf e) : f_Z, WitnessToField (otf z) : f_Z)
       }
    ].
  Next Obligation.
    intros.
    ssprove_valid.
    destruct x as [xi h].
    ssprove_valid.
    destruct x as [[[? ?] ?] ?].
    ssprove_valid.
  Qed.
  Fail Next Obligation.

  Program Definition schnorr_ideal :
    package fset0
      [interface]
      [interface #val #[ SCHNORR ] : schnorrInput → schnorrOutput]
    :=
    [package
       #def #[ SCHNORR ] ('(xi, h) : schnorrInput) : schnorrOutput
       {
         c ← sample (uniform #|'Z_q|) ;;
         #assert Schnorr_ZKP.Schnorr.MyParam.R h (FieldToWitness xi) ;;
         z ← sample (uniform #|'Z_q|) ;;
         is_state (Build_t_SchnorrZKPCommit
                     (f_schnorr_zkp_u := ret_both ((g ^+ otf z * (h : gT) ^- otf c)%g))
                     (f_schnorr_zkp_c := ret_both (WitnessToField (otf c)))
                     (f_schnorr_zkp_z := ret_both (WitnessToField (otf z))))
       }
    ].
  Next Obligation.
    intros.
    ssprove_valid.
    destruct x as [xi h].
    ssprove_valid.
    1: apply valid_scheme ; rewrite <- fset0E ; apply (ChoiceEquality.is_valid_code (both_prog_valid _)).
  Qed.
  Fail Next Obligation.

  Program Definition schnorr_ideal_no_assert :
    package fset0
      [interface]
      [interface #val #[ SCHNORR ] : schnorrInput → schnorrOutput]
    :=
    [package
       #def #[ SCHNORR ] ('(xi, h) : schnorrInput) : schnorrOutput
       {
         c ← sample (uniform #|'Z_q|) ;;
         z ← sample (uniform #|'Z_q|) ;;
         is_state (Build_t_SchnorrZKPCommit
                     (f_schnorr_zkp_u := ret_both ((g ^+ otf z * (h : gT) ^- otf c)%g))
                     (f_schnorr_zkp_c := ret_both (WitnessToField (otf c)))
                     (f_schnorr_zkp_z := ret_both (WitnessToField (otf z))))
       }
    ].
  Next Obligation.
    intros.
    ssprove_valid.
    destruct x as [xi h].
    ssprove_valid.
    1: apply valid_scheme ; rewrite <- fset0E ; apply (ChoiceEquality.is_valid_code (both_prog_valid _)).
  Qed.
  Fail Next Obligation.

  Lemma schnorr_advantage :
    ∀ (LA : {fset Location}) (A : raw_package),
      ValidPackage LA [interface #val #[SCHNORR] : schnorrInput → schnorrOutput ] A_export A →
      LA :#: Schnorr_ZKP.Schnorr.MyAlg.Sigma_locs ->
      LA :#: Schnorr_ZKP.Schnorr.MyAlg.Simulator_locs ->
      (AdvantageE
        (schnorr_real)
        (schnorr_ideal) A = 0)%R.
  Proof.
    intros.
    split_advantage (pack schnorr_mid ∘ pack Schnorr_ZKP.hacspec_run).
    1:{
      apply: eq_rel_perf_ind_ignore.
      4: rewrite fset0U ; apply H0.
      3: apply fdisjoints0.
      1: apply fsubsetxx.

      unfold eq_up_to_inv.
      simplify_eq_rel inp_unit.
      destruct inp_unit as [xi h].
      simpl.

      repeat choice_type_eqP_handle.
      erewrite !cast_fun_K.
      fold chElement.

      eapply r_transR.
      1:{
        apply r_nice_swap_rule ; [ easy | easy | ].
        apply r_bind_assertD.
      }
      rewrite !otf_fto.
      apply r_assertD_same.
      intros.
      simpl.

      eapply r_uniform_bij with (f := _).
      1: instantiate (1 := fun x => x) ; now apply inv_bij.
      intros.

      rewrite bind_assoc.
      rewrite <- bind_ret at 1.
      rewrite !WitnessToFieldCancel.
      ssprove_same_head_generic.
      destruct a as [[? ?] ?].
      rewrite bind_rewrite.
      simpl.
      rewrite !otf_fto.
      rewrite !WitnessToFieldCancel.
      apply r_ret.
      easy.
    }
    split_advantage (pack schnorr_mid ∘ (pack Schnorr_ZKP.Schnorr.Sigma.RUN_interactive)).
    {
      unfold_advantageE.
      eapply Schnorr_ZKP.hacspec_vs_RUN_interactive.
      1:{
        solve_valid_package.
        apply H.
      }
      apply H0.
    }
    split_advantage (pack schnorr_mid ∘ (pack Schnorr_ZKP.Schnorr.Sigma.SHVZK_real_aux ∘ pack Schnorr_ZKP.Schnorr.Sigma.SHVZK_real)).
    {
      unfold_advantageE.
      eapply Schnorr_ZKP.Schnorr.Sigma.run_interactive_shvzk.
      3: apply H0.
      2:{
        solve_valid_package.
        apply H.
        Unshelve.
        all: try (apply fsubsetxx || solve_in_fset).
        refine fset0.
      }
      intros.
      unfold Schnorr_ZKP.Schnorr.MyAlg.choiceTranscript.
      refine ({code ret (chCanonical _)}).
    }
    split_advantage (pack schnorr_mid ∘ (pack Schnorr_ZKP.Schnorr.Sigma.SHVZK_real_aux ∘ pack Schnorr_ZKP.Schnorr.Sigma.SHVZK_ideal)).
    {
      unfold_advantageE.
      unfold_advantageE.

      eapply Schnorr_ZKP.Schnorr.schnorr_SHVZK with (LA := LA).
      2: apply H0.
      1:{
        solve_valid_package.
        apply H.
        Unshelve.
        all: try (apply fsubsetxx || solve_in_fset).
      }
    }
    {
      apply: eq_rel_perf_ind_ignore.
      3: rewrite !fset0U ; apply H1.
      3: apply fdisjoints0.
      1: apply fsubsetxx.

      unfold eq_up_to_inv.
      simplify_eq_rel inp_unit.
      destruct inp_unit as [xi h].
      simpl.

      repeat choice_type_eqP_handle.
      erewrite !cast_fun_K.
      fold chElement.

      simpl.

      eapply r_uniform_bij with (f := _).
      1: instantiate (1 := fun x => x) ; now apply inv_bij.
      intros.

      rewrite bind_assoc.
      eapply r_transL.
      1:{
        apply r_nice_swap_rule ; [ easy | easy | ].
        apply r_bind_assertD.
      }
      simpl.
      rewrite !otf_fto.

      apply r_assertD_same.
      intros.

      eapply r_uniform_bij with (f := _).
      1: instantiate (1 := fun x => x) ; now apply inv_bij.
      intros.

      rewrite otf_fto.
      now apply r_ret.
    }
  Qed.

  (** Commit *)

  Notation " 'chCommitInput' " :=
    (v_G)
    (in custom pack_type at level 2).

  Notation " 'chCommitOutput' " :=
    (f_Z)
    (in custom pack_type at level 2).

  Definition COMMIT : nat := 142.

  Program Definition commit_real :
    package fset0
      [interface]
      [interface
         #val #[ COMMIT ] : chCommitInput → chCommitOutput
      ]
    :=
    [package
        #def #[ COMMIT ] (vote_i : chCommitInput) : chCommitOutput
        {
          commit ← is_state (f_hash (t_Group := HOGaFE.GroupAndField.OVN.v_G_t_Group)
             (impl__into_vec
                (unsize
                   (box_new
                      (array_from_list [(ret_both vote_i)]))))) ;;
          ret (commit : v_Z)
        }
    ].
  Next Obligation.
    intros.
    ssprove_valid.
    1: apply valid_scheme ; rewrite <- fset0E ; apply (ChoiceEquality.is_valid_code (both_prog_valid _)).
  Qed.
  Fail Next Obligation.

  Program Definition commit_ideal :
    package fset0
      [interface]
      [interface
         #val #[ COMMIT ] : chCommitInput → chCommitOutput
      ]
    :=
    [package
        #def #[ COMMIT ] (_ : chCommitInput) : chCommitOutput
        {
          xi ← sample (uniform #|'Z_q|) ;; let xi := WitnessToField (otf xi) in
          ret (xi : v_Z)
        }
    ].
  Fail Next Obligation.

  (* hash_is_psudorandom / commit - game *)
  Definition Commit_game :
    loc_GamePair [interface
         #val #[ COMMIT ] : chCommitInput → chCommitOutput
      ] :=
    λ b,
      if b then {locpackage commit_ideal} else {locpackage commit_real}.

  (* (∀ D, DDH.ϵ_DDH D <= ϵ_DDH) *)
  Definition ϵ_COMMIT := Advantage Commit_game.


  (** GPowYiNotZero *)

  Notation " 'chGPowYiNotZeroInput' " :=
    ('unit)
    (in custom pack_type at level 2).

  Notation " 'chGPowYiNotZeroOutput' " :=
    (v_G)
    (in custom pack_type at level 2).

  Definition GPOWYINOTZERO : nat := 143.

  Program Definition GPowYiNotZero_real i state :
    package fset0
      [interface]
      [interface
         #val #[ GPOWYINOTZERO ] : chGPowYiNotZeroInput → chGPowYiNotZeroOutput
      ]
    :=
    [package
        #def #[ GPOWYINOTZERO ] (_ : chGPowYiNotZeroInput) : chGPowYiNotZeroOutput
        {
          temp ← is_state (compute_g_pow_yi (ret_both (i : int32)) (f_g_pow_xis (ret_both state))) ;;
          ret (temp : v_G)
        }
    ].
  Next Obligation.
    intros.
    ssprove_valid.
    1: apply valid_scheme ; rewrite <- fset0E ; apply (ChoiceEquality.is_valid_code (both_prog_valid _)).
  Qed.
  Fail Next Obligation.

  Program Definition GPowYiNotZero_ideal i state :
    package fset0
      [interface]
      [interface
         #val #[ GPOWYINOTZERO ] : chGPowYiNotZeroInput → chGPowYiNotZeroOutput
      ]
    :=
    [package
        #def #[ GPOWYINOTZERO ] (_ : chGPowYiNotZeroInput) : chGPowYiNotZeroOutput
        {
          temp ← is_state (compute_g_pow_yi (ret_both (i : int32)) (f_g_pow_xis (ret_both state))) ;;
          #assert ((temp : gT) != g ^+ nat_of_ord (FieldToWitness (0%R))) ;;
          ret (temp : v_G)
        }
    ].
  Next Obligation.
    intros.
    ssprove_valid.
    1: apply valid_scheme ; rewrite <- fset0E ; apply (ChoiceEquality.is_valid_code (both_prog_valid _)).
  Qed.
  Fail Next Obligation.

  (* GPowYiNotZero - game *)
  Definition GPowYiNotZero_game i state :
    loc_GamePair [interface
         #val #[ GPOWYINOTZERO ] : chGPowYiNotZeroInput → chGPowYiNotZeroOutput
      ] :=
    λ b,
      if b then {locpackage (GPowYiNotZero_ideal i state)} else {locpackage (GPowYiNotZero_real i state)}.

  (* (∀ D, DDH.ϵ_DDH D <= ϵ_DDH) *)
  Definition ϵ_GPOWYINOTZERO i state := Advantage (GPowYiNotZero_game i state).

  (** CDS *)

  Notation " 'CDSoutput' " :=
    (t_OrZKPCommit)
    (in custom pack_type at level 2).
  (* (v_G × v_G × v_G × v_G × v_G × v_G × f_Z × f_Z × f_Z × f_Z × f_Z) *)

  Notation " 'CDSinput' " :=
    ((v_G × v_G × v_G) × (f_Z × 'bool))
    (in custom pack_type at level 2).

  Definition CDS : nat := 233.

  Program Definition cds_real :
    package fset0
      [interface]
      [interface #val #[ CDS ] : CDSinput → CDSoutput ]
    :=
    [package
       #def #[ CDS ] ('((x,h,y),(xi,vi)) : CDSinput) : CDSoutput
       {
         #assert OR_ZKP.proof_args.MyParam.R (x,h,y) (FieldToWitness xi, vi, h) ;;
          wr ← sample uniform #|'Z_q| ;;
          rr ← sample uniform #|'Z_q| ;;
          dr ← sample uniform #|'Z_q| ;;
          is_state (zkp_one_out_of_two
                      (ret_both (WitnessToField (otf wr : 'Z_q)))
                      (ret_both (WitnessToField (otf rr : 'Z_q)))
                      (ret_both (WitnessToField (otf dr : 'Z_q)))
                      (ret_both h)
                      (ret_both xi)
                      (ret_both (vi : 'bool)))
       }
    ].
  Next Obligation.
    intros.
    ssprove_valid.
    destruct x as [[[? ?] ?] [? ?]].
    ssprove_valid.
    1: apply valid_scheme ; rewrite <- fset0E ; apply (ChoiceEquality.is_valid_code (both_prog_valid _)).
  Qed.
  Fail Next Obligation.

  Program Definition cds_ideal :
    package fset0
      [interface]
      [interface #val #[ CDS ] : CDSinput → CDSoutput ]
    :=
    [package
       #def #[ CDS ] ('((x,h,y),(xi,vi)) : CDSinput) : CDSoutput
       {
         #assert OR_ZKP.proof_args.MyParam.R (x,h,y) (FieldToWitness xi, vi, h) ;;
         c ← sample uniform #|'Z_q| ;;

         d ← sample uniform #|'Z_q| ;;
         r ← sample uniform #|'Z_q| ;;
         r_other ← sample uniform #|'Z_q| ;;
         let d2 := otf d in
         let r2 := otf r in
         let r1 := otf r_other in
         let d1 := (otf c - d2)%R in
         let a1 := (g ^+ r1 * (x : gT) ^+ d1)%g in
         let b1 := ((h : gT) ^+ r1 * (y : gT) ^+ d1)%g in
         let a2 := (g ^+ r2 * (x : gT) ^+ d2)%g in
         let b2 := ((h : gT) ^+ r2 * ((y : gT) * invg g) ^+ d2)%g in

         ret ((x,y,
                a1,b1,a2,b2,
                WitnessToField (otf c),
                WitnessToField d1,WitnessToField d2,WitnessToField r1,WitnessToField r2)
             : t_OrZKPCommit)
       }
    ].
  Next Obligation.
    intros.
    ssprove_valid.
    destruct x as [[[? ?] ?] [? ?]].
    ssprove_valid.
  Qed.
  Fail Next Obligation.

  Program Definition cds_ideal_no_assert :
    package fset0
      [interface]
      [interface #val #[ CDS ] : CDSinput → CDSoutput ]
    :=
    [package
       #def #[ CDS ] ('((x,h,y),(xi,vi)) : CDSinput) : CDSoutput
       {
         c ← sample uniform #|'Z_q| ;;

         d ← sample uniform #|'Z_q| ;;
         r ← sample uniform #|'Z_q| ;;
         r_other ← sample uniform #|'Z_q| ;;
         let d2 := otf d in
         let r2 := otf r in
         let r1 := otf r_other in
         let d1 := (otf c - d2)%R in
         let a1 := (g ^+ r1 * (x : gT) ^+ d1)%g in
         let b1 := ((h : gT) ^+ r1 * (y : gT) ^+ d1)%g in
         let a2 := (g ^+ r2 * (x : gT) ^+ d2)%g in
         let b2 := ((h : gT) ^+ r2 * ((y : gT) * invg g) ^+ d2)%g in

         ret ((x,y,
                a1,b1,a2,b2,
                WitnessToField (otf c),
                WitnessToField d1,WitnessToField d2,WitnessToField r1,WitnessToField r2)
             : t_OrZKPCommit)
       }
    ].
  Next Obligation.
    intros.
    ssprove_valid.
    destruct x as [[[? ?] ?] [? ?]].
    ssprove_valid.
  Qed.
  Fail Next Obligation.

  Notation " 'CDSMidInp' " :=
    (OR_ZKP.proof_args.MyAlg.choiceStatement × OR_ZKP.proof_args.MyAlg.choiceWitness)
      (in custom pack_type at level 2).

  Notation " 'CDSMidOut' " :=
    (OR_ZKP.proof_args.MyAlg.choiceTranscript)
    (in custom pack_type at level 2).

  Program Definition cds_mid :
    package fset0
      [interface #val #[ OR_ZKP.proof_args.Sigma.RUN ] : CDSMidInp → CDSMidOut ]
      [interface #val #[ CDS ] : CDSinput → CDSoutput ]
    :=
    [package
       #def #[ CDS ] ('((x,h,y),(xi,vi)) : CDSinput) : CDSoutput
       {
         #import {sig #[ OR_ZKP.proof_args.Sigma.RUN ] : CDSMidInp → CDSMidOut }
         as cds ;;
         temp ← cds (fto (x : gT, h : gT, y : gT), fto (FieldToWitness xi, vi, h : gT)) ;;
         ret (OR_ZKP.or_sigma_ret_to_hacspec_ret temp)
       }
    ].
  Next Obligation.
    intros.
    ssprove_valid.
    destruct x as [[[? ?] ?] [? ?]].
    ssprove_valid.
  Qed.
  Fail Next Obligation.

  Lemma cds_advantage :
    ∀ (LA : {fset Location}) (A : raw_package),
      ValidPackage LA [interface #val #[CDS] : CDSinput → CDSoutput ] A_export A ->
      LA :#: OR_ZKP.proof_args.MyAlg.Sigma_locs ->
      LA :#: OR_ZKP.proof_args.MyAlg.Simulator_locs ->
      (AdvantageE
        (cds_real)
        (cds_ideal) A = 0)%R.
  Proof.
    intros.
    split_advantage (cds_mid ∘ OR_ZKP.hacspec_or_run).
    {
      apply: eq_rel_perf_ind_ignore.
      4: rewrite fset0U ; apply H0.
      3: apply fdisjoints0.
      1: apply fsubsetxx.

      unfold eq_up_to_inv.
      simplify_eq_rel inp_unit.

      destruct (inp_unit) as [[[x h] y] [xi vi]].
      intros.

      simpl.

      repeat choice_type_eqP_handle.
      erewrite !cast_fun_K.
      fold chElement.


      eapply r_transR.
      1:{
        apply r_nice_swap_rule ; [ easy | easy | ].
        apply r_bind_assertD.
      }
      simpl.
      rewrite !otf_fto.

      apply r_assertD_same.
      intros.

      ssprove_sync=> ?.
      ssprove_sync=> ?.
      ssprove_sync=> ?.
      rewrite bind_assoc.
      rewrite WitnessToFieldCancel.

      replace (_ == _) with vi.
      2:{
        simpl.

        unfold OR_ZKP.proof_args.MyParam.R in e.
        apply (ssrbool.elimT andP) in e ; destruct e.
        apply (ssrbool.elimT andP) in H2 ; destruct H2.

        apply (ssrbool.elimT eqP) in H2.
        apply (ssrbool.elimT eqP) in H3.
        apply (ssrbool.elimT eqP) in H4.
        subst.

        destruct vi.
        - rewrite eqxx.
          reflexivity.
        - rewrite expg0.
          symmetry.
          apply /eqP.
          red ; intros.
          apply prod_swap_iff in H2.
          rewrite mulg1 in H2.
          rewrite mulVg in H2.
          apply generator_is_not_one.
          apply both_equivalence_is_pure_eq.
          easy.
      }
      rewrite <- bind_ret at 1.

      simpl.

      set (zkp_one_out_of_two _ _ _ _ _ _).

      apply (somewhat_substitution b).
      apply (somewhat_substitutionR b).
      rewrite !bind_rewrite.
      apply r_ret.
      intros.
      split ; [ | easy ].
      subst b.

      setoid_rewrite OR_ZKP.ret_cancel.
      2:{
        unfold zkp_one_out_of_two at 1.
        unfold Build_t_OrZKPCommit at 1 2.
        repeat unfold let_both at 1.

        unfold OR_ZKP.proof_args.MyParam.R in e.
        apply (ssrbool.elimT andP) in e ; destruct e.
        apply (ssrbool.elimT andP) in H3 ; destruct H3.

        apply (ssrbool.elimT eqP) in H3.
        apply (ssrbool.elimT eqP) in H4.
        apply (ssrbool.elimT eqP) in H5.
        subst.

        simpl.
        destruct vi.
        + simpl.
          rewrite <- conversion_is_true.
          reflexivity.
        + simpl.
          rewrite <- conversion_is_true.
          reflexivity.
      }
      2:{
        unfold zkp_one_out_of_two at 1.
        unfold Build_t_OrZKPCommit at 1 2.
        repeat unfold let_both at 1.

        unfold OR_ZKP.proof_args.MyParam.R in e.
        apply (ssrbool.elimT andP) in e ; destruct e.
        apply (ssrbool.elimT andP) in H3 ; destruct H3.

        apply (ssrbool.elimT eqP) in H3.
        apply (ssrbool.elimT eqP) in H4.
        apply (ssrbool.elimT eqP) in H5.
        subst.

        simpl.
        destruct vi.
        + simpl.
          rewrite pow_witness_to_field.
          rewrite WitnessToFieldCancel.
          rewrite expg1.
          Misc.push_down_sides.
          reflexivity.
        + simpl.
          rewrite pow_witness_to_field.
          rewrite WitnessToFieldCancel.
          rewrite expg0. rewrite mulg1.
          Misc.push_down_sides.
          reflexivity.
      }
      reflexivity.
    }

    split_advantage (cds_mid ∘ (OR_ZKP.proof_args.Sigma.SHVZK_real_aux ∘ OR_ZKP.proof_args.Sigma.SHVZK_real)).
    {
      unfold_advantageE.
      eapply OR_ZKP.run_interactive_or_shvzk.
      1: unshelve solve_valid_package.
      4: apply H.
      3: apply H0.
      1,2: solve_in_fset.
    }

    split_advantage (cds_mid ∘ (OR_ZKP.proof_args.Sigma.SHVZK_real_aux ∘ OR_ZKP.proof_args.Sigma.SHVZK_ideal)).
    {
      unfold_advantageE.
      unfold_advantageE.
      apply OR_ZKP.shvzk_success with (LA := LA).
      2: apply H0.
      solve_valid_package.
      apply H.

      Unshelve.
      all: revgoals.
      all: try (apply fsubsetxx || solve_in_fset).
    }

    {
      apply: eq_rel_perf_ind_ignore.
      3: rewrite !fset0U ; apply H1.
      3: apply fdisjoints0.
      1: apply fsubsetxx.

      unfold eq_up_to_inv.
      simplify_eq_rel inp_unit.

      destruct (inp_unit) as [[[x h] y] [xi vi]].
      intros.

      simpl.

      repeat choice_type_eqP_handle.
      erewrite !cast_fun_K.
      fold chElement.

      simpl.

      set (OR_ZKP.proof_args.MyParam.R _ _).
      eapply r_transL with (c₀ := #assert b ;; _).
      1:{
        apply r_nice_swap_rule ; [ easy | easy | ].
        destruct b.
        + simpl.
          apply rreflexivity_rule.
        + eapply r_const_sample_L ; [ apply LosslessOp_uniform | intros ].
          rewrite bind_assoc.
          apply r_bind_assertD.
      }
      subst b.
      rewrite !otf_fto.

      apply r_assertD_same.
      intros.

      ssprove_sync=> ?.
      setoid_rewrite bind_rewrite.
      unfold OR_ZKP.or_sigma_ret_to_hacspec_ret.
      rewrite !otf_fto.
      setoid_rewrite otf_fto.
      setoid_rewrite otf_fto.

      ssprove_sync=> d.
      ssprove_sync=> r_other.
      ssprove_sync=> r.
      now apply r_ret.
    }
  Fail Timeout 5 Qed. Admitted. (* 216.817 secs *)

  (** DL_ *)

  Notation " 'chDL_Input' " :=
    (v_G × f_Z × f_Z)
    (in custom pack_type at level 2).

  Notation " 'chDL_Output' " :=
    (v_G)
    (in custom pack_type at level 2).

  Definition DL_ : nat := 101.

  Theorem N_lt_succ_l : forall {a b},
      (a.+1 < b)%N -> (a < b)%N.
  Proof. easy. Qed.

  Fixpoint inv_helper (i : nat) `{H : (i < (Zp_trunc q).+2)%N} (h : gT) : Datatypes.option 'Z_q :=
    let oi : 'Z_q := Ordinal (m := i) (n := (S (S (Zp_trunc q)))) H in
    if g ^+ oi == h
    then Some oi
    else
      match i as k return (k < (Zp_trunc q).+2)%N -> Datatypes.option 'Z_q with
      | 0%nat => fun _ => None
      | S n => fun H' => inv_helper n (H := N_lt_succ_l H') h
      end H.

  Lemma always_find_smaller_power :
    forall (i x : nat) H H0, (x <= i)%N -> inv_helper i (H := H) (g ^+ x) = Some (Ordinal (m := x) (n := (S (S (Zp_trunc q)))) H0).
  Proof.
    clear ; intros.
    induction i.
    {
      destruct x ; [ | easy ].
      simpl.
      rewrite eqxx.
      f_equal.
      apply ord_ext.
      reflexivity.
    }
    {
      simpl.
      rewrite eq_expg_mod_order.

      destruct (i.+1 == x) eqn:x_is_Si.
      {
        apply (ssrbool.elimT eqP) in x_is_Si.
        subst.
        rewrite eqxx.
        f_equal.
        apply ord_ext.
        reflexivity.
      }
      {
        rewrite !modn_small.
        3:{
          simpl.
          rewrite order_ge1 in H.
          apply H.
        }
        2:{
          rewrite order_ge1 in H.
          eapply leq_ltn_trans ; [ apply H0 | ].
          rewrite order_ge1.
          easy.
        }

        rewrite x_is_Si.

        apply IHi.
        easy.
      }
    }
  Qed.

  Lemma q_sub_1_lt_q : is_true (q.-1 < (Zp_trunc q).+2)%N.
  Proof. unfold Zp_trunc. easy. Qed.

  Lemma Zq_lt_q : forall x : 'Z_q, is_true (x < (Zp_trunc q).+2)%N.
  Proof. unfold Zp_trunc. easy. Qed.

  Corollary always_find_smaller_power_q : forall (x : nat) H0,
      inv_helper q.-1 (H := q_sub_1_lt_q) (g ^+ x) =
        Some (Ordinal (m := x) (n := (S (S (Zp_trunc q)))) H0).
  Proof.
    intros.
    apply always_find_smaller_power.
    rewrite order_ge1 in H0. easy.
  Qed.

  Lemma inv_helper_is_not_none : forall h, inv_helper (H := q_sub_1_lt_q) q.-1 h <> None.
  Proof.
    intros.
    red ; intros.
    destruct (cyclic_group_to_exponent h) as [? []] ; subst.
    apply isSome_none in H.
    unshelve erewrite always_find_smaller_power_q in H.
    - rewrite order_ge1. unfold q. easy.
    - easy.
  Defined.

  (* inv_helper_is_not_none h v eqrefl *)
  Definition inv (h : gT) : 'Z_q.
  Proof.
    intros.
    epose proof (inv_helper_is_not_none h).
    destruct (inv_helper _ _) in H.
    {
      apply o.
    }
    {
      contradiction.
    }
  Defined.

  Theorem inv_is_exponent : forall (x : 'Z_q), inv (g ^+ x) = x.
  Proof.
    intros.
    unfold inv.
    unshelve epose proof (always_find_smaller_power_q x (Zq_lt_q x)).
    set (inv_helper_is_not_none (g ^+ x)).
    set (inv_helper _ _) in *.

    generalize dependent n0.
    intros.

    destruct o eqn:no.
    2: contradiction.
    subst o.
    inversion H.
    subst.
    destruct x.
    apply ord_ext.
    reflexivity.
  Qed.

  Theorem inv_is_inv : forall h, g ^+ inv h = h.
  Proof.
    intros.
    destruct (cyclic_group_to_exponent h) as [? []] ; subst.
    unshelve epose proof (inv_is_exponent (Ordinal (m := x) (n := (S (S (Zp_trunc q)))) _)).
    {
      rewrite order_ge1. unfold q. easy.
    }
    rewrite H.
    reflexivity.
  Qed.

  (* Program Definition dl' : *)
  (*   package fset0 *)
  (*     [interface *)
  (*        #val #[ DL ] : chDLInput → chDLOutput *)
  (*     ] *)
  (*     [interface *)
  (*        #val #[ DL_ ] : chDL_Input → chDL_Output *)
  (*     ] *)
  (*   := *)
  (*   [package *)
  (*       #def #[ DL_ ] ('(h,xi) : chDL_Input) : chDL_Output *)
  (*       { *)
  (*         #import {sig #[ DL ] : chDLInput → chDLOutput } *)
  (*         as dl ;; *)
  (*         dl (WitnessToField (FieldToWitness xi * (inv h)))%R *)
  (*       } *)
  (*   ]. *)
  (* Solve All Obligations with now intros ; destruct from_uint_size. *)
  (* Next Obligation. *)
  (*   intros. *)
  (*   ssprove_valid. *)
  (*   destruct x as [[h xi] c]. *)
  (*   ssprove_valid. *)
  (* Qed. *)
  (* Fail Next Obligation. *)

  Print Interface.
  Print opsig.

  Check fin_type.
  Locate "[ package _ ]".

  Definition K_any_package_raw {A : choice_type} {B : finType} (F : Finite.sort B -> Choice.sort A) `{H_pos : Positive #|B|} (K_loc : nat) SET GET {H_disj : SET <> GET} (b : bool) :
    raw_package :=
    mkfmap
      (cons
         (SET,
           (A; 'unit;
            fun v =>
              k ← get (chOption A ; K_loc ) ;;
              match k with
              | None =>
                  k ←
                    (if b
                     then
                       xi ← sample (uniform (H := H_pos) #|B|) ;;
                       ret (F (otf xi) : A)
                     else
                       ret v) ;;
                  #put ('option A ; K_loc) := Some k ;;
                                              ret (Datatypes.tt : 'unit)
              | Some _ =>
                  ret (Datatypes.tt : 'unit)
              end
         ))
         (cons
            (GET,
              ('unit; A;
               fun _ =>
                 k ← get (chOption A ; K_loc ) ;;
                 k ← match k with
                   | None =>
                       (@fail A ;; ret (chCanonical A))
                   | Some x =>
                       ret x
                   end ;;
                 ret k
            ))
            nil)).

  Lemma K_any_package_valid {A : choice_type} {B : finType} (F : Finite.sort B -> Choice.sort A) `{H_pos : Positive #|B|} (K_loc : nat) SET GET {H_disj : SET <> GET} (b : bool) :
    ValidPackage
      (fset [('option A ; K_loc) : Location])
      [interface]
      (fset [(SET, (A, 'unit)); (GET, ('unit, A))])
      (K_any_package_raw F K_loc SET GET (H_disj := H_disj) b).
  Proof.
    repeat apply valid_package_cons ; [ apply valid_empty_package | .. ].
    - intros.
      ssprove_valid.
    - rewrite <- fset0E.
      rewrite imfset0.
      rewrite fset0E.
      apply notin_fset.
    - intros.
      ssprove_valid.
    - rewrite <- fset1E.
      rewrite imfset1.
      rewrite fset1E.
      rewrite notin_fset.
      rewrite notin_cons.
      apply /andP.
      move /eqP : H_disj => //.
  Defined.

  Definition K_any_package {A : choice_type} {B : finType} (F : Finite.sort B -> Choice.sort A) `{H_pos : Positive #|B|} (K_loc : nat) SET GET {H_disj : SET <> GET} (b : bool) :
    package
      (fset [('option A ; K_loc) : Location])
      [interface]
      (fset [(SET, (A, 'unit)); (GET, ('unit, A))]) :=
    {package _ #with K_any_package_valid F K_loc SET GET (H_disj := H_disj) b }.

  Notation " 'chSingleProtocolTranscript' " :=
    ((t_SchnorrZKPCommit × v_G) × (v_Z) × (t_OrZKPCommit × v_G))
    (in custom pack_type at level 2).

  Definition FULL_PROTOCOL_INTERFACE : nat := 102.
  Definition SECOND_STEP : nat := 103.

  (* Field or group element *)

  #[global] Notation " 'chSETFinp' " :=
    (v_Z : choice_type)
      (in custom pack_type at level 2).
  #[global] Notation " 'chSETFout' " :=
    ('unit)
      (in custom pack_type at level 2).

  #[global] Notation " 'chGETFinp' " :=
    ('unit : choice_type)
      (in custom pack_type at level 2).
  #[global] Notation " 'chGETFout' " :=
    (v_Z : choice_type)
      (in custom pack_type at level 2).

  Program Definition KF_package (K_loc : nat) SET GET {H_disj : SET <> GET} (b : bool) :
    package
      (fset [('option v_Z ; K_loc) : Location])
      [interface]
      [interface
         #val #[ SET ] : chSETFinp → chSETFout ;
         #val #[ GET ] : chGETFinp → chGETFout
      ] :=
    K_any_package
      (A := v_Z)
      (B := 'Z_q)
      (fun xi => WitnessToField xi)
      K_loc SET GET (H_disj := H_disj) b.

  #[global] Notation " 'chSETinp' " :=
    (v_G : choice_type)
      (in custom pack_type at level 2).
  #[global] Notation " 'chSETout' " :=
    ('unit)
      (in custom pack_type at level 2).

  #[global] Notation " 'chGETinp' " :=
    ('unit : choice_type)
      (in custom pack_type at level 2).
  #[global] Notation " 'chGETout' " :=
    (v_G : choice_type)
      (in custom pack_type at level 2).

  Definition K_package (K_loc : nat) SET GET {H_disj : SET <> GET} (b : bool) :
    package
      (fset [('option v_G ; K_loc) : Location])
      [interface]
      [interface
         #val #[ SET ] : chSETinp → chSETout ;
         #val #[ GET ] : chGETinp → chGETout
      ] :=
    K_any_package
      (A := v_G)
      (B := 'Z_q)
      (fun xi => g ^+ xi)
      K_loc SET GET (H_disj := H_disj) b.

  #[global] Notation " 'chSETZKPinp' " :=
    (t_SchnorrZKPCommit : choice_type)
      (in custom pack_type at level 2).
  #[global] Notation " 'chSETZKPout' " :=
    ('unit)
      (in custom pack_type at level 2).

  #[global] Notation " 'chGETZKPinp' " :=
    ('unit : choice_type)
      (in custom pack_type at level 2).
  #[global] Notation " 'chGETZKPout' " :=
    (t_SchnorrZKPCommit : choice_type)
      (in custom pack_type at level 2).

  Definition Kzkp_package (K_loc : nat) SET GET {H_disj : SET <> GET} (b : bool) :
    package
      (fset [('option t_SchnorrZKPCommit ; K_loc) : Location])
      [interface]
      [interface
         #val #[ SET ] : chSETZKPinp → chSETZKPout ;
         #val #[ GET ] : chGETZKPinp → chGETZKPout
      ] :=
    K_any_package
      (A := t_SchnorrZKPCommit)
      (B := 'Z_q * 'Z_q * 'Z_q)
      (fun p =>
        let '(a, b, c) := p in
        ( g ^+ a : v_G, (WitnessToField b) : v_Z, (WitnessToField c) : v_Z)
      )
      K_loc SET GET (H_disj := H_disj) b.

  #[global] Notation " 'chSETORinp' " :=
    (t_OrZKPCommit : choice_type)
      (in custom pack_type at level 2).
  #[global] Notation " 'chSETORout' " :=
    ('unit)
      (in custom pack_type at level 2).

  #[global] Notation " 'chGETORinp' " :=
    ('unit : choice_type)
      (in custom pack_type at level 2).
  #[global] Notation " 'chGETORout' " :=
    (t_OrZKPCommit : choice_type)
      (in custom pack_type at level 2).

  Definition Kor_package (K_loc : nat) SET GET {H_disj : SET <> GET} (b : bool) :
    package
      (fset [('option t_OrZKPCommit ; K_loc) : Location])
      [interface]
      [interface
         #val #[ SET ] : chSETORinp → chSETORout ;
         #val #[ GET ] : chGETORinp → chGETORout
      ] :=
    K_any_package
      (A := t_OrZKPCommit)
      (B := 'Z_q * 'Z_q * 'Z_q * 'Z_q * 'Z_q * 'Z_q * 'Z_q * 'Z_q * 'Z_q * 'Z_q * 'Z_q)
      (fun p =>
        let '(av, bv, cv, dv, ev, fv, gv, hv, iv, jv, kv) := p in
        (g ^+ av : v_G,
        g ^+ bv : v_G,
        g ^+ cv : v_G,
        g ^+ dv : v_G,
        g ^+ ev : v_G,
        g ^+ fv : v_G,
        (WitnessToField gv) : v_Z,
        (WitnessToField hv) : v_Z,
        (WitnessToField iv) : v_Z,
        (WitnessToField jv) : v_Z,
        (WitnessToField kv) : v_Z)
      )
      K_loc SET GET (H_disj := H_disj) b.

  #[global] Notation " 'chSETBinp' " :=
    ('bool : choice_type)
      (in custom pack_type at level 2).
  #[global] Notation " 'chSETBout' " :=
    ('unit)
      (in custom pack_type at level 2).

  #[global] Notation " 'chGETBinp' " :=
    ('unit : choice_type)
      (in custom pack_type at level 2).
  #[global] Notation " 'chGETBout' " :=
    ('bool : choice_type)
      (in custom pack_type at level 2).

  Definition KB_package (K_loc : nat) SET GET {H_disj : SET <> GET} (b : bool) :
    package
      (fset [('option 'bool ; K_loc) : Location])
      [interface]
      [interface
         #val #[ SET ] : chSETBinp → chSETBout ;
         #val #[ GET ] : chGETBinp → chGETBout
      ] := K_any_package (A := 'bool) (B := 'bool) id K_loc SET GET (H_disj := H_disj) b.

  Definition K_use_raw {A : choice_type} {B : finType} (F : Finite.sort B -> Choice.sort A) `{H_pos : Positive #|B|} SET :
    raw_package :=
    (mkfmap [(SET, (A; ('unit; (fun _ => (let set_x := λ x, opr (SET, (A, 'unit)) x (λ y, ret y) in
              xi ← sample (uniform (H := H_pos) #|B|) ;;
              set_x (F (otf xi) : A))))))]).

  Lemma K_use_valid :
    forall {A : choice_type} {B : finType} (F : Finite.sort B -> Choice.sort A) `{H_pos : Positive #|B|} SET,
      ValidPackage
        fset0
      (fset [(SET, (A, 'unit))])
      (fset [(SET, (A, 'unit))])
      (K_use_raw F SET).
  Proof. intros. ssprove_valid_package. ssprove_valid. Qed.

  Definition GK_raw {A : choice_type} {B : finType} (F : Finite.sort B -> Choice.sort A) `{H_pos : Positive #|B|} (K_loc : nat) SET GET {H_disj : SET <> GET} (b : bool) :
    raw_package :=
    par (K_use_raw F SET) (ID (fset [(GET, ('unit, A))])) ∘ K_any_package F K_loc SET GET (H_disj := H_disj) b.

  Axiom ignore_Parable : forall A B, Parable A B.

  Ltac solve_flat :=
    clear ;
    unfold flat ;

    intros n u1 u2 ;
    try rewrite !in_fsetU ;

    let H := fresh in
    let H0 := fresh in
    intros H H0 ;

    rewrite <- !fset1E in H, H0 ;
    rewrite !in_fset1 in H, H0 ;

    repeat (apply (ssrbool.elimT ssrbool.orP) in H ; destruct H) ; apply (ssrbool.elimT eqP) in H ; inversion H ; subst ;

    repeat (apply (ssrbool.elimT ssrbool.orP) in H0 ; destruct H0) ; apply (ssrbool.elimT eqP) in H0 ; now inversion H0 ; subst.

  Definition GK_valid {A : choice_type} {B : finType} (F : Finite.sort B -> Choice.sort A) `{H_pos : Positive #|B|} (K_loc : nat) SET GET {H_disj : SET <> GET} (b : bool) :
    ValidPackage
      (fset [('option A ; K_loc) : Location])
      [interface]
      (fset [(SET, (A, 'unit)); (GET, ('unit, A))])
      (GK_raw F K_loc SET GET (H_disj := H_disj) b).
  Proof.
    rewrite <- fset0U.
    refine (valid_link _ _ _ _ _ _ _ _ (pack_valid _)).
    rewrite <- fset0U.
    rewrite fset_cons.
    rewrite fset1E.
    refine (valid_par  _ _ _ _ _ _ _ _ _ _ _).
    + apply ignore_Parable.
    + apply K_use_valid.
    + apply valid_ID.
      solve_flat.
  Qed.

  Definition GK {A : choice_type} {B : finType} (F : Finite.sort B -> Choice.sort A) `{H_pos : Positive #|B|} (K_loc : nat) SET GET {H_disj : SET <> GET} :
    loc_GamePair (fset [(SET, (A, 'unit)); (GET, ('unit, A))]) :=
    fun b => {locpackage _ #with GK_valid F K_loc SET GET (H_disj := H_disj) b}.

  Lemma bobble_sample_uniform_getr :
    ∀
      {C : choiceType}
      {ℓ : Location}
      (o : nat) {Ho : Positive o}
      (c : raw_code C)
      (f : Arit (uniform o) -> ℓ.π1 -> raw_code C),
      (* (forall (r : Arit (uniform o)) (v : ℓ.π1), exists L, valid_code L fset0 (f r v)) -> *)
      ⊢ ⦃ λ '(h₀, h₁), h₀ = h₁ ⦄
        r ← sample uniform o ;;
      v ← get ℓ ;;
      f r v ≈
        c ⦃ Logic.eq ⦄ <->
        ⊢ ⦃ λ '(h₀, h₁), h₀ = h₁ ⦄
          v ← get ℓ ;;
        r ← sample uniform o ;;
        f r v ≈
          c ⦃ Logic.eq ⦄.
  Proof.
    intros ? ? ? ? ? ?.
    split.
    - intros H.
      eapply r_transR.
      1: apply H.
      apply (r_get_remember_lhs _ _ _ (fun '(H0, H1) => H0 = H1)).
      intros v.
      apply r_uniform_bij with (f := id) ; [ now apply inv_bij | intros ].
      eapply (r_get_remind_rhs _ v _ _ _) ;
        [ apply Remembers_rhs_from_tracked_lhs ;
          [ apply Remembers_lhs_conj_right
            ; apply Remembers_lhs_rem_lhs
          | apply Syncs_conj ; apply (Syncs_eq ℓ) ]
        | apply r_forget_lhs ; apply rreflexivity_rule ].
    - intros H.
      eapply r_transR.
      1: apply H.
      apply (r_get_remember_rhs _ _ _ (fun '(H0, H1) => H0 = H1)).
      intros v.
      apply r_uniform_bij with (f := id) ; [ now apply inv_bij | intros ].
      eapply (r_get_remind_lhs _ v _ _ _) ;
        [ apply Remembers_lhs_from_tracked_rhs ;
          [ apply Remembers_rhs_conj_right
            ; apply Remembers_rhs_rem_rhs
          | apply Syncs_conj ; apply (Syncs_eq ℓ) ]
        | apply r_forget_rhs ; apply rreflexivity_rule ].
  Qed.

  Lemma GK_advantage :
    forall B (C : finType) H K_loc SET GET H_disj (H_pos : Positive #|C|),
    ∀ (LA : {fset Location}) (A : raw_package),
      LA :#: fset [:: ('option B; K_loc) : Location] ->
      ValidPackage LA (fset [:: (SET, (B, 'unit)); (GET, ('unit, B))]) A_export A →
      (Advantage (GK (A := B) (B := C) H K_loc SET GET (H_disj := H_disj)) A <= 0)%R.
  Proof.
    intros.
    rewrite Advantage_E.
    replace (AdvantageE _ _ _) with (@GRing.zero R) ; [ easy | symmetry ].
    Locate eq_upto_inv_perf_ind.
    eapply eq_rel_perf_ind_eq.
    1: apply pack_valid.
    1: apply pack_valid.
    2: eassumption.
    2,3: assumption.

    unfold GK.
    unfold locs_pack, pack.
    unfold GK_raw.
    unfold K_use_raw.
    unfold K_any_package.
    unfold K_any_package_raw.
    unfold pack.

    (* unfold eq_up_to_inv. *)
    simplify_eq_rel b.
    - eapply (rpost_weaken_rule _ Logic.eq) ; [ | intros [] [] => [ [] ] // ]. 
      unfold par.
      rewrite !setmE ; rewrite eqxx.
      unfold ".2".
      repeat choice_type_eqP_handle.
      erewrite !cast_fun_K.

      simpl.

      rewrite !setmE ; rewrite eqxx.
      repeat choice_type_eqP_handle.
      erewrite !cast_fun_K.

      simpl.
      apply r_dead_sample_R ; [ apply LosslessOp_uniform | intros ].

      apply (proj2 (bobble_sample_uniform_getr (ℓ := ('option B; K_loc)) _ _ _)).
      ssprove_sync_eq => [ [ * | * ] ].
      + apply r_const_sample_L ; [ apply LosslessOp_uniform | intros ].
        now apply r_ret.
      + simpl.
        apply r_uniform_bij with (f := id) ; [ now apply inv_bij | intros ].
        apply better_r_put_rhs.
        apply better_r_put_lhs.
        apply r_ret.
        now intros ? ? [? [[? []] ?]].
    - eapply (rpost_weaken_rule _ Logic.eq) ; [ | intros [] [] => [ [] ] // ]. 
      unfold par.
      rewrite !setmE.
      apply RelationClasses.neq_Symmetric in H_disj.
      rewrite !(ssrbool.introF eqP H_disj).
      rewrite !IDE.
      rewrite <- !fset1E.
      simpl.
      rewrite !eqxx.
      simpl.
      repeat choice_type_eqP_handle.
      erewrite !cast_fun_K.

      simpl.
      rewrite !setmE ; rewrite eqxx.
      rewrite !(ssrbool.introF eqP H_disj).
      repeat choice_type_eqP_handle.
      erewrite !cast_fun_K.

      simpl.
      ssprove_sync_eq => [ [ * | * ] ] ; [ | simpl ; ssprove_sync_eq => * ] ; now apply r_ret.
  Qed.

  Definition Bound_nat := OVN_Param.N : nat.
  Lemma Bound_nat_Pos : Positive Bound_nat. Proof. apply HOP.n_pos. Qed.

  Definition SET_x (i : nat) := (Bound_nat * 0 + i)%nat.
  Definition GET_x (i : nat) := (Bound_nat * 1 + i)%nat.
  Definition LOC_x (i : nat) := (Bound_nat * 0 + i)%nat.

  Definition SET_gx (i : nat) := (Bound_nat * 2 + i)%nat.
  Definition GET_gx (i : nat) := (Bound_nat * 3 + i)%nat.
  Definition LOC_gx (i : nat) := (Bound_nat * 1 + i)%nat.

  Definition SET_zkp (i : nat) := (Bound_nat * 4 + i)%nat.
  Definition GET_zkp (i : nat) := (Bound_nat * 5 + i)%nat.
  Definition LOC_zkp (i : nat) := (Bound_nat * 2 + i)%nat.

  Definition REGISTER_VOTE_INTERFACE := 101%nat.

  Definition SET_gy (i : nat) := (Bound_nat * 6 + i)%nat.
  Definition GET_gy (i : nat) := (Bound_nat * 7 + i)%nat.
  Definition LOC_gy (i : nat) := (Bound_nat * 3 + i)%nat.

  Definition SET_v (i : nat) := (Bound_nat * 8 + i)%nat.
  Definition GET_v (i : nat) := (Bound_nat * 9 + i)%nat.
  Definition LOC_v (i : nat) := (Bound_nat * 4 + i)%nat.

  Definition SET_vote (i : nat) := (Bound_nat * 10 + i)%nat.
  Definition GET_vote (i : nat) := (Bound_nat * 11 + i)%nat.
  Definition LOC_vote (i : nat) := (Bound_nat * 5 + i)%nat.
  
  Definition SET_commit (i : nat) := (Bound_nat * 12 + i)%nat.
  Definition GET_commit (i : nat) := (Bound_nat * 13 + i)%nat.
  Definition LOC_commit (i : nat) := (Bound_nat * 6 + i)%nat.

  Definition COMMIT_TO_VOTE_INTERFACE := 102%nat.

  Definition SET_or (i : nat) := (Bound_nat * 14 + i)%nat.
  Definition GET_or (i : nat) := (Bound_nat * 15 + i)%nat.
  Definition LOC_or (i : nat) := (Bound_nat * 7 + i)%nat.

  Definition CAST_VOTE_INTERFACE := 103%nat.

  Definition SET_tally (i : nat) := (Bound_nat * 16 + i)%nat.
  Definition GET_tally (i : nat) := (Bound_nat * 17 + i)%nat.
  Definition LOC_tally (i : nat) := (Bound_nat * 8 + i)%nat.

  Definition TALLY_INTERFACE := 104%nat.

  Lemma H_disj_x : forall i, SET_x i <> GET_x i. Proof. by now unfold SET_x, GET_x, OVN_Param.N; epose proof Bound_nat_Pos; destruct Bound_nat ; easy || Lia.lia. Qed.
  Lemma H_disj_gx : forall i, SET_gx i <> GET_gx i. Proof. by now unfold SET_gx, GET_gx, OVN_Param.N; epose proof Bound_nat_Pos; destruct Bound_nat ; easy || Lia.lia. Qed.
  Lemma H_disj_zkp : forall i, SET_zkp i <> GET_zkp i. Proof. by now unfold SET_zkp, GET_zkp, OVN_Param.N; epose proof Bound_nat_Pos; destruct Bound_nat ; easy || Lia.lia. Qed.
  Lemma H_disj_v : forall i, SET_v i <> GET_v i. Proof. by now unfold SET_v, GET_v, OVN_Param.N; epose proof Bound_nat_Pos; destruct Bound_nat ; easy || Lia.lia. Qed.
  Lemma H_disj_gy : forall i, SET_gy i <> GET_gy i. Proof. by now unfold SET_gy, GET_gy, OVN_Param.N; epose proof Bound_nat_Pos; destruct Bound_nat ; easy || Lia.lia. Qed.
  Lemma H_disj_vote : forall i, SET_vote i <> GET_vote i. Proof. by now unfold SET_vote, GET_vote, OVN_Param.N; epose proof Bound_nat_Pos; destruct Bound_nat ; easy || Lia.lia. Qed.
  Lemma H_disj_commit : forall i, SET_commit i <> GET_commit i. Proof. by now unfold SET_commit, GET_commit, OVN_Param.N; epose proof Bound_nat_Pos; destruct Bound_nat ; easy || Lia.lia. Qed.
  Lemma H_disj_or : forall i, SET_or i <> GET_or i. Proof. by now unfold SET_or, GET_or, OVN_Param.N; epose proof Bound_nat_Pos; destruct Bound_nat ; easy || Lia.lia. Qed.
  Lemma H_disj_tally : forall i, SET_tally i <> GET_tally i. Proof. by now unfold SET_tally, GET_tally, OVN_Param.N; epose proof Bound_nat_Pos; destruct Bound_nat ; easy || Lia.lia. Qed.

  Definition schnorr_game := fun b =>
    if b
    then schnorr_ideal
    else schnorr_real.

  Lemma valid_link_emptyL :
    ∀ L I M E p1 p2,
      ValidPackage fset0 M E p1 →
      ValidPackage L I M p2 →
      ValidPackage L I E (link p1 p2).
  Proof.
    intros.
    rewrite <- fset0U.
    eapply valid_link ; eauto.
  Qed.

  Lemma valid_link_emptyR :
    ∀ L I M E p1 p2,
      ValidPackage L M E p1 →
      ValidPackage fset0 I M p2 →
      ValidPackage L I E (link p1 p2).
  Proof.
    intros.
    rewrite <- fsetU0.
    eapply valid_link ; eauto.
  Qed.

  Definition Gschnorr : loc_GamePair [interface #val #[ SCHNORR ] : schnorrInput → schnorrOutput] :=
    fun b => if b then {locpackage schnorr_ideal} else {locpackage schnorr_real}.
  Definition Kx i : loc_GamePair _ :=
    fun b => {locpackage KF_package (H_disj := H_disj_x i) (LOC_x i) (SET_x i) (GET_x i) b}.
  Definition Kzkp i : loc_GamePair _ :=
    fun b => {locpackage Kzkp_package (H_disj := H_disj_zkp i) (LOC_zkp i) (SET_zkp i) (GET_zkp i) b}.

  Fixpoint parallel_package_raw (p : forall (n : nat), raw_package) u : raw_package :=
    match u with
    | O => p O
    | S n => par (parallel_package_raw p n) (p (S n))
    end.
  Fixpoint combined_interfaces {T : ordType} (i : forall (n : nat), {fset T}) u : {fset T} :=
    match u with
    | O => i O
    | S n => (combined_interfaces i n) :|: (i (S n))
    end.

  Lemma parallel_package_valid : forall L I E (p : nat -> raw_package) (H : forall (n : nat), ValidPackage (L n) (I n) (E n) (p n)) u,
      ValidPackage
        (combined_interfaces L u)
        (combined_interfaces I u)
        (combined_interfaces E u)
        (parallel_package_raw p u).
  Proof.
    intros.
    induction u.
    - apply H.
    - simpl.
      apply valid_par.
      + apply ignore_Parable.
      + apply IHu.
      + apply H.
  Qed.
  Definition parallel_package {L I E} p u := {package _ #with parallel_package_valid L I E (fun i => pack (p i)) (fun i => pack_valid (p i)) u}.

  Equations parallel_package_in_raw {u : nat} (index : 'I_u) (p : forall (n : 'I_u), raw_package) : raw_package by wf (nat_of_ord index) lt :=
    parallel_package_in_raw (@Ordinal _ O i) p := p (Ordinal (m := O) i) ;
    parallel_package_in_raw (@Ordinal _ (S n) i) p := par (parallel_package_in_raw (Ordinal (m := n) (ltnW i)) p) (p (Ordinal (m := S n) i)).
  Final Obligation. easy. Defined.

  Equations combined_interfaces_in {u : nat} (index : 'I_u) {T : ordType} (i : forall (n : 'I_u), {fset T}) : {fset T} by wf (nat_of_ord index) lt :=
    combined_interfaces_in (@Ordinal _ O h) i := i (Ordinal (m := O) h) ;
    combined_interfaces_in (@Ordinal _ (S n) h) i := (combined_interfaces_in (Ordinal (m := n) (ltnW h)) i) :|: (i (Ordinal (m := S n) h)).
  Final Obligation. easy. Defined.

  Lemma parallel_package_in_valid : forall u (index : 'I_u) L I E (p : forall (n : 'I_u), package (L n) (I n) (E n)),
      ValidPackage
        (combined_interfaces_in index L)
        (combined_interfaces_in index I)
        (combined_interfaces_in index E)
        (parallel_package_in_raw index p).
  Proof.
    intros.
    destruct index.
    induction m.
    - rewrite parallel_package_in_raw_equation_1.
      apply pack_valid.
    - rewrite parallel_package_in_raw_equation_2.
      rewrite !combined_interfaces_in_equation_2.
      apply valid_par.
      + apply ignore_Parable.
      + apply IHm.
      + apply p.
  Qed.
  Definition parallel_package_in {u} (index : 'I_u) {L I E} p := {package _ #with parallel_package_in_valid u index L I E p}.

  Section Fold_rule.

    Context {A : choice_type} (I : nat → A -> precond) (N : nat).

    Context (c₀ c₁ : nat → A → raw_code A).

    Lemma fold_rule :
      (∀ i a, ⊢ ⦃ true_precond ⦄ c₀ i a ≈ c₁ i a ⦃ pre_to_post true_precond ⦄) →
      forall (a0 : A) l,
      ⊢ ⦃ true_precond ⦄
        List.fold_left (fun x y => v ← x ;; c₀ y v) (iota l N.+1) (ret a0)  ≈
        List.fold_left (fun x y => v ← x ;; c₁ y v) (iota l N.+1) (ret a0)
        ⦃ pre_to_post true_precond ⦄.
    Proof.
      intros h.
      intros a0.
      assert (forall l, ⊢ ⦃ true_precond ⦄ v ← ret a0 ;; c₀ l v ≈ v ← ret a0 ;; c₁ l v ⦃ pre_to_post true_precond ⦄) by intros => //=.
      set (ret a0) in H at 1 |- * at 1.
      set (ret a0) in H at 1 |- * at 1.
      generalize dependent r0.
      generalize dependent r.
      generalize dependent a0.
      induction N as [| n ih] ; intros.
      - simpl.
        (* rewrite addn1. *)
        apply H.
      - unfold iota ; fold (iota l.+1 n.+1).
        set (y := fun _ _ => _) ; unfold List.fold_left at 1 ; fold (List.fold_left y) ; subst y ; hnf.
        set (y := fun _ _ => _) at 2 ; unfold List.fold_left at 2 ; fold (List.fold_left y) ; subst y ; hnf.
        (* replace (_ + n.+2)%nat with (l.+1 + n.+1)%nat by Lia.lia. *)

        specialize (ih a0 (v ← r ;; c₀ l v) (v ← r0 ;; c₁ l v)).
        apply ih.
        intros.
        eapply r_bind.
        + eapply H.
        + simpl. intros.
          apply rpre_hypothesis_rule => ? ? [] * ; subst.
          intros.
          eapply rpre_weaken_rule.
          1: apply h.
          auto.
    Qed.
  End Fold_rule.

  Section Fold_rule.

    Lemma fold_valid :
      forall {A B} {L I} (f : _ -> B -> code L I A) (l : list B) (s : code L I A),
        ValidCode L I (List.fold_left f l s).
    Proof.
      induction l ; intros.
      - apply prog_valid.
      - apply IHl.
    Qed.

    Lemma fold_valid2 :
      forall {A : choiceType} {B : ordType} {L I} (f : _ -> B -> raw_code A) (l : list B) (s : raw_code A),
        (ValidCode L I s) ->
        (forall (a : code L I A) b, b \in l -> ValidCode L I (f (prog a) b)) ->
        ValidCode L I (List.fold_left f l s).
    Proof.
      induction l ; intros.
      - apply H.
      - simpl.
        apply IHl.
        + apply (H0 {code s #with H}).
          apply mem_head.
        + intros.
          apply H0.
          now apply /orP ; right.
    Qed.

  End Fold_rule.

  Lemma in_cat :
    forall (X : eqType) l1 l2, forall (x : X), (x \in (l1 ++ l2)) = ((x \in l1) || (x \in l2)).
  Proof.
    intros.
    generalize dependent l1.
    induction l2 ; intros.
    + rewrite List.app_nil_r.
      now rewrite Bool.orb_false_r.
    + replace (l1 ++ _) with ((l1 ++ [a]) ++ l2).
      2:{
        rewrite <- list.Assoc_instance_0.
        rewrite list.cons_middle.
        reflexivity.
      }
      rewrite IHl2.
      rewrite in_cons.
      induction l1.
      * simpl.
        rewrite in_cons.
        rewrite in_nil.
        now rewrite Bool.orb_false_r.
      * simpl.
        rewrite !in_cons.
        rewrite <- !orbA.
        now rewrite IHl1.
  Qed.

  (* Definition g_y_game u : loc_GamePair _ := *)
  (*   fun b => {locpackage g_yi_ideal u b #with Gdl_gx_valid_full u b}. *)

  Lemma trivial_combined_interface :
    forall (u : nat) {T : ordType} (I : {fset T}), combined_interfaces (fun _ => I) u = I.
  Proof.
    intros.
    induction u.
    - reflexivity.
    - simpl.
      rewrite IHu.
      rewrite fsetUid.
      reflexivity.
  Qed.

  Lemma trivial_combined_interface_in :
    forall {u} (m : 'I_u) {T : ordType} (I : {fset T}), combined_interfaces_in m (fun _ => I) = I.
  Proof.
    intros.
    destruct m.
    induction m.
    - now rewrite combined_interfaces_in_equation_1.
    - rewrite combined_interfaces_in_equation_2.
      rewrite IHm.
      rewrite fsetUid.
      reflexivity.
  Qed.

    Lemma package_split :
      forall p, par p p = p.
    Proof.
      intros.
      unfold par.
      now rewrite unionmI.
    Qed.

  Lemma trivial_parallel_package_raw :
    forall u (p : raw_package), parallel_package_raw (fun _ => p) u = p.
  Proof.
    intros.
    induction u.
    - reflexivity.
    - simpl.
      rewrite IHu.
      now rewrite package_split.
  Qed.

  Lemma trivial_combined_interface_to_in :
    forall {u : nat} (m : nat) (H_le : (m <= u)%nat) {T : ordType} (f : nat -> {fset T}),
      combined_interfaces f m
      = combined_interfaces_in (Ordinal (n := u.+1) (m := m) H_le) (fun i => f (nat_of_ord i)).
  Proof.
    intros.
    induction m.
    - reflexivity.
    - simpl.
      rewrite IHm.
      + Lia.lia.
      + intros.
        rewrite combined_interfaces_in_equation_2.
        f_equal.
        f_equal.
        apply ord_ext.
        reflexivity.
  Qed.

  Check fsub0set.
  Lemma fsub0Eset : ∀ {T : ordType} (s : {fset T}), fset [] :<=: s.
  Proof. intros. rewrite <- fset0E. apply fsub0set. Qed.

  Lemma fsub1Eset : ∀ {T : ordType} x (l : list T), x \in l -> fset [x] :<=: fset l.
  Proof. intros. rewrite <- fset1E. rewrite fsub1set. rewrite in_fset. apply H. Qed.

  Lemma combined_interfaces_Game_import :
    forall u, combined_interfaces (λ _ : nat, Game_import) u = Game_import.
  Proof.
    induction u.
    + reflexivity.
    + by move: IHu fsetUid => /= -> ->.
  Qed.

  Lemma Advantage_par_emptyR :
    ∀ G₀ G₁ A,
      AdvantageE (par G₀ emptym) (par G₁ emptym) A = AdvantageE G₀ G₁ A.
  Proof.
    intros G₀ G₁ A.
    unfold AdvantageE.
    unfold par.
    rewrite !unionm0.
    reflexivity.
  Qed.

  Lemma Advantage_parR :
    ∀ G₀ G₁ G₁' A L₀ L₁ L₁' E₀ E₁,
      ValidPackage L₀ Game_import E₀ G₀ →
      ValidPackage L₁ Game_import E₁ G₁ →
      ValidPackage L₁' Game_import E₁ G₁' →
      flat E₁ →
      trimmed E₀ G₀ →
      trimmed E₁ G₁ →
      trimmed E₁ G₁' →
      AdvantageE (par G₁ G₀) (par G₁' G₀) A =
        AdvantageE G₁ G₁' (A ∘ par (ID E₁) G₀).
  Proof.
    intros G₀ G₁ G₁' A L₀ L₁ L₁' E₀ E₁.
    intros Va0 Va1 Va1' Fe0 Te0 Te1 Te1'.
    replace (par G₁ G₀) with ((par (ID E₁) G₀) ∘ (par G₁ (ID Game_import) )).
    2:{
      erewrite <- interchange.
      all: ssprove_valid.
      4:{
        ssprove_valid.
        rewrite domm_ID_fset.
        rewrite -fset0E.
        apply fdisjoints0.
      }
      2:{ unfold Game_import. rewrite -fset0E. discriminate. }
      2: apply trimmed_ID.
      rewrite link_id.
      2:{ unfold Game_import. rewrite -fset0E. discriminate. }
      2: assumption.
      rewrite id_link.
      2: assumption.
      reflexivity.
    }
    replace (par G₁' G₀) with ((par (ID E₁) G₀) ∘ (par G₁' (ID Game_import))).
    2:{
      erewrite <- interchange.
      all: ssprove_valid.
      4:{
        ssprove_valid.
        rewrite domm_ID_fset.
        rewrite -fset0E.
        apply fdisjoints0.
      }
      2:{ unfold Game_import. rewrite -fset0E. discriminate. }
      2: apply trimmed_ID.
      rewrite link_id.
      2:{ unfold Game_import. rewrite -fset0E. discriminate. }
    2: assumption.
    rewrite id_link.
    2: assumption.
    reflexivity.
  }
  rewrite -Advantage_link.
  unfold Game_import. rewrite -fset0E.
  rewrite Advantage_par_emptyR.
  reflexivity.
  Unshelve. all: auto.
Qed.

    Lemma split_parallel_package_raw :
      forall u A B,
      parallel_package_raw (λ i : nat, par (A i) (B i)) u
      = par (parallel_package_raw A u) (parallel_package_raw B u).
    Proof.
      intros.
      induction u.
      - reflexivity.
      - simpl.
        rewrite IHu.
        rewrite <- par_assoc.
        setoid_rewrite (par_commut (parallel_package_raw B u)).
        2,3: apply ignore_Parable.
        rewrite !par_assoc.
        reflexivity.
    Qed.

    Lemma parallel_package_interchange_raw :
      forall u A B,
      (* forall {L I E}, *)
        (* ValidPackage L I E (parallel_package_raw A u) -> *)
        parallel_package_raw (fun i => A i ∘ B i) u =
          parallel_package_raw A u ∘ parallel_package_raw B u.
    Proof.
      intros.
      induction u.
      - reflexivity.
      - simpl.
        rewrite IHu.
        erewrite <- interchange ; [ | admit .. ].
        1: reflexivity.
    Admitted.

    Lemma parallel_package_in_interchange_raw :
      forall u n A B,
      (* forall {L I E}, *)
        (* ValidPackage L I E (parallel_package_raw A u) -> *)
        forall (H_l : (n <= u)%nat),
        parallel_package_in_raw (Ordinal (n:=u.+1) (m:=n) H_l) (fun i => A i ∘ B (nat_of_ord i)) =
          parallel_package_in_raw (Ordinal (n:=u.+1) (m:=n) H_l) A ∘ parallel_package_raw B n.
    Proof.
      intros.
      induction n0.
      - reflexivity.
      - simpl.
        rewrite !parallel_package_in_raw_equation_2.
        simpl.
        rewrite IHn0.
        erewrite <- interchange ; [ | admit .. ].
        1: reflexivity.
    Admitted.

    Lemma trim_parallel_package :
      forall {u} {E} (P : forall (i : nat), raw_package),
        (forall i, trimmed (E i) (P i)) ->
        trimmed (combined_interfaces E u) (parallel_package_raw (λ n0 : nat, P n0) u).
    Proof.
      intros.
      induction u.
      - now apply H.
      - simpl.
        apply trimmed_par.
        + apply ignore_Parable.
        + now apply IHu.
        + now apply H.
    Qed.

  Lemma Advantage_parR_parallel :
    ∀ G₀ G₁ G₁' A L₀ L₁ L₁' E₀ E₁ u,
      ValidPackage L₀ Game_import E₀ G₀ →
      (forall i, ValidPackage (L₁ i) Game_import (E₁ i) (G₁ i)) →
      (forall i, ValidPackage (L₁' i) Game_import (E₁ i) (G₁' i)) →
      (forall i, flat (E₁ i)) →
      trimmed E₀ G₀ →
      (forall i, trimmed (E₁ i) (G₁ i)) →
      (forall i, trimmed (E₁ i) (G₁' i)) →
      AdvantageE (par (parallel_package_raw G₁ u) G₀) (par (parallel_package_raw G₁' u) G₀) A =
      AdvantageE (parallel_package_raw G₁ u) (parallel_package_raw G₁' u) (A ∘ par (parallel_package_raw (fun i => ID (E₁ i)) u) G₀).
  Proof.
    intros G₀ G₁ G₁' A L₀ L₁ L₁' E₀ E₁ u.
    intros Va0 Va1 Va1' Fe0 Te0 Te1 Te1'.
    replace (par (parallel_package_raw G₁ u) G₀) with ((par (parallel_package_raw (fun i => ID (E₁ i)) u) G₀) ∘ (par (parallel_package_raw G₁ u) (ID Game_import) )).
    2:{
      erewrite <- interchange.
      2:{
        refine (parallel_package_valid _ _ _ (λ i, ID (E₁ i)) _ u).
        intros.
        apply valid_ID.
        apply Fe0.
      }
      2: apply Va0.
      2: refine (parallel_package_valid _ _ _ (fun n => (G₁ n)) _ _).
      2: apply valid_ID ; eapply flat_valid_package ; apply valid_empty_package.
      2: refine (trim_parallel_package _ _) ; intros ; apply trimmed_ID.
      2: easy.
      2: apply ignore_Parable.
      rewrite link_id.
      2:{ unfold Game_import. rewrite -fset0E. discriminate. }
      2: assumption.
      rewrite <- parallel_package_interchange_raw.
      f_equal.
      f_equal.
      apply functional_extensionality.
      intros.
      rewrite id_link.
      1: reflexivity.
      easy.
    }
    replace (par (parallel_package_raw G₁' u) G₀) with ((par (parallel_package_raw (fun i => ID (E₁ i)) u) G₀) ∘ (par (parallel_package_raw G₁' u) (ID Game_import))).
    2:{
      erewrite <- interchange.
      2:{
        refine (parallel_package_valid _ _ _ (λ i, ID (E₁ i)) _ u).
        intros.
        apply valid_ID.
        apply Fe0.
      }
      2: apply Va0.
      2: refine (parallel_package_valid _ _ _ (fun n => (G₁' n)) _ _).
      2: apply valid_ID ; eapply flat_valid_package ; apply valid_empty_package.
      2: refine (trim_parallel_package _ _) ; intros ; apply trimmed_ID.
      2: easy.
      2: apply ignore_Parable.
      rewrite link_id.
      2:{ unfold Game_import. rewrite -fset0E. discriminate. }
      2: assumption.
      rewrite <- parallel_package_interchange_raw.
      f_equal.
      f_equal.
      apply functional_extensionality.
      intros.
      rewrite id_link.
      1: reflexivity.
      easy.
    }
    rewrite -Advantage_link.
    unfold Game_import. rewrite -fset0E.
    rewrite Advantage_par_emptyR.
    reflexivity.
    Unshelve. all: auto.
  Qed.

    Lemma advantage_helper :
      forall {LA IA EA},
      forall {LB IB EB},
      forall {LK IK EK},
      forall {A : bool -> raw_package}
        {B : bool -> raw_package}
        {K : bool -> raw_package},
        fsubset IA EK ->
        fsubset IB EK ->
        fsubset IK [interface] ->
        (forall b, ValidPackage LA IA EA (A b)) ->
        (forall b, ValidPackage LB IB EB (B b)) ->
        (forall b, ValidPackage LK IK EK (K b)) ->
        (forall b, trimmed EA (A b)) ->
        (forall b, trimmed EB (B b)) ->
        (forall b, trimmed EK (K b)) ->
        forall ε ν,
          (forall Adv, (AdvantageE (A false ∘ K false) (A true ∘ K true) Adv <= ε)%R) ->
          (forall Adv, (AdvantageE (B false ∘ K false) (B true ∘ K true) Adv <= ν)%R) ->
        (forall Adv, (AdvantageE (par (A false) (B false) ∘ K false) (par (A true) (B true) ∘ K true) Adv <= ν + ε)%R).
    Proof.
      intros.
      rewrite <- (package_split (K false)).
      rewrite <- (package_split (K true)).
      erewrite <- !interchange ; [ | try (easy || apply ignore_Parable) .. ].
      2-5: eapply valid_package_inject_export ; [ | easy ] ; assumption.
      eapply Order.le_trans ; [ eapply Advantage_triangle with (R := par (A false ∘ K false) (B true ∘ K true)) | ].
      apply Num.Theory.lerD.
      {
        erewrite Advantage_par ;
          [ | (eapply valid_link || eapply flat_valid_package || apply trimmed_link) ; try easy.. ].
        2-4: eapply valid_package_inject_export ; [ | eapply valid_package_inject_import ; easy ] ; assumption.
        apply H9.
      }
      {
        erewrite Advantage_parR ;
          [ | (eapply valid_link || eapply flat_valid_package || apply trimmed_link) ; try easy.. ].
        2-4: eapply valid_package_inject_export ; [ | eapply valid_package_inject_import ; easy ] ; assumption.
        apply H8.
      }
      Unshelve. all: apply false.
    Qed.

    Corollary advantage_helper0 :
            forall {LA IA EA},
      forall {LB IB EB},
      forall {LK IK EK},
      forall {A : bool -> raw_package}
        {B : bool -> raw_package}
        {K : bool -> raw_package},
        fsubset IA EK ->
        fsubset IB EK ->
        fsubset IK [interface] ->
        (forall b, ValidPackage LA IA EA (A b)) ->
        (forall b, ValidPackage LB IB EB (B b)) ->
        (forall b, ValidPackage LK IK EK (K b)) ->
        (forall b, trimmed EA (A b)) ->
        (forall b, trimmed EB (B b)) ->
        (forall b, trimmed EK (K b)) ->
        (forall Adv, (AdvantageE (A false ∘ K false) (A true ∘ K true) Adv <= 0)%R) ->
        (forall Adv, (AdvantageE (B false ∘ K false) (B true ∘ K true) Adv <= 0)%R) ->
        (forall Adv, (AdvantageE (par (A false) (B false) ∘ K false) (par (A true) (B true) ∘ K true) Adv <= 0)%R).
    Proof. intros. rewrite <- (add0r 0%R). now rewrite advantage_helper. Qed.

    Lemma link_par_right :
      forall {LA IA EA},
      forall {LB IB EB},
      (* forall {LC IC EC}, *)
      forall {A : raw_package}
        {B : raw_package}
        {C : raw_package},
        fsubset IA EB ->
        ValidPackage LA IA EA A ->
        ValidPackage LB IB EB B ->
        (* ValidPackage LC IC EC C -> *)
        trimmed EA A ->
        A ∘ par B C = A ∘ B.
    Proof.
      intros.
      apply eq_fmap.
      unfold link.
      intro n. repeat rewrite ?mapmE.
      destruct (A n) as [[S1 [T1 f1]]|] eqn:e. 2: reflexivity.
      cbn. f_equal. f_equal. f_equal. extensionality x.
      erewrite (code_link_par_left _ _ _ _ IA) ; [ reflexivity | | eapply valid_package_inject_export ; easy ].

      eapply trimmed_valid_Some_in in e as hi ; [ | eassumption.. ].
      eapply from_valid_package in H0.
      specialize (H0 _ hi).
      destruct H0 as [g [eg hg]].
      rewrite e in eg.
      noconf eg.
      cbn in hg.
      apply hg.
    Qed.

    Lemma advantage_helper2 :
      forall {LA IA EA},
      forall {LB IB EB},
      forall {A : bool -> raw_package}
        {B : bool -> raw_package}
        {C : bool -> raw_package}
        {K : bool -> raw_package},
        fsubset IA EB ->
        (forall b, ValidPackage LA IA EA (A b)) ->
        (forall b, ValidPackage LB IB EB (B b)) ->
        (forall b, trimmed EA (A b)) ->
        (forall b, K b = par (B b) (C b)) ->
        forall ε,
        (forall Adv, (AdvantageE (A false ∘ B false) (A true ∘ B true) Adv <= ε)%R) ->
        (forall Adv, (AdvantageE (A false ∘ K false) (A true ∘ K true) Adv <= ε)%R).
    Proof.
      intros.
      subst.
      rewrite !H3.
      rewrite link_par_right ; [ | easy .. ].
      rewrite link_par_right ; [ | easy .. ].
      apply H4.
    Qed.

  Section Gschnorr_x_zkp.
    Definition SCHNORR_ (i : nat) := (Bound_nat * 18 + i)%nat.

    Program Definition schnorr_i_real i :
      package fset0
        [interface
           #val #[GET_x i] : chGETFinp → chGETFout ;
           #val #[GET_gx i] : chGETinp → chGETout ;
           #val #[SET_zkp i] : schnorrOutput → chSETORout
        ]
        [interface #val #[ SCHNORR_ i ] : 'unit → 'unit] :=
      [package
         #def #[ SCHNORR_ i ] (_ : 'unit) : 'unit
        {
          #import {sig #[ GET_x i ] : chGETFinp → chGETFout }
          as get_x ;;
          #import {sig #[ GET_gx i ] : chGETinp → chGETout }
          as get_gx ;;
          #import {sig #[ SET_zkp i ] : chSETZKPinp → chSETZKPout }
          as set_zkp ;;
          h ← get_gx Datatypes.tt ;;
          m ← get_x Datatypes.tt ;;
          r ← sample (uniform #|'Z_q|) ;; let r := WitnessToField (otf r) in
          let u := (g^+(FieldToWitness r))%g in
          c ← is_state (f_hash (t_Group := HOGaFE.GroupAndField.OVN.v_G_t_Group)
             (impl__into_vec
                (unsize
                   (box_new
                      (array_from_list [(ret_both g); (ret_both h); (ret_both u)]))))) ;;
          let z := (FieldToWitness c * FieldToWitness m + FieldToWitness r)%R in
          set_zkp (u,c,WitnessToField z)
        }
      ].
    Final Obligation.
      intros.
      ssprove_valid.
      apply valid_scheme.
      rewrite <- fset0E.
      apply (ChoiceEquality.is_valid_code (both_prog_valid _)).
    Qed.

    Definition schnorr_i_ideal i :
      package fset0
        [interface
           #val #[GET_gx i] : chGETinp → chGETout ;
           #val #[SET_zkp i] : schnorrOutput → chSETORout
        ]
        [interface #val #[ SCHNORR_ i ] : 'unit → 'unit] :=
      [package
         #def #[ SCHNORR_ i ] (_ : 'unit) : 'unit
        {
          #import {sig #[ GET_gx i ] : chGETinp → chGETout }
          as get_gx ;;
          #import {sig #[ SET_zkp i ] : chSETZKPinp → chSETZKPout }
          as set_zkp ;;
          h ← get_gx Datatypes.tt ;;
          z ← sample (uniform #|'Z_q|) ;; let z := WitnessToField (otf z) in
          c ← sample (uniform #|'Z_q|) ;; let c := WitnessToField (otf c) in
          let u := (g^+(FieldToWitness z) * (h : gT)^-(FieldToWitness c))%g in
          set_zkp (u,c,z)
        }
      ].

    Definition schnorr_i i (b : bool) :
      package fset0
        [interface
           #val #[GET_x i] : chGETFinp → chGETFout ;
           #val #[GET_gx i] : chGETinp → chGETout ;
           #val #[SET_zkp i] : schnorrOutput → chSETORout
        ]
        [interface #val #[ SCHNORR_ i ] : 'unit → 'unit].
    Proof.
      refine (if b then _ else _).
      - refine {package schnorr_i_ideal i #with valid_package_inject_import _ _ _ _ _ _ (valid_package_inject_locations _ _ _ _ _ _ _)}.
        all: solve_in_fset.
      - apply schnorr_i_real.
    Defined.

    Definition Gschnorr_i_raw i b :=
      schnorr_i i b
        ∘ (par
             (KF_package (H_disj := H_disj_x i) (LOC_x i) (SET_x i) (GET_x i) true)
             (par
                (K_package (H_disj := H_disj_gx i) (LOC_gx i) (SET_gx i) (GET_gx i) false)
                (Kzkp_package (H_disj := H_disj_zkp i) (LOC_zkp i) (SET_zkp i) (GET_zkp i) b))).

    Lemma Gschnorr_i_valid : forall i b,
        ValidPackage
          (fset [:: ('option v_Z; LOC_x i)]
                 :|: (fset [:: ('option v_G; LOC_gx i)]
                 :|: fset [:: ('option t_SchnorrZKPCommit; LOC_zkp i)]))
          [interface]
          [interface #val #[ SCHNORR_ i ] : 'unit → 'unit]
          (Gschnorr_i_raw i b).
    Proof.
      intros.
      rewrite <- fset0U.
      unfold Gschnorr_i_raw.
      refine (valid_link _ _ _ _ _ _ _ _ _).
      2:{
        rewrite <- (fsetUid [interface]).
        refine (valid_par _ _ _ _ _ _ _ _ (ignore_Parable _ _) _ _).
        rewrite <- (fsetUid [interface]).
        refine (valid_par _ _ _ _ _ _ _ _ (ignore_Parable _ _) _ _).
      }
      eapply valid_package_inject_import.
      2: apply pack_valid.
      solve_in_fset.
    Qed.

    Definition Gschnorr_x_zkp_raw u b : raw_package :=
      parallel_package
        (E := fun i => [interface #val #[ SCHNORR_ i ] : 'unit → 'unit])
        (I := _)
        (fun i => {package _ #with Gschnorr_i_valid i b}) u.

    Lemma Gschnorr_x_zkp_valid : forall u b, ValidPackage (combined_interfaces (fun i => fset [:: ('option v_Z; LOC_x i)]
                 :|: (fset [:: ('option v_G; LOC_gx i)]
                 :|: fset [:: ('option t_SchnorrZKPCommit; LOC_zkp i)])) u) Game_import
     (combined_interfaces (λ i : nat, [interface #val #[SCHNORR_ i] : 'unit → 'unit ])
        u) (Gschnorr_x_zkp_raw u b).
    Proof.
      intros.
      setoid_rewrite <- (trivial_combined_interface u [interface]).
      apply pack_valid.
    Qed.

    Definition Gschnorr_x_zkp u : loc_GamePair (combined_interfaces (fun i => [interface #val #[ SCHNORR_ i ] : 'unit → 'unit]) u) :=
      fun b => {locpackage Gschnorr_x_zkp_raw u b #with Gschnorr_x_zkp_valid u b}.

  Lemma Advantage_par_split :
    ∀ G₀ G₀' G₁ G₁' A₀ A₁ L₀ L₁ L₁' E₀ E₁,
      ValidPackage L₀ Game_import E₀ G₀ →
      ValidPackage L₀ Game_import E₀ G₀' →
      ValidPackage L₁ Game_import E₁ G₁ →
      ValidPackage L₁' Game_import E₁ G₁' →
      trimmed E₀ G₀ →
      trimmed E₀ G₀' →
      trimmed E₁ G₁ →
      trimmed E₁ G₁' →
      AdvantageE (par G₁ G₀) (par G₁' G₀') (par A₁ A₀) =
      (AdvantageE G₁ G₁' A₁ + AdvantageE G₀ G₀' A₀)%R.
  Proof.
    intros.
    admit.
  Admitted.    

    Lemma Advantage_parallel_package :
      forall u (k : _) {L E} (P : forall (i : nat) (b : bool), package (L i) [interface] (E i)),
      forall (A : nat -> raw_package),
        (forall i, ValidPackage (L i) (E i) A_export (A i)) ->
      (forall i, flat (E i)) ->
      (forall i, (i <= u)%nat -> Advantage (P i) (A i) <= k)%R ->
      (forall i b, trimmed (E i) (P i b)) ->
      (Advantage (λ b : bool, parallel_package (P^~ b) u) (parallel_package_raw A u)
       <= k *+ (u.+1))%R.
    Proof.
      intros.
      generalize dependent A.
      induction u ; intros.
      - now eapply H1.
      - rewrite Advantage_E.
        simpl.
        erewrite Advantage_par_split.
        {
          rewrite mulrSr.
          apply Num.Theory.lerD.
          2: now eapply H1. 
          {
            apply IHu.
            - intros.
              eapply H.
            - now intros ; eapply H1.
          }
        }
        * apply pack_valid.
        * apply pack_valid.
        * erewrite <- combined_interfaces_Game_import.
          apply parallel_package_valid.
          intros ; apply pack_valid.
        * erewrite <- combined_interfaces_Game_import.
          apply parallel_package_valid.
          intros ; apply pack_valid.
        * now apply H2.
        * now apply H2.
        * eapply (trim_parallel_package (u := u)) ; intros. apply H2.
        * eapply (trim_parallel_package (u := u)) ; intros. apply H2.
    Qed.

    Corollary Advantage_parallel_package0 :
      forall u {L E} (P : forall (i : nat) (b : bool), package (L i) [interface] (E i)),
      forall (A : nat -> raw_package),
        (forall i, ValidPackage (L i) (E i) A_export (A i)) ->
      (forall i, flat (E i)) ->
      (forall i, (i <= u)%nat -> Advantage (P i) (A i) <= 0)%R ->
      (forall i b, trimmed (E i) (P i b)) ->
      (Advantage (λ b : bool, parallel_package (P^~ b) u) (parallel_package_raw A u)
       <= 0)%R.
    Proof.
      intros.
      eapply Order.le_trans.
      1: now eapply Advantage_parallel_package.
      now rewrite mul0rn.
    Qed.

    Lemma Gschnorr_x_zkp_advantage :
      forall u,
      ∀ (LA : {fset Location}) (A : raw_package),
        (forall i, ValidPackage (fset [:: ('option v_Z; LOC_x i)]
     :|: (fset [:: ('option v_G; LOC_gx i)] :|: fset [:: ('option t_SchnorrZKPCommit; LOC_zkp i)])) ([interface #val #[SCHNORR_ i] : chSETBout → chSETBout ]) A_export A) →
        (Advantage (Gschnorr_x_zkp u) A <= 0)%R.
    Proof.
      intros.
      unfold Gschnorr_x_zkp, locs_pack, pack, Gschnorr_x_zkp_raw.
      rewrite <- (trivial_parallel_package_raw u A).
      eapply Advantage_parallel_package0.
      1: apply H.
      1: intros ; solve_flat.
      2:{ intros.
          unfold Gschnorr_i_raw.
          unfold schnorr_i.
          unfold pack.
          unfold schnorr_i_ideal.
          destruct b ; solve_trimmed.
          Unshelve.
          all: apply trimmed_package_cons ; apply trimmed_empty_package.
      }
      intros.
      unfold Gschnorr_i_raw.
      unfold pack.
      unfold schnorr_i.
      unfold pack.

      (* Ignore 'just' code *)
      rewrite Advantage_E.

      split_advantage (schnorr_i_ideal i
      ∘ par (KF_package (H_disj := H_disj_x i) (LOC_x i) (SET_x i) (GET_x i)  true)
          (par (K_package (H_disj := H_disj_gx i) (LOC_gx i) (SET_gx i) (GET_gx i) false)
             (Kzkp_package (H_disj := H_disj_zkp i) (LOC_zkp i) (SET_zkp i) (GET_zkp i) false))).
      {
        split_advantage (pack Schnorr_ZKP.hacspec_run).
        {
          apply: eq_rel_perf_ind_ignore.
          1: apply Gschnorr_i_valid.
          1:{ admit. (* apply Schnorr_ZKP.hacspec_run. *) }
          2:{
            unfold eq_up_to_inv.
            simplify_eq_rel inp_unit.

             (* TODO: Use markus' formalization for Sigma protocol.. *)
            admit.
          }
          all: admit.
        }
        split_advantage (pack Schnorr_ZKP.Schnorr.Sigma.RUN_interactive).
        {
          eapply Schnorr_ZKP.hacspec_vs_RUN_interactive.
          - admit.
          - admit.
        }
        admit.
      }
      {
        epose (GK
                 (A := t_SchnorrZKPCommit)
                 (fun '(u,c,z) =>
                    (g^+(otf u : 'Z_q) , (WitnessToField c) , WitnessToField z))
                 (LOC_zkp i)
                 (SET_zkp i)
                 (GET_zkp i)).

        split_advantage (pack (l false)) ; [ | split_advantage (pack (l true)) ] ; subst l.
        2:{
          apply AdvantageE_le_0.
          eapply GK_advantage.
          all: admit.
        }
        {
          unfold GK.
          unfold locs_pack, pack.
          unfold GK_raw.
          unfold Kzkp_package.

          eapply (eq_rel_perf_ind_eq (E := [interface #val #[SET_zkp i] : schnorrOutput → chSETORout])).
          1: admit.
          1: admit.
          2: admit.
          2,3: admit.

          simplify_eq_rel b.

          admit.
        }
        admit.
      }
    Admitted.

  End Gschnorr_x_zkp.

  Section Gdl_gx.
    Definition DL_i (i : nat) := (Bound_nat * 19 + i)%nat.

    Definition dl_i_real i :
      package fset0
        [interface
           #val #[GET_x i] : chGETFinp → chGETFout ;
           #val #[SET_gx i] : chSETinp → chSETout
        ]
        [interface
           #val #[ DL_i i ] : 'unit → 'unit
        ]
      :=
      [package
        #def #[ DL_i i ] (_ : 'unit) : 'unit
        {
          #import {sig #[ GET_x i ] : chGETFinp → chGETFout }
          as get_x ;;
          #import {sig #[ SET_gx i ] : chDL_Output → chSETORout }
          as set_gx ;;
          x ← get_x Datatypes.tt ;;
          set_gx (g ^+ FieldToWitness x)
        }
      ].

  Definition dl_i_ideal i :
    package fset0
      [interface
         #val #[SET_gx i] : chSETinp → chSETout
      ]
      [interface
         #val #[ DL_i i ] : 'unit → 'unit
      ]
    :=
    [package
        #def #[ DL_i i ] (_ : 'unit) : 'unit
        {
          #import {sig #[ SET_gx i ] : chDL_Output → chSETORout }
          as set_gx ;;
          xi ← sample (uniform #|'Z_q|) ;; let xi := WitnessToField (otf xi) in
          set_gx (g ^+ FieldToWitness xi)
        }
    ].

    Definition dl_i i (b : bool) :
      package fset0
        [interface
           #val #[GET_x i] : chGETFinp → chGETFout ;
           #val #[SET_gx i] : chSETinp → chSETout
        ]
        [interface #val #[ DL_i i ] : 'unit → 'unit].
    Proof.
      refine (if b then _ else _).
      - refine {package dl_i_ideal i #with valid_package_inject_import _ _ _ _ _ _ (valid_package_inject_locations _ _ _ _ _ _ _)}.
        all: solve_in_fset.
      - apply dl_i_real.
    Defined.

    Definition Gdl_i_raw i b :=
      (dl_i i b) ∘ (par
                      (KF_package (H_disj := H_disj_x i) (LOC_x i) (SET_x i) (GET_x i) b)
                      (K_package (H_disj := H_disj_gx i) (LOC_gx i) (SET_gx i) (GET_gx i) b)).

    Lemma Gdl_i_valid :
      forall i b,
        ValidPackage
          (fset [:: ('option v_Z; LOC_x i)] :|: fset [:: ('option v_G; LOC_gx i)])
          [interface]
          [interface #val #[ DL_i i ] : 'unit → 'unit]
          (Gdl_i_raw i b).
    Proof.
      intros.
      unfold Gdl_i_raw.
      rewrite <- fset0U.
      eapply valid_link.
      2:{
        rewrite <- (fsetUid [interface]).
        apply valid_par ; [ apply ignore_Parable | apply pack_valid .. ].
      }
      eapply valid_package_inject_import.
      2: apply pack_valid.
      solve_in_fset.
    Qed.

    Definition Gdl_raw u b := parallel_package (fun i => {package _ #with Gdl_i_valid i b}) u.

    Lemma Gdl_valid :
      forall u b,
        ValidPackage
          (combined_interfaces (fun i => fset [:: ('option v_Z; LOC_x i)] :|: fset [:: ('option v_G; LOC_gx i)]) u)
          [interface]
          (combined_interfaces (fun i => [interface #val #[ DL_i i ] : 'unit → 'unit]) u)
          (Gdl_raw u b).
    Proof.
      intros.
      setoid_rewrite <- (trivial_combined_interface u [interface]).
      apply pack_valid.
    Qed.

    Definition Gdl_gx u : loc_GamePair _ :=
      fun b => {locpackage Gdl_raw u b #with Gdl_valid u b}.

    Lemma Gdl_gx_advantage :
      forall u,
      ∀ (LA : {fset Location}) (A : raw_package),
        ValidPackage LA (combined_interfaces (fun i => [interface #val #[DL_i i] : 'unit → 'unit ]) u) A_export A →
        (Advantage (Gdl_gx u) A <= 0)%R.
    Proof.
      intros.
    Admitted.

  End Gdl_gx.

  Section Gg_y.
    Definition GPOWY (i : nat) := (Bound_nat * 20 + i)%nat.

    Program Definition g_yi_real i u `{_ : (i <= u)%nat}:
      package fset0
        (combined_interfaces (λ i : nat, [interface #val #[SET_gx i] : chDL_Output → chSETORout ; #val #[GET_gx i] : chSETORout → chDL_Output ]) u
           :|: [interface #val #[SET_gy i] : chDL_Output → chSETORout ])
        [interface
           #val #[ GPOWY i ] : 'unit → 'unit
        ]
      :=
      [package
         #def #[ GPOWY i ] (_ : 'unit) : 'unit
         {
           #import {sig #[ SET_gy i ] : chDL_Output → chSETORout }
           as set_gy ;;
           prod1 ← List.fold_left
             (fun c j =>
                p ← c ;;
                #import {sig #[ GET_gx j ] : chSETORout → chDL_Output }
                as get_g_xj ;;
                g_xj ← get_g_xj Datatypes.tt ;;
                ret ((p * (g_xj : gT))%g)) (iota 0 i) (ret (g^+0 : v_G)) ;;
           prod2 ← List.fold_left
             (fun c j =>
                p ← c ;;
                #import {sig #[ GET_gx j ] : chSETORout → chDL_Output }
                as get_g_xj ;;
                g_xj ← get_g_xj Datatypes.tt ;;
                ret ((p * (g_xj : gT))%g)) (iota i (u-(i+1))) (ret (g^+0 : v_G)) ;;
           set_gy (prod1 * (prod2 ^-1))%g
         }
      ].
    Next Obligation.
      intros.
      ssprove_valid.
      - apply fold_valid2.
        + ssprove_valid.
        + intros.
          ssprove_valid.
          * apply prog_valid. 
          * clear -H H0.
            assert (b <= u)%nat by now rewrite mem_iota in H0 ; Lia.lia.
            clear -H1.
            rewrite in_fset.
            rewrite in_cat.
            apply /orP ; left.
            simpl.
            induction u.
            -- destruct b ; [ | discriminate ].
               simpl.
               rewrite in_fset.
               rewrite !in_cons.
               apply /orP ; right.
               now apply /orP ; left.
            -- rewrite in_fset.
               rewrite in_cat.
               apply /orP.
               destruct (b == u.+1) eqn:b_eq.
               ++ move /eqP : b_eq ->.
                  right.
                  rewrite in_fset.
                  rewrite !in_cons.
                  apply /orP ; right.
                  now apply /orP ; left.
               ++ left.
                  simpl.
                  apply IHu.
                  move /eqP : b_eq.
                  Lia.lia.
      - apply fold_valid2.
        + ssprove_valid.
        + intros.
          ssprove_valid.
          * apply prog_valid. 
          * clear -H H0.
            assert (b <= u)%nat by now rewrite mem_iota in H0 ; Lia.lia.
            clear -H1.
            rewrite in_fset.
            rewrite in_cat.
            apply /orP ; left.
            simpl.
            induction u.
            -- destruct b ; [ | discriminate ].
               simpl.
               rewrite in_fset.
               rewrite !in_cons.
               apply /orP ; right.
               now apply /orP ; left.
            -- rewrite in_fset.
               rewrite in_cat.
               apply /orP.
               destruct (b == u.+1) eqn:b_eq.
               ++ move /eqP : b_eq ->.
                  right.
                  rewrite in_fset.
                  rewrite !in_cons.
                  apply /orP ; right.
                  now apply /orP ; left.
               ++ left.
                  simpl.
                  apply IHu.
                  move /eqP : b_eq.
                  Lia.lia.
      - rewrite in_fset.
        rewrite in_cat.
        apply /orP ; right.
        simpl.
        rewrite in_fset.
        rewrite in_cons.
        now apply /orP ; left.
    Qed.
    Fail Next Obligation.

    Definition g_yi_ideal i :
      package fset0
        [interface #val #[SET_gy i] : chDL_Output → chSETORout ]
        [interface
           #val #[ GPOWY i ] : 'unit → 'unit
        ]
      :=
      [package
         #def #[ GPOWY i ] (_ : 'unit) : 'unit
         {
           #import {sig #[ SET_gy i ] : chDL_Output → chSETORout }
           as set_gy ;;
           xi ← sample (uniform #|'Z_q|) ;; let xi := WitnessToField (otf xi) in
           set_gy (g ^+ FieldToWitness xi)%g
         }
      ].

    Definition g_yi u (i : 'I_u.+1) (b : bool) :
      package fset0
        (combined_interfaces (λ i : nat, [interface #val #[SET_gx i] : chDL_Output → chSETORout ; #val #[GET_gx i] : chSETORout → chDL_Output ]) u
           :|: [interface #val #[SET_gy i] : chDL_Output → chSETORout ])
        [interface
           #val #[ GPOWY i ] : 'unit → 'unit
        ].
    Proof.
      refine (if b then _ else _).
      - refine {package g_yi_ideal i #with valid_package_inject_import _ _ _ _ _ _ _}.
        solve_in_fset.
      - apply g_yi_real.
        apply (ltn_ord i).
    Qed.

    Definition Kgxs u b :=
      (parallel_package
         (L := fun i => (fset [:: ('option v_G; LOC_gx i)]) :|: (fset [:: ('option v_G; LOC_gy i)]))
         (I := fun _ => [interface] :|: [interface])
         (E := fun i => [interface
                      #val #[SET_gx i] : chDL_Output → chSETORout ;
                      #val #[GET_gx i] : chSETORout → chDL_Output ] :|: [interface
                      #val #[SET_gy i] : chDL_Output → chSETORout ;
                      #val #[GET_gy i] : chSETORout → chDL_Output ])
         (fun i => {package par (K_package (H_disj := H_disj_gx i) (LOC_gx i) (SET_gx i) (GET_gx i) b) (K_package (H_disj := H_disj_gy i) (LOC_gy i) (SET_gy i) (GET_gy i) b) #with valid_par _ _ _ _ _ _ _ _ (ignore_Parable _ _) _ _} )
         u).

    Definition Gg_y_raw (u : nat) (b : bool) : raw_package :=
      (parallel_package_in
         (u := S u)
         (Ordinal (n := S u) (m := u) (ltnSn u))
         (L := fun i => fset0)
         (I := fun i =>
                 (combined_interfaces
                    (λ j : nat,
                        [interface #val #[SET_gx j] : chDL_Output → chSETORout ;
                         #val #[GET_gx j] : chSETORout → chDL_Output ]) u) :|: [interface #val #[SET_gy i] : chDL_Output → chSETBout ])
         (E := fun i => [interface #val #[ GPOWY i ] : 'unit → 'unit])
         (fun i => {package g_yi u i b #with valid_package_inject_import _ _ _ _ _ (fsetUS _ (fsubsetxx _)) _}) ∘ Kgxs u b).

    Lemma Gg_y_valid : forall u b,
        ValidPackage
          (combined_interfaces (fun i => fset [:: ('option v_G; LOC_gx i)] :|: fset [:: ('option v_G; LOC_gy i) : Location]) u)
          [interface]
          (combined_interfaces (λ i, [interface #val #[GPOWY i] : 'unit → 'unit ]) u)
          (Gg_y_raw u b).
    Proof.
      intros.
      unfold Gg_y_raw.
      rewrite <- fsetUid.
      eapply valid_link.
      2:{
        setoid_rewrite <- (fsetUid [interface]).
        setoid_rewrite <- (trivial_combined_interface u ([interface] :|: [interface])).
        apply pack_valid.
      }
      {
        setoid_rewrite (trivial_combined_interface_to_in (u := u) u (ltnSn u) (λ i : nat, fset [:: ('option v_G; LOC_gx i)] :|: fset [:: ('option v_G; LOC_gy i)])).
        setoid_rewrite (trivial_combined_interface_to_in (u := u) u (ltnSn u) (λ i : nat, [interface #val #[GPOWY i] : chSETBout → chSETBout ])).
        setoid_rewrite <- (trivial_combined_interface_in (Ordinal (n:=u.+1) (m:=u) (ltnSn u)) (combined_interfaces _ _)).
        set (parallel_package_in _ _).
        epose proof (pack_valid p).

        refine (valid_package_inject_locations _ _ _ _ _ _ _).
        2:{
          refine (valid_package_inject_import _ _ _ _ _ _ _).
          simpl.
          clear.
          destruct Ordinal.
          induction m.
          - rewrite !combined_interfaces_in_equation_1.
            simpl.
            clear.
            rewrite fsubUset.
            apply /andP ; split.
            + induction u.
              * simpl.
                solve_in_fset.
              * simpl.
                rewrite fsubUset.
                apply /andP ; split ; apply fsubsetU ; apply /orP ; [ left | right ].
                -- apply IHu.
                -- solve_in_fset.
            + induction u.
              * simpl.
                solve_in_fset.
              * simpl.
                apply fsubsetU ; apply /orP ; left.
                apply IHu.
          - rewrite !combined_interfaces_in_equation_2.
            simpl.
            rewrite fsubUset.
            apply /andP ; split.
            + apply fsubsetU ; apply /orP ; left.
              apply IHm.
            + apply fsubsetU ; apply /orP ; right.
              clear -i.

              rewrite fsubUset ; apply /andP ; split.
              1:{
                clear.
                induction u.
                - simpl.
                  apply fsubsetUl.
                - simpl.
                  rewrite fsubUset ; apply /andP ; split; apply fsubsetU ; apply /orP ; [ left | right ].
                  + apply IHu.
                  + solve_in_fset.
              }
              1:{
                destruct (m == u) eqn:m_is_u ; move /eqP: m_is_u => m_is_u.
                - subst.
                  exfalso.
                  Lia.lia.
                - generalize dependent m.
                  induction u ; intros ; [ discriminate | ].
                  simpl.
                  destruct (m == u) eqn:m_is_u2 ; move /eqP: m_is_u2 => m_is_u2 ; apply fsubsetU ; apply /orP ; [ right | left ].
                  + subst.
                    clear.
                    solve_in_fset.
                  + apply IHu.
                    * Lia.lia.
                    * easy.
              }
        }
        destruct Ordinal.
        induction m.
        - rewrite !combined_interfaces_in_equation_1.
          apply fsub0set.
        - rewrite !combined_interfaces_in_equation_2.
          rewrite fsetU0.
          apply fsubsetU ; apply /orP ; left.
          apply IHm.

          apply pack_valid.
      }
    Qed.

    Definition Gg_y u : loc_GamePair (combined_interfaces (λ i, [interface #val #[GPOWY i] : chSETBout → chSETBout ]) u) :=
      fun b => {locpackage Gg_y_raw u b #with Gg_y_valid u b}.

    Lemma Gg_y_advantage :
      forall u,
      ∀ (LA : {fset Location}) (A : raw_package),
        ValidPackage LA (combined_interfaces (fun i => [interface #val #[GPOWY i] : 'unit → 'unit ]) u) A_export A →
        (Advantage (Gg_y u) A <= 0)%R.
    Proof.
      intros.
    Admitted.

  End Gg_y.

  Section Gvote.
    Definition VOTE (i : nat) := (Bound_nat * 21 + i)%nat.

    Definition g_vote_i_real i :
      package fset0
        [interface
           #val #[GET_gy i] : chSETORout → chDL_Output ;
           #val #[GET_x i] : chSETORout → chCommitOutput ;
           #val #[GET_v i] : 'unit → 'bool ;
           #val #[SET_vote i] : chSETinp → chSETout
        ]
        [interface
           #val #[ VOTE i ] : 'unit → 'unit
        ] :=
      [package
         #def #[ VOTE i ] (_ : 'unit) : 'unit
         {
           #import {sig #[ GET_gy i ] : chGETinp → chGETout }
           as get_gy ;;
           #import {sig #[ GET_x i ] : chGETFinp → chGETFout }
           as get_x ;;
           #import {sig #[ GET_v i ] : chGETBinp → chGETBout }
           as get_v ;;
           #import {sig #[ SET_vote i ] : chSETinp → chSETout }
           as set_vote ;;
           g_yi ← get_gy Datatypes.tt ;;
           xi ← get_x Datatypes.tt ;;
           vi ← get_v Datatypes.tt ;;
           set_vote ((g_yi : gT) ^+ (FieldToWitness xi) * (if vi then g else 1))%g
         }
      ].

    Definition g_vote_i_ideal i :
      package fset0
        [interface
           #val #[SET_vote i] : chSETinp → chSETout
        ]
        [interface
           #val #[ VOTE i ] : 'unit → 'unit
        ]
      :=
      [package
         #def #[ VOTE i ] (_ : 'unit) : 'unit
         {
           #import {sig #[ SET_vote i ] : chSETinp → chSETout }
           as set_vote ;;
           z ← sample (uniform #|'Z_q|) ;; let z := WitnessToField (otf z) in
           set_vote (g ^+ FieldToWitness z)%g
         }
      ].

    Definition g_vote_i i (b : bool) :
      package fset0
        [interface
           #val #[GET_gy i] : chSETORout → chDL_Output ;
           #val #[GET_x i] : chSETORout → chCommitOutput ;
           #val #[GET_v i] : 'unit → 'bool ;
           #val #[SET_vote i] : chSETinp → chSETout
        ]
        [interface
           #val #[ VOTE i ] : 'unit → 'unit
        ].
    Proof.
      refine (if b then _ else _).
      - refine {package g_vote_i_ideal i #with valid_package_inject_import _ _ _ _ _ _ _}.
        solve_in_fset.
      - apply g_vote_i_real.
    Defined.

    Definition Gvote_i_raw i (b : bool) : raw_package :=
      (g_vote_i i b)
        ∘ (par
             (K_package (H_disj := H_disj_gy i) (LOC_gy i) (SET_gy i) (GET_gy i) b)
             (par
                (KF_package (H_disj := H_disj_x i) (LOC_x i) (SET_x i) (GET_x i) b)
                (par
                   (KB_package (H_disj := H_disj_v i) (LOC_v i) (SET_v i) (GET_v i) b)
                   (K_package (H_disj := H_disj_vote i) (LOC_vote i) (SET_vote i) (GET_vote i) b)))).

    Lemma Gvote_i_valid : forall i b,
        ValidPackage
          (fset [:: ('option v_G; LOC_gy i)]
             :|: (fset [:: ('option v_Z; LOC_x i)]
             :|: (fset [:: ('option 'bool; LOC_v i)]
             :|: fset [:: ('option v_G; LOC_vote i)])))
          (fset [::])
          [interface #val #[VOTE i] : chSETBout → chSETBout ]
          (Gvote_i_raw i b).
    Proof.
      intros.
      unfold Gvote_i_raw.
      rewrite <- fset0U.
      eapply valid_link ; [ apply pack_valid | .. ].

      rewrite (fset_cons (_ i, _)).
      rewrite fset1E.
      rewrite <- (fsetUid [interface]).
      apply valid_par ; [ apply ignore_Parable | eapply valid_package_inject_export ; [ | apply pack_valid] ; solve_in_fset | .. ].

      rewrite (fset_cons (_ i, _)).
      rewrite fset1E.
      rewrite <- (fsetUid [interface]).
      apply valid_par ; [ apply ignore_Parable | eapply valid_package_inject_export ; [ | apply pack_valid] ; solve_in_fset | .. ].

      rewrite (fset_cons (_ i, _)).
      rewrite fset1E.
      rewrite <- (fsetUid [interface]).
      apply valid_par ; [ apply ignore_Parable | eapply valid_package_inject_export ; [ | apply pack_valid] ; solve_in_fset | .. ].

      eapply valid_package_inject_export ; [ | apply pack_valid] ; solve_in_fset.
    Qed.

    Lemma Gvote_valid :
      ∀ (u : nat) (b : bool),
    ValidPackage
      (combined_interfaces
           (fun i =>
              fset [:: ('option v_G; LOC_gy i)]
                :|: (fset [:: ('option v_Z; LOC_x i)]
                       :|: (fset [:: ('option 'bool; LOC_v i)]
                              :|: fset [:: ('option v_G; LOC_vote i)]))) u)
        [interface]
        (combined_interfaces (λ i, [interface #val #[VOTE i] : chSETBout → chSETBout ]) u)
        (parallel_package (fun i => {package Gvote_i_raw i b #with Gvote_i_valid i b}) u).
    Proof.
      intros.
      setoid_rewrite <- (trivial_combined_interface _ [interface]).
      apply pack_valid.
    Qed.

    Definition Gvote (u : nat) : loc_GamePair (combined_interfaces (λ i, [interface #val #[VOTE i] : chSETBout → chSETBout ]) u) :=
      fun b => {locpackage (parallel_package (fun i => {package Gvote_i_raw i b #with Gvote_i_valid i b}) u) #with Gvote_valid u b}.

    Lemma Gvote_advantage :
      forall u,
      ∀ (LA : {fset Location}) (A : raw_package),
        ValidPackage LA (combined_interfaces (fun i => [interface #val #[VOTE i] : 'unit → 'unit ]) u) A_export A →
        (Advantage (Gvote u) A <= 0)%R.
    Proof.
      intros.
    Admitted.

  End Gvote.

  Section Gcommit.
    Definition COMMIT_VOTE (i : nat) := (Bound_nat * 22 + i)%nat.

    Program Definition g_commit_i_real i :
      package fset0
        [interface
           #val #[GET_vote i] : chGETinp → chGETout ;
           #val #[SET_commit i] : chSETFinp → chSETFout
        ]
        [interface
           #val #[ COMMIT_VOTE i ] : 'unit → 'unit
        ] :=
      [package
         #def #[ COMMIT_VOTE i ] (_ : 'unit) : 'unit
         {
           #import {sig #[ GET_vote i ] : chGETinp → chGETout }
           as get_vote ;;
           #import {sig #[ SET_commit i ] : chSETFinp → chSETFout }
           as set_commit ;;
           vote_i ← get_vote Datatypes.tt ;;
           commit_i ← is_state (f_hash (t_Group := HOGaFE.GroupAndField.OVN.v_G_t_Group)
             (impl__into_vec
                (unsize
                   (box_new
                      (array_from_list [(ret_both vote_i)]))))) ;;
           set_commit commit_i
         }
      ].
    Final Obligation.
      intros.
      ssprove_valid_package.
      ssprove_valid.
      apply valid_scheme.
      rewrite <- fset0E.
      apply (ChoiceEquality.is_valid_code (both_prog_valid _)).
    Qed.

    Definition g_commit_i_ideal i :
      package fset0
        [interface
           #val #[SET_commit i] : chSETFinp → chSETFout
        ]
        [interface
           #val #[ COMMIT_VOTE i ] : 'unit → 'unit
        ]
      :=
      [package
         #def #[ COMMIT_VOTE i ] (_ : 'unit) : 'unit
         {
           #import {sig #[ SET_commit i ] : chSETFinp → chSETFout }
           as set_commit ;;
           z ← sample (uniform #|'Z_q|) ;; let z := WitnessToField (otf z) in
           set_commit z
         }
      ].

    Definition g_commit_i i (b : bool) :
      package fset0
        [interface
           #val #[GET_vote i] : chSETORout → chDL_Output ;
           #val #[SET_commit i] : chSETFinp → chSETFout
        ]
        [interface
           #val #[ COMMIT_VOTE i ] : 'unit → 'unit
        ].
    Proof.
      refine (if b then _ else _).
      - refine {package g_commit_i_ideal i #with valid_package_inject_import _ _ _ _ _ _ _}.
        solve_in_fset.
      - apply g_commit_i_real.
    Qed.

    Definition Gcommit_i_raw i (b : bool) : raw_package :=
      (g_commit_i i b)
        ∘ (par
             (K_package (H_disj := H_disj_vote i) (LOC_vote i) (SET_vote i) (GET_vote i) b)
             (KF_package (H_disj := H_disj_commit i) (LOC_commit i) (SET_commit i) (GET_commit i) b)).

    Lemma Gcommit_i_valid : forall i b,
        ValidPackage
          (fset [:: ('option v_G; LOC_vote i)]
             :|: fset [:: ('option v_Z; LOC_commit i)])
          (fset [::])
          [interface #val #[COMMIT_VOTE i] : chSETBout → chSETBout ]
          (Gcommit_i_raw i b).
    Proof.
      intros.
      unfold Gcommit_i_raw.
      rewrite <- fset0U.
      eapply valid_link ; [ apply pack_valid | .. ].

      rewrite (fset_cons (_ i, _)).
      rewrite fset1E.
      rewrite <- (fsetUid [interface]).
      apply valid_par ; [ apply ignore_Parable | eapply valid_package_inject_export ; [ | apply pack_valid] ; solve_in_fset | .. ].

      eapply valid_package_inject_export ; [ | apply pack_valid] ; solve_in_fset.
    Qed.

    Lemma Gcommit_valid :
      ∀ (u : nat) (b : bool),
    ValidPackage
      (combined_interfaces
           (fun i =>
              (fset [:: ('option v_G; LOC_vote i)]
             :|: fset [:: ('option v_Z; LOC_commit i)])) u)
        [interface]
        (combined_interfaces (λ i, [interface #val #[COMMIT_VOTE i] : chSETBout → chSETBout ]) u)
        (parallel_package (fun i => {package Gcommit_i_raw i b #with Gcommit_i_valid i b}) u).
    Proof.
      intros.
      setoid_rewrite <- (trivial_combined_interface _ [interface]).
      apply pack_valid.
    Qed.

    Definition Gcommit (u : nat) : loc_GamePair (combined_interfaces (λ i, [interface #val #[COMMIT_VOTE i] : chSETBout → chSETBout ]) u) :=
      fun b => {locpackage (parallel_package (fun i => {package Gcommit_i_raw i b #with Gcommit_i_valid i b}) u) #with Gcommit_valid u b}.

    Lemma Gcommit_advantage :
      forall u,
      ∀ (LA : {fset Location}) (A : raw_package),
        ValidPackage LA (combined_interfaces (fun i => [interface #val #[COMMIT_VOTE i] : 'unit → 'unit ]) u) A_export A →
        (Advantage (Gcommit u) A <= 0)%R.
    Proof.
      intros.
    Admitted.

  End Gcommit.

  Section G_CDS.
    Definition OR (i : nat) := (Bound_nat * 23 + i)%nat.

    Definition g_cds_i_real i :
      package fset0
        [interface
           #val #[GET_x i] : chGETFinp → chGETFout ;
           #val #[GET_gx i] : chGETinp → chGETout ;
           #val #[GET_v i] : chGETBinp → chGETBout ;
           #val #[SET_or i] : chSETORinp → chSETORout
        ]
        [interface
           #val #[ OR i ] : 'unit → 'unit
        ].
      refine [package
         #def #[ OR i ] (_ : 'unit) : 'unit
         {
           #import {sig #[ GET_x i ] : chGETFinp → chGETFout }
           as get_x ;;
           #import {sig #[ GET_gx i ] : chGETinp → chGETout }
           as get_gx ;;
           #import {sig #[ GET_v i ] : chGETBinp → chGETBout }
           as get_v ;;
           #import {sig #[ SET_or i ] : chSETORinp → chSETORout }
           as set_or ;;
           xi ← get_x Datatypes.tt ;;
           h ← get_gx Datatypes.tt ;;
           vi ← get_v Datatypes.tt ;;
           let x := (g ^+ FieldToWitness xi) in
           let h := (h : gT) in
           let y := (h ^+ FieldToWitness xi * g ^+ (vi : bool))%g in
           let m := FieldToWitness xi in
           w ← sample uniform #|'Z_q| ;;
           d ← sample uniform #|'Z_q| ;;
           r ← sample uniform #|'Z_q| ;;
           if vi
           then
             (
               let r1 := r in
               let d1 := d in

               let a1 := (g ^+ (otf r1 : 'Z_q) * x ^+ (otf d1 : 'Z_q))%g in
               let b1 := (h ^+ (otf r1 : 'Z_q) * y ^+ (otf d1 : 'Z_q))%g in

               let a2 := (g ^+ (otf w : 'Z_q))%g in
               let b2 := (h ^+ (otf w : 'Z_q))%g in

               c ← is_state (f_hash (t_Group := HOGaFE.GroupAndField.OVN.v_G_t_Group)
             (impl__into_vec
                (unsize
                   (box_new
                      (array_from_list [(ret_both x)]))))) ;;
               let c := FieldToWitness c in

               let d2 := ( c - otf d)%R in
               let r2 := (otf w - (m * d2))%R in

               set_or (
                   x, y,
                   a1, b1, a2, b2,
                   WitnessToField c ,
                   WitnessToField (otf r1), WitnessToField (otf d), WitnessToField r2, WitnessToField d2))
           else
             (let r2 := r in
              let d2 := d in

              let a1 := (g ^+ (otf w : 'Z_q))%g in
              let b1 := (h ^+ (otf w : 'Z_q))%g in

              let a2 := (g ^+ (otf r2 : 'Z_q) * x ^+ (otf d2 : 'Z_q))%g in
              let b2 := (h ^+ (otf r2 : 'Z_q) * (y * g^-1) ^+ (otf d2 : 'Z_q))%g in

               c ← is_state (f_hash (t_Group := HOGaFE.GroupAndField.OVN.v_G_t_Group)
             (impl__into_vec
                (unsize
                   (box_new
                      (array_from_list [ret_both x; ret_both y; ret_both a1; ret_both b1; ret_both a2; ret_both b2]))))) ;;
               let c := FieldToWitness c in

               let d1 := (c - otf d)%R in
               let r1 := (otf w - (m * d1))%R in

              set_or (
                   x, y,
                   a1, b1, a2, b2,
                   WitnessToField c ,
                   WitnessToField r1, WitnessToField (otf d), WitnessToField (otf r2), WitnessToField (otf d2)))
         }
        ].
      ssprove_valid.
      - apply valid_scheme.
        rewrite <- fset0E.
        apply (ChoiceEquality.is_valid_code (both_prog_valid _)).
      - apply valid_scheme.
        rewrite <- fset0E.
        apply (ChoiceEquality.is_valid_code (both_prog_valid _)).
        Unshelve.
        all: exact Zq_pos.
    Defined.

    Definition g_cds_i_ideal i :
      package fset0
        [interface
           #val #[SET_or i] : chSETORinp → chSETORout
        ]
        [interface
           #val #[ OR i ] : 'unit → 'unit
        ]
      :=
      [package
         #def #[ OR i ] (_ : 'unit) : 'unit
         {
           #import {sig #[ SET_or i ] : chSETORinp → chSETORout }
           as set_cds ;;
                       
         ret ((x,y,
                a1,b1,a2,b2,
                WitnessToField (otf c),
                WitnessToField d1,WitnessToField d2,WitnessToField r1,WitnessToField r2)
             : t_OrZKPCommit)

           z ← sample (uniform #|'Z_q|) ;; let z := WitnessToField (otf z) in
           set_cds z
         }
      ].

    Definition g_cds_i i (b : bool) :
      package fset0
        [interface
           #val #[GET_x i] : chGETFinp → chGETFout ;
           #val #[GET_gx i] : chGETinp → chGETout ;
           #val #[GET_v i] : chGETBinp → chGETBout ;
           #val #[SET_or i] : chSETORinp → chSETORout
        ]
        [interface
           #val #[ OR i ] : 'unit → 'unit
        ].
    Proof.
      refine (if b then _ else _).
      - refine {package g_cds_i_ideal i #with valid_package_inject_import _ _ _ _ _ _ _}.
        solve_in_fset.
      - apply g_cds_i_real.
    Qed.

    Definition Gcds_i_raw i (b : bool) : raw_package :=
      (g_cds_i i b)
        ∘ (par
             (K_package (H_disj := H_disj_vote i) (LOC_vote i) (SET_vote i) (GET_vote i) b)
             (KF_package (H_disj := H_disj_cds i) (LOC_cds i) (SET_cds i) (GET_cds i) b)).

    Lemma Gcds_i_valid : forall i b,
        ValidPackage
          (fset [:: ('option v_G; LOC_vote i)]
             :|: fset [:: ('option v_Z; LOC_cds i)])
          (fset [::])
          [interface #val #[CDS_VOTE i] : chSETBout → chSETBout ]
          (Gcds_i_raw i b).
    Proof.
      intros.
      unfold Gcds_i_raw.
      rewrite <- fset0U.
      eapply valid_link ; [ apply pack_valid | .. ].

      rewrite (fset_cons (_ i, _)).
      rewrite fset1E.
      rewrite <- (fsetUid [interface]).
      apply valid_par ; [ apply ignore_Parable | eapply valid_package_inject_export ; [ | apply pack_valid] ; solve_in_fset | .. ].

      eapply valid_package_inject_export ; [ | apply pack_valid] ; solve_in_fset.
    Qed.

    Lemma Gcds_valid :
      ∀ (u : nat) (b : bool),
    ValidPackage
      (combined_interfaces
           (fun i =>
              (fset [:: ('option v_G; LOC_vote i)]
             :|: fset [:: ('option v_Z; LOC_cds i)])) u)
        [interface]
        (combined_interfaces (λ i, [interface #val #[CDS_VOTE i] : chSETBout → chSETBout ]) u)
        (parallel_package (fun i => {package Gcds_i_raw i b #with Gcds_i_valid i b}) u).
    Proof.
      intros.
      setoid_rewrite <- (trivial_combined_interface _ [interface]).
      apply pack_valid.
    Qed.

    Definition Gcds (u : nat) : loc_GamePair (combined_interfaces (λ i, [interface #val #[CDS_VOTE i] : chSETBout → chSETBout ]) u) :=
      fun b => {locpackage (parallel_package (fun i => {package Gcds_i_raw i b #with Gcds_i_valid i b}) u) #with Gcds_valid u b}.

    Lemma Gcds_advantage :
      forall u,
      ∀ (LA : {fset Location}) (A : raw_package),
        ValidPackage LA (combined_interfaces (fun i => [interface #val #[CDS_VOTE i] : 'unit → 'unit ]) u) A_export A →
        (Advantage (Gcds u) A <= 0)%R.
    Proof.
      intros.
    Admitted.
    
    (* fail. (* TODO *) *)
  End G_CDS.

  Section G_register.
    (* REGISTER_VOTE_INTERFACE *)
    Definition REGISTER (i : nat) := (Bound_nat * 24 + i)%nat.

    Definition register_i i :
      package fset0
        [interface
           #val #[SET_x i] : chSETFinp → chSETFout ;
           #val #[SCHNORR_ i] : 'unit → 'unit ;
           #val #[DL_i i] : 'unit → 'unit
        ]
        [interface
           #val #[ REGISTER i ] : 'unit → 'unit
        ] :=
      [package
         #def #[ REGISTER i ] (_ : 'unit) : 'unit
         {
           #import {sig #[ SET_x i ] : chSETFinp → chSETFout }
           as set_x ;;
           #import {sig #[ DL_i i ] : 'unit → 'unit }
           as dl ;;
           #import {sig #[ SCHNORR_ i ] : 'unit → 'unit }
           as schnorr ;;
           xi ← sample (uniform #|'Z_q|) ;; let xi := WitnessToField (otf xi) in
           set_x xi ;;
           dl Datatypes.tt ;;
           schnorr Datatypes.tt
         }
      ].

    Definition register_i_keys_raw i b :=
      (par
         (KF_package (H_disj := H_disj_x i) (LOC_x i) (SET_x i) (GET_x i) b)
         (par
            (K_package (H_disj := H_disj_gx i) (LOC_gx i) (SET_gx i) (GET_gx i) b)
            (Kzkp_package (H_disj := H_disj_zkp i) (LOC_zkp i) (SET_zkp i) (GET_zkp i) b))).

    Lemma register_i_keys_valid :
      forall i b,
        ValidPackage
          (fset [:: ('option v_Z; LOC_x i)]
           :|: (fset [:: ('option v_G; LOC_gx i)]
                  :|: fset [:: ('option t_SchnorrZKPCommit; LOC_zkp i)]))
          [interface]
          ([interface #val #[SET_x i] : chCommitOutput → chSETBout ;
            #val #[GET_x i] : chSETBout → chCommitOutput ]
             :|: ([interface #val #[SET_gx i] : chGETout → chSETBout ;
                   #val #[GET_gx i] : chGETBinp → chGETout ]
                    :|: [interface #val #[SET_zkp i] : chGETZKPout → chSETBout ;
                         #val #[GET_zkp i] : chGETBinp → chGETZKPout ]))
          (register_i_keys_raw i b).
    Proof.
      intros.
      rewrite <- (fsetUid [interface]).
      apply valid_par ; [ apply ignore_Parable | apply pack_valid | .. ].
      rewrite <- (fsetUid [interface]).
      apply valid_par ; [ apply ignore_Parable | apply pack_valid .. ].
    Qed.

    Definition register_i_funcs i b :=
      (par (ID [interface #val #[SET_x i] : chSETFinp → chSETFout]) (par (schnorr_i i b) (dl_i i b))).

    Definition Gregister_i_funcs_raw i b :=
      register_i i
        ∘ register_i_funcs i b.

    Lemma Gregister_i_funcs_valid i b :
      ValidPackage
        fset0
        ([interface #val #[SET_x i] : chCommitOutput → chSETBout ]
  :|: ([interface #val #[SET_x i] : chGETFout → chSETBout ; #val #[GET_gx i] : chGETBinp → chGETout ;
                  #val #[SET_zkp i] : schnorrOutput → chSETBout ]
       :|: [interface #val #[GET_x i] : chGETBinp → chGETFout ;
                      #val #[SET_gx i] : chGETout → chSETBout ]))
        [interface #val #[REGISTER i] : 'unit → 'unit ]
        (Gregister_i_funcs_raw i b).
    Proof.
      unfold Gregister_i_funcs_raw.
      rewrite <- fset0U.
      eapply valid_link.
      2:{
        rewrite <- fset0U.
        eapply (valid_par_upto _ _ _ fset0 _ [interface #val #[SET_x i] : chCommitOutput → chSETBout ] _ _ _).
        1: apply ignore_Parable.
        1: apply valid_ID ; solve_flat.
        1:{
          eapply valid_par_upto.
          1: apply ignore_Parable.
          1, 2: apply pack_valid.
          1: rewrite fsetUid ; apply fsubsetxx.
          1: apply fsubsetxx.
          1: apply fsubsetxx.
        }
        1: rewrite fsetUid ; apply fsubsetxx.
        1: solve_in_fset.
        1: apply fsubsetxx.
      }
      rewrite fsetUA.
      rewrite <- !fset_cat.
      apply pack_valid.
    Qed.

    Definition Gregister_i_raw i b :=
      register_i i
        ∘ register_i_funcs i b
        ∘ register_i_keys_raw i b.

    Lemma Gregister_i_valid i b :
      ValidPackage
        (fset [:: ('option v_Z; LOC_x i)]
           :|: (fset [:: ('option v_G; LOC_gx i)]
           :|: fset [:: ('option t_SchnorrZKPCommit; LOC_zkp i)]))
        [interface]
        [interface #val #[REGISTER i] : 'unit → 'unit ]
        (Gregister_i_raw i b).
    Proof.
      unfold Gregister_i_raw.
      rewrite link_assoc.
      rewrite <- fset0U.
      eapply valid_link.
      1: apply Gregister_i_funcs_valid.
      eapply valid_package_inject_export.
      2:apply register_i_keys_valid.
      solve_in_fset.
    Qed.

    Definition Gregister_raw (u : nat) b :=
      parallel_package (fun i => {package Gregister_i_raw i b #with Gregister_i_valid i b}) u.

    Lemma Gregister_valid : forall u b,
        ValidPackage
          (combined_interfaces
             (fun i =>
                (fset [:: ('option v_Z; LOC_x i)]
                   :|: (fset [:: ('option v_G; LOC_gx i)]
                   :|: fset [:: ('option t_SchnorrZKPCommit; LOC_zkp i)]))) u)
          [interface]
          (combined_interfaces (λ i : nat, [interface #val #[REGISTER i] : chSETBout → chSETBout ]) u)
          (Gregister_raw u b).
    Proof.
      intros.
      setoid_rewrite <- (trivial_combined_interface _ [interface]).
      apply pack_valid.
    Qed.

    Definition Gregister (u : nat) : loc_GamePair (combined_interfaces (λ i, [interface #val #[REGISTER i] : chSETBout → chSETBout ]) u) :=
      fun b => {locpackage Gregister_raw u b #with Gregister_valid u b}.

    Lemma Gregister_advantage :
      forall u,
      ∀ (LA : {fset Location}) (A : raw_package),
        ValidPackage LA (combined_interfaces (fun i => [interface #val #[REGISTER i] : 'unit → 'unit ]) u) A_export A →
        (Advantage (Gregister u) A <= 0)%R.
    Proof.
      intros.
    Admitted.

  End G_register.

  Section G_commit_vote.
    (* COMMIT_TO_VOTE_INTERFACE *)
    Definition COMMIT_TO_VOTE (i : nat) := (Bound_nat * 25 + i)%nat.

    Definition commit_to_vote_i i :
      package fset0
        [interface
           #val #[GPOWY i] : 'unit → 'unit ;
           #val #[VOTE i] : 'unit → 'unit ;
           #val #[COMMIT_VOTE i] : 'unit → 'unit
        ]
        [interface
           #val #[ COMMIT_TO_VOTE i ] : 'unit → 'unit
        ] :=
      [package
         #def #[ COMMIT_TO_VOTE i ] (_ : 'unit) : 'unit
         {
           #import {sig #[ GPOWY i ] : 'unit → 'unit }
           as g_y ;;
           #import {sig #[ VOTE i ] : 'unit → 'unit }
           as vote ;;
           #import {sig #[ COMMIT_VOTE i ] : 'unit → 'unit }
           as commit ;;
           g_y Datatypes.tt ;;
           vote Datatypes.tt ;;
           commit Datatypes.tt
         }
      ].

    Definition Gcommit_to_vote_i_raw u (i : 'I_u.+1) b :=
      commit_to_vote_i i
        ∘ (par (g_yi u i b) (par (g_vote_i i b) (g_commit_i i b))).

    Lemma Gcommit_to_vote_i_valid u (i : 'I_u.+1) b :
      ValidPackage
        (fset [:: ('option v_Z; LOC_x i)]
           :|: (fset [:: ('option v_G; LOC_gx i)]
           :|: fset [:: ('option t_SchnorrZKPCommit; LOC_zkp i)]))
        (combined_interfaces (λ i : nat, [interface #val #[SET_gx i] : chSETinp → chSETout ; #val #[GET_gx i] : chGETinp → chGETout ]) u
           :|: [interface #val #[SET_gy i] : chSETinp → chSETout ; #val #[GET_gy i] : chGETinp → chGETout ]
           :|: [interface #val #[SET_vote i] : chSETinp → chSETout ; #val #[GET_vote i] : chGETinp → chGETout]
           :|: [interface #val #[SET_commit i] : chCommitOutput → chSETBout ]
           :|: [interface #val #[GET_x i] : chGETFinp → chGETFout]
           :|: [interface #val #[GET_v i] : chSETBout → 'bool ])
        [interface #val #[COMMIT_TO_VOTE i] : 'unit → 'unit ]
        (Gcommit_to_vote_i_raw u i b).
    Proof.
    Admitted.

    Definition Gcommit_to_vote_raw (u : nat) b :=
      parallel_package_in (Ordinal (n:=u.+1) (m:=u) (ltnSn u)) (fun i => {package Gcommit_to_vote_i_raw u i b #with Gcommit_to_vote_i_valid u i b}).

    Lemma combined_interfacesU :
      forall (u : nat) {T : ordType} (f g : nat -> {fset T}),
        (combined_interfaces (fun i => (f i :|: g i)) u) =
          combined_interfaces f u :|: combined_interfaces g u.
    Proof.
      intros.
      induction u.
      - reflexivity.
      - simpl.
        rewrite IHu.
        solve_fset_eq.
    Qed.

    Lemma combined_interfaces_combine :
      forall (u : nat) {T : ordType} (f g : nat -> {fset T}),
        (combined_interfaces (fun i => (combined_interfaces f u :|: g i)) u) =
          (combined_interfaces (fun i => f i :|: g i) u).
    Proof.
      intros.
      rewrite combined_interfacesU.
      rewrite trivial_combined_interface.
      induction u.
      - reflexivity.
      - simpl.
        rewrite <- IHu.
        solve_fset_eq.
    Qed.

    Lemma Gcommit_to_vote_valid : forall u b,
        ValidPackage
          (combined_interfaces
             (fun i =>
                (fset [:: ('option v_Z; LOC_x i)]
                   :|: (fset [:: ('option v_G; LOC_gx i)]
                   :|: fset [:: ('option t_SchnorrZKPCommit; LOC_zkp i)]))) u)
          (combined_interfaces
       (λ i : nat,
           ([interface #val #[SET_gx i] : chSETinp → chSETout ; #val #[GET_gx i] : chGETinp → chGETout ]
              :|: [interface #val #[SET_gy i] : chSETinp → chSETout ; #val #[GET_gy i] : chGETinp → chGETout ]
              :|: [interface #val #[SET_vote i] : chSETinp → chSETout ; #val #[GET_vote i] : chGETinp → chGETout]
              :|: [interface #val #[SET_commit i] : chCommitOutput → chSETBout ]
              :|: [interface #val #[GET_x i] : chGETFinp → chGETFout]
              :|: [interface #val #[GET_v i] : chSETBout → 'bool ])) u)
          (combined_interfaces (λ i : nat, [interface #val #[COMMIT_TO_VOTE i] : chSETBout → chSETBout ]) u)
          (Gcommit_to_vote_raw u b).
    Proof.
      intros.
      rewrite !combined_interfacesU.
      rewrite <- (trivial_combined_interface u (combined_interfaces (λ i : nat, [interface #val #[SET_gx i] : chDL_Output → chSETBout ; #val #[GET_gx i] : chSETBout → chDL_Output ]) u)).
      rewrite <- !combined_interfacesU.
      setoid_rewrite (trivial_combined_interface_to_in (Ordinal (n:=u.+1) (m:=u) (ltnSn u))).
      unfold Gcommit_to_vote_raw.
      apply pack_valid.
    Qed.
(* :|: [interface #val #[GET_vote i] : chSETBout → chDL_Output ; #val #[SET_vote i] : chDL_Output → chSETBout ] *)
(*           :|: [interface #val #[SET_commit i] : chCommitOutput → chSETBout ] *)
(*           :|: [interface #val #[GET_x i] : chSETBout → chCommitOutput ; #val #[GET_v i] : chSETBout → 'bool ]) u) *)

    Definition commit_to_vote_keys_raw i b :=
      par
        (K_package (H_disj := H_disj_gx i) (LOC_gx i) (SET_gx i) (GET_gx i) b)
        (par (K_package (H_disj := H_disj_gy i) (LOC_gy i) (SET_gy i) (GET_gy i) b)
           (par(K_package (H_disj := H_disj_vote i) (LOC_vote i) (SET_vote i) (GET_vote i) b)
              (par(KF_package (H_disj := H_disj_commit i) (LOC_commit i) (SET_commit i) (GET_commit i) b)
                 (par (KF_package (H_disj := H_disj_x i) (LOC_x i) (SET_x i) (GET_x i) b)
                    (KB_package (H_disj := H_disj_v i) (LOC_v i) (SET_v i) (GET_v i) b))))).

    Lemma commit_to_vote_keys_valid : forall i b,
        ValidPackage
          ((fset [:: ('option v_G; LOC_gx i)])
             :|: (fset [:: ('option v_G; LOC_gy i)])
             :|: (fset [:: ('option v_G; LOC_vote i)])
             :|: (fset [:: ('option v_Z; LOC_commit i)])
             :|: (fset [:: ('option v_Z; LOC_x i)])
             :|: fset [:: ('option 'bool; LOC_v i)])
          [interface]
          ([interface #val #[SET_gx i] : chSETinp → chSETout ; #val #[GET_gx i] : chGETinp → chGETout ]
             :|: [interface #val #[SET_gy i] : chSETinp → chSETout ; #val #[GET_gy i] : chGETinp → chGETout ]
                    :|: [interface #val #[SET_vote i] : chSETinp → chSETout ; #val #[GET_vote i] : chGETinp → chGETout]
                           :|: [interface #val #[SET_commit i] : chCommitOutput → chSETBout ]
                                  :|: [interface #val #[GET_x i] : chGETFinp → chGETFout]
                                         :|: [interface #val #[GET_v i] : chSETBout → 'bool ])
          (commit_to_vote_keys_raw i b).
    Proof.
      intros.
      rewrite <- !fsetUA.
      rewrite <- (fsetUid [interface]).
      refine (valid_par _ _ _ _ _ _ _ _ (ignore_Parable _ _) _ _).
      rewrite <- (fsetUid [interface]).
      refine (valid_par _ _ _ _ _ _ _ _ (ignore_Parable _ _) _ _).
      rewrite <- (fsetUid [interface]).
      refine (valid_par _ _ _ _ _ _ _ _ (ignore_Parable _ _) _ _).
      rewrite <- (fsetUid [interface]).
      refine (valid_par _ _ _ _ _ _ _ _ (ignore_Parable _ _) (valid_package_inject_export _ _ _ _ _ (fsub1Eset _ _ (mem_head _ _)) (pack_valid _)) _).
      rewrite <- (fsetUid [interface]).
      refine (valid_par _ _ _ _ _ _ _ _ (ignore_Parable _ _) (valid_package_inject_export _ _ _ _ _ _ (pack_valid _)) _).
      1: solve_in_fset.
      refine (valid_package_inject_export _ _ _ _ _ _ _).
      solve_in_fset.
    Qed.

    Definition Gcommit_to_vote_with_keys_raw (u : nat) (b : bool) :=
      (Gcommit_to_vote_raw u b) ∘
         (parallel_package
            (fun i => {package
                      commit_to_vote_keys_raw i b
                      #with
                 commit_to_vote_keys_valid i b
            } )
            u).

    Lemma Gcommit_to_vote_with_keys_valid : forall (u : nat) (b : bool),
        ValidPackage
          (combined_interfaces (fun i => (fset [:: ('option v_G; LOC_gx i)])
             :|: (fset [:: ('option v_G; LOC_gy i)])
             :|: (fset [:: ('option v_G; LOC_vote i)])
             :|: (fset [:: ('option v_Z; LOC_commit i)])
             :|: (fset [:: ('option v_Z; LOC_x i)])
             :|: fset [:: ('option 'bool; LOC_v i)]
             :|: fset [:: ('option t_SchnorrZKPCommit; LOC_zkp i)]) u
          )
          [interface]
          (combined_interfaces (fun i => [interface #val #[COMMIT_TO_VOTE i] : 'unit → 'unit ]) u)
          (Gcommit_to_vote_with_keys_raw u b).
    Proof.
      intros.
      unfold Gcommit_to_vote_with_keys_raw.
      setoid_rewrite <- (trivial_combined_interface u [interface]).
      (* rewrite <- fsetU0. *)
      eapply valid_package_inject_locations.
      2: refine (valid_link _ _ _ _ _ _ (parallel_package (λ i : nat, {package commit_to_vote_keys_raw i b }) u) (Gcommit_to_vote_valid u b) (pack_valid _)).
      rewrite !combined_interfacesU.
      solve_in_fset.
    Qed.

    Definition Gcommit_to_vote (u : nat) : loc_GamePair (combined_interfaces (fun i => [interface #val #[COMMIT_TO_VOTE i] : 'unit → 'unit ]) u) :=
      fun b => {locpackage Gcommit_to_vote_with_keys_raw u b #with Gcommit_to_vote_with_keys_valid u b}.

    Lemma Gcommit_to_vote_advantage :
      forall u,
      ∀ (LA : {fset Location}) (A : raw_package),
        ValidPackage LA (combined_interfaces (fun i => [interface #val #[COMMIT_TO_VOTE i] : 'unit → 'unit ]) u) A_export A →
        (Advantage (Gcommit_to_vote u) A <= 0)%R.
    Proof.
      intros.
    Admitted.

  End G_commit_vote.

  Section G_cast.
    Definition CAST (i : nat) := (Bound_nat * 26 + i)%nat.

    (* fail. (* TODO *) *)
  End G_cast.

  Section G_tally.
    Definition TALLY := 1000%nat.
    (* fail. (* TODO *) *)
  End G_tally.

  Section G_ovn.
    Definition OVN := 1001%nat.

    Program Definition ovn u  :
      package
        fset0
        ((combined_interfaces
            (fun i => [interface
                      #val #[ REGISTER i ] : 'unit → 'unit ;
                    #val #[ COMMIT_TO_VOTE i ] : 'unit → 'unit ;
                    #val #[ CAST i ] : 'unit → 'unit]) u)
           :|:  [interface #val #[ TALLY ] : 'unit → 'unit ])
        [interface
           #val #[ OVN ] : 'unit → 'unit
        ] :=
      [package
         #def #[ OVN ] (_ : 'unit) : 'unit
         {
           List.fold_left
             (fun c j =>
                p ← c ;;
                #import {sig #[ REGISTER j ] : 'unit → 'unit }
                as register ;;
                   register Datatypes.tt) (iota 0 u) (ret Datatypes.tt) ;;
           List.fold_left
             (fun c j =>
                p ← c ;;
                #import {sig #[ COMMIT_TO_VOTE j ] : 'unit → 'unit }
                as commit_to_vote ;;
                   commit_to_vote Datatypes.tt) (iota 0 u) (ret Datatypes.tt) ;;
           List.fold_left
             (fun c j =>
                p ← c ;;
                #import {sig #[ CAST j ] : 'unit → 'unit }
                as cast ;;
                   cast Datatypes.tt) (iota 0 u) (ret Datatypes.tt) ;;
           #import {sig #[ TALLY ] : 'unit → 'unit }
           as tally ;;
           tally Datatypes.tt
         }
      ].
    Final Obligation.
      intros.
      ssprove_valid_package.
      apply valid_bind.
      1:{
        apply fold_valid2 ; [ ssprove_valid | intros a ; ssprove_valid ; [ apply a | ] ].
        rewrite in_fset.
        rewrite in_cat.
        apply /orP ; left.
        simpl.
        assert (b < u)%nat by now rewrite mem_iota in H ; Lia.lia.
        clear -H0.
        induction u.
        - discriminate.
        - simpl.
         rewrite in_fset.
         rewrite in_cat.
         apply /orP ; left.
         destruct (b == u) eqn:b_is_u ; move /eqP: b_is_u => b_is_u.
          + subst.
            clear.
            simpl.
            induction u.
            * rewrite in_fset.
              rewrite in_cons.
              apply /orP ; left.
              apply /eqP.
              reflexivity.
            * simpl.
              rewrite in_fset.
              rewrite in_cat.
              apply /orP ; right.
              simpl.
              rewrite in_fset.
              rewrite in_cons.
              apply /orP ; left.
              apply /eqP.
              reflexivity.
          + apply IHu.
            Lia.lia.
      }
      intros _.
 
      apply valid_bind.
      1:{
        apply fold_valid2 ; [ ssprove_valid | intros a ; ssprove_valid ; [ apply a | ] ].
        rewrite in_fset.
        rewrite in_cat.
        apply /orP ; left.
        simpl.
        assert (b < u)%nat by now rewrite mem_iota in H ; Lia.lia.
        clear -H0.
        induction u.
        - discriminate.
        - simpl.
         rewrite in_fset.
         rewrite in_cat.
         apply /orP ; left.
         destruct (b == u) eqn:b_is_u ; move /eqP: b_is_u => b_is_u.
          + subst.
            clear.
            simpl.
            induction u.
            * rewrite in_fset.
              rewrite in_cons.
              apply /orP ; right.
              apply /orP ; left.
              apply /eqP.
              reflexivity.
            * simpl.
              rewrite in_fset.
              rewrite in_cat.
              apply /orP ; right.
              simpl.
              rewrite in_fset.
              rewrite in_cons.
              apply /orP ; right.
              apply /orP ; left.
              apply /eqP.
              reflexivity.
          + apply IHu.
            Lia.lia.
      }
      intros _.

      apply valid_bind.
      1:{
        apply fold_valid2 ; [ ssprove_valid | intros a ; ssprove_valid ; [ apply a | ] ].
        rewrite in_fset.
        rewrite in_cat.
        apply /orP ; left.
        simpl.
        assert (b < u)%nat by now rewrite mem_iota in H ; Lia.lia.
        clear -H0.
        induction u.
        - discriminate.
        - simpl.
         rewrite in_fset.
         rewrite in_cat.
         apply /orP ; left.
         destruct (b == u) eqn:b_is_u ; move /eqP: b_is_u => b_is_u.
          + subst.
            clear.
            simpl.
            induction u.
            * rewrite in_fset.
              rewrite in_cons.
              apply /orP ; right.
              apply /orP ; right.
              apply /orP ; left.
              apply /eqP.
              reflexivity.
            * simpl.
              rewrite in_fset.
              rewrite in_cat.
              apply /orP ; right.
              simpl.
              rewrite in_fset.
              rewrite in_cons.
              apply /orP ; right.
              apply /orP ; right.
              apply /orP ; left.
              apply /eqP.
              reflexivity.
          + apply IHu.
            Lia.lia.
      }
      intros _.

      ssprove_valid.
      rewrite in_fset.
      rewrite in_cat.
      apply /orP ; right.
      rewrite in_fset.
      reflexivity.
    Defined.

    Definition ovn_keys_raw i b :=
      par
        (K_package (H_disj := H_disj_gx i) (LOC_gx i) (SET_gx i) (GET_gx i) b)
        (par (K_package (H_disj := H_disj_gy i) (LOC_gy i) (SET_gy i) (GET_gy i) b)
           (par(K_package (H_disj := H_disj_vote i) (LOC_vote i) (SET_vote i) (GET_vote i) b)
              (par(KF_package (H_disj := H_disj_commit i) (LOC_commit i) (SET_commit i) (GET_commit i) b)
                 (par (KF_package (H_disj := H_disj_x i) (LOC_x i) (SET_x i) (GET_x i) b)
                    (KB_package (H_disj := H_disj_v i) (LOC_v i) (SET_v i) (GET_v i) b))))).

    Lemma ovn_keys_valid : forall i b,
        ValidPackage
          ((fset [:: ('option v_G; LOC_gx i)])
             :|: (fset [:: ('option v_G; LOC_gy i)])
             :|: (fset [:: ('option v_G; LOC_vote i)])
             :|: (fset [:: ('option v_Z; LOC_commit i)])
             :|: (fset [:: ('option v_Z; LOC_x i)])
             :|: fset [:: ('option 'bool; LOC_v i)])
          [interface]
          ([interface #val #[SET_gx i] : chSETinp → chSETout ; #val #[GET_gx i] : chGETinp → chGETout ]
             :|: [interface #val #[SET_gy i] : chSETinp → chSETout ; #val #[GET_gy i] : chGETinp → chGETout ]
                    :|: [interface #val #[SET_vote i] : chSETinp → chSETout ; #val #[GET_vote i] : chGETinp → chGETout]
                           :|: [interface #val #[SET_commit i] : chCommitOutput → chSETBout ]
                                  :|: [interface #val #[GET_x i] : chGETFinp → chGETFout]
                                         :|: [interface #val #[GET_v i] : chSETBout → 'bool ])
          (ovn_keys_raw i b).
    Proof.
    Admitted.

    Definition Govn_raw u b :=
      ovn u
        ∘ (par
           (parallel_package (fun i => {package _ #with Gregister_i_funcs_valid i b}) u)
           (parallel_package_in (Ordinal (n:=u.+1) (m:=u) (ltnSn u)) (fun i => {package _ #with Gcommit_to_vote_i_valid u i b})))
        ∘ parallel_package (fun i => {package ovn_keys_raw i b #with ovn_keys_valid i b }) u.

    Lemma Govn_valid u b :
      ValidPackage
        (combined_interfaces
           (fun i => (fset [:: ('option v_G; LOC_gx i)])
                    :|: (fset [:: ('option v_G; LOC_gy i)])
                    :|: (fset [:: ('option v_G; LOC_vote i)])
                    :|: (fset [:: ('option v_Z; LOC_commit i)])
                    :|: (fset [:: ('option v_Z; LOC_x i)])
                    :|: fset [:: ('option 'bool; LOC_v i)]) u)
        [interface]
        [interface #val #[ OVN ] : 'unit → 'unit ]
        (Govn_raw u b).
    Proof.
    Admitted.

    Definition Govn (u : nat) : loc_GamePair [interface #val #[ OVN ] : 'unit → 'unit ] :=
      fun b => {locpackage Govn_raw u b #with Govn_valid u b}.

    Lemma pack_parallel_package :
      forall u {L I E} (f : forall (i : nat), package (L i) (I i) (E i)),
      pack (parallel_package f u)
      = parallel_package_raw (fun i => pack (f i)) u.
    Proof. reflexivity. Qed.

    Lemma pack_parallel_package_in :
      forall u (index : 'I_u) {L I E} (f : forall i, package (L i) (I i) (E i)),
      pack (parallel_package_in index f)
      = parallel_package_in_raw index (fun i => pack (f i)).
    Proof. reflexivity. Qed.

    Lemma split_parallel_package : forall (u : nat) {LA IA EA}
        (A : forall (i : nat), package (LA i) (IA i) (EA i))
      {LB IB EB}
      (B : forall (i : nat), package (LB i) (IB i) (EB i)),
      forall (ValidAB : forall i, ValidPackage (LA i :|: LB i) (IA i :|: IB i) (EA i :|: EB i) (par (A i) (B i))),
        parallel_package (λ i : nat, {package par (A i) (B i) #with ValidAB i}) u
        = {package par (parallel_package A u) (parallel_package B u) #with sig_rewrite_aux id
    (parallel_package_valid (λ i : nat, LA i :|: LB i) (λ i : nat, IA i :|: IB i)
       (λ i : nat, EA i :|: EB i) (λ i : nat, {package par (A i) (B i) }) u)
    (split_parallel_package_raw u (λ i : nat, A i) (λ i : nat, B i))}.
    Proof.
      intros.
      unfold parallel_package.
      unfold pack.
      now rewrite (mkpackage_rewrite id _ (split_parallel_package_raw u _ _)).
    Qed.

    Lemma advantage_reflexivity :
      forall P A, AdvantageE P P A = 0%R.
    Proof.
      unfold AdvantageE.
      intros.
      rewrite subrr.
      rewrite Num.Theory.normr0.
      reflexivity.
    Qed.

    Lemma keyed_package :
      forall {LA EA},
      forall {LB EB},
      forall {LK IK EK},
      forall (A : raw_package)
        (B : raw_package)
        (K : raw_package),
        ValidPackage LA EK EA A ->
        ValidPackage LB EK EB B ->
        ValidPackage LK IK EK K ->
        trimmed EA A ->
        trimmed EB B ->
        trimmed EK K ->
        (par A B) ∘ K = (par (A ∘ ID EK) (B ∘ ID EK)) ∘ K.
    Proof.
      intros.
      set (K) at 2.
      rewrite <- (id_link LK IK EK K) ; [ | assumption | assumption ].
      set (ID EK) at 2 3.
      rewrite (package_split (ID EK)).
      subst r r0.
      rewrite link_assoc.
      now erewrite <- (interchange) ; [ .. | apply ignore_Parable] ; (reflexivity || eassumption || apply valid_ID, (flat_valid_package _ _ _ K _)).
      Unshelve. all: exact fset0.
    Qed.

    Lemma Govn_advantage :
      forall u,
      ∀ (LA : {fset Location}) (A : raw_package),
        ValidPackage LA [interface #val #[ OVN ] : 'unit → 'unit ] A_export A →
        (Advantage (Govn u) A <= 0)%R.
    Proof.
      intros.
      unfold Govn.
      simpl.
      unfold Govn_raw.

      (* Ignore 'just' code *)
      rewrite Advantage_E
      ; rewrite -Advantage_link
      ; set (Hl := _ ∘ _) ; pattern false in Hl
      ; set (Hr := _ ∘ _) ; pattern true in Hr
      ; subst Hl Hr
      ; erewrite <- Advantage_E.

      rewrite Advantage_E.
      match goal with
      | [ |- context [ par (pack ?a) (pack ?b) ∘ (pack ?c) ] ] => set a ; set b ; set c
      end.
      pattern false in p.
      set (fun _ => _) in p.
      subst p.
      pattern false in p0.
      set (fun _ => _) in p0.
      subst p0.
      pattern false in p1.
      set (fun _ => _) in p1.
      subst p1.

      fold (y true).
      fold (y0 true).
      fold (y1 true).

      refine (advantage_helper0 _ _ _ (fun b => pack_valid (y b)) (fun b => pack_valid (y0 b)) (fun b => pack_valid (y1 b)) _ _ _ _ _ _) ; [ admit .. | clear ; intros | clear ; intros ].
      {
        refine (advantage_helper2
                    (A := y)
                    (B := fun b => parallel_package_raw (fun i => register_i_keys_raw _ b) u)
                    (K := y1)
                    _ _ _ _ _ 0%R _ Adv) ; [ admit .. | clear Adv ; intros ].
        {
          intros.
          subst y.
          hnf.
          unfold pack, parallel_package.
          rewrite !parallel_package_interchange_raw.
          rewrite <- !link_assoc.
          rewrite <- !parallel_package_interchange_raw.

          set (Hl := parallel_package_raw _ _) ; pattern false in Hl
          ; set (Hr := parallel_package_raw _ _) ; pattern true in Hr
          ; subst Hl Hr
          ; erewrite <- Advantage_E.

          refine (Gregister_advantage u _ _ _).
          admit.
        }
      }
      {
        refine (advantage_helper2
                    (A := y0)
                    (B := fun b => parallel_package_raw (fun i => commit_to_vote_keys_raw _ b) u)
                    (K := y1)
                    _ _ _ _ _ 0%R _ Adv) ; [ admit .. | clear Adv ; intros ].
        {
          intros.
          subst y0.
          hnf.
          unfold pack, parallel_package_in.
          (* rewrite <- !parallel_package_in_interchange_raw. *)

          set (Hl := _ ∘ _) ; pattern false in Hl
          ; set (Hr := _ ∘ _) ; pattern true in Hr
          ; subst Hl Hr
          ; erewrite <- Advantage_E.

          refine (Gcommit_to_vote_advantage u _ _ _).
          admit.
        }
      }
    Admitted.
  End G_ovn.

End OVN_proof.
