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

  Definition K_any_package_raw {A : choice_type} {B : finType} (H : Choice.sort A = Finite.sort B) `{H_pos : Positive #|B|} (K_loc : nat) SET GET {H_disj : SET <> GET} (b : bool) :
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
                       ret ([eta λ b : B, eq_rect_r id b H] (otf xi) : A)
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

  Lemma K_any_package_valid {A : choice_type} {B : finType} (H : Choice.sort A = Finite.sort B) `{H_pos : Positive #|B|} (K_loc : nat) SET GET {H_disj : SET <> GET} (b : bool) :
    ValidPackage
      (fset [('option A ; K_loc) : Location])
      [interface]
      (fset [(SET, (A, 'unit)); (GET, ('unit, A))])
      (K_any_package_raw H K_loc SET GET (H_disj := H_disj) b).
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

  Definition K_any_package {A : choice_type} {B : finType} (H : Choice.sort A = Finite.sort B) `{H_pos : Positive #|B|} (K_loc : nat) SET GET {H_disj : SET <> GET} (b : bool) :
    package
      (fset [('option A ; K_loc) : Location])
      [interface]
      (fset [(SET, (A, 'unit)); (GET, ('unit, A))]) :=
    {package _ #with K_any_package_valid H K_loc SET GET (H_disj := H_disj) b }.

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
    [package
       #def #[ SET ] (v : chSETFinp) : chSETFout
       {
         k ← get (chOption v_Z ; K_loc ) ;;
         match k with
         | None =>
             k ←
               (if b
                then
                  xi ← sample (uniform (H := Zq_pos) #|'Z_q|) ;;
                  ret (WitnessToField (otf xi))
                else
                  ret v) ;;
             #put ('option v_Z ; K_loc) := Some k ;;
             ret (Datatypes.tt : 'unit)
         | Some _ =>
             ret (Datatypes.tt : 'unit)
         end
       } ;
     #def #[ GET ] (_ : 'unit) : chGETFout
       {
         k ← get (chOption v_Z ; K_loc ) ;;
         k ← match k with
           | None =>
               (@fail v_Z ;; ret (chCanonical v_Z))
           | Some x =>
               ret x
           end ;;
         ret k
       }
    ].
  Next Obligation.
    intros.
    ssprove_valid ; try destruct v ; ssprove_valid.
    rewrite notin_cons. now apply /andP.
  Defined.
  Fail Next Obligation.

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
    ltac:( refine( [package
       #def #[ SET ] (v : chSETinp) : chSETout
       {
         k ← get (chOption v_G ; K_loc ) ;;
         match k with
         | None =>
             k ←
               (if b
                then
                  xi ← sample (uniform (H := Zq_pos) #|'Z_q|) ;;
                  ret (g ^+ fto xi : v_G)
                else
                  ret v) ;;
             #put ('option v_G ; K_loc) := Some k ;;
             ret (Datatypes.tt : 'unit)
         | Some _ =>
             ret (Datatypes.tt : 'unit)
         end
       } ;
     #def #[ GET ] (_ : 'unit) : chGETout
       {
         k ← get (chOption v_G ; K_loc ) ;;
         k ← match k with
           | None =>
               (@fail v_G ;; ret (chCanonical v_G))
           | Some x =>
               ret x
           end ;;
         ret k
       }
    ] ) ; ssprove_valid ; try destruct v ; ssprove_valid ; rewrite notin_cons ; now apply /andP).

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
    ltac:( refine ([package
       #def #[ SET ] (v : chSETZKPinp) : chSETZKPout
       {
         k ← get (chOption t_SchnorrZKPCommit ; K_loc ) ;;
         match k with
         | None =>
             k ←
               (if b
                then
                  a ← sample (uniform (H := Zq_pos) #|'Z_q|) ;;
                  b ← sample (uniform (H := Zq_pos) #|'Z_q|) ;;
                  c ← sample (uniform (H := Zq_pos) #|'Z_q|) ;;
                  ret (( g ^+ (otf a) : v_G, (WitnessToField (otf b)) : v_Z, (WitnessToField (otf c)) : v_Z) : t_SchnorrZKPCommit)
                else
                  ret v) ;;
             #put ('option t_SchnorrZKPCommit ; K_loc) := Some k ;;
             ret (Datatypes.tt : 'unit)
         | Some _ =>
             ret (Datatypes.tt : 'unit)
         end
       } ;
     #def #[ GET ] (_ : 'unit) : chGETZKPout
       {
         k ← get (chOption t_SchnorrZKPCommit ; K_loc ) ;;
         k ← match k with
           | None =>
               (@fail t_SchnorrZKPCommit ;; ret (chCanonical t_SchnorrZKPCommit))
           | Some x =>
               ret x
           end ;;
         ret k
       }
    ]) ; ssprove_valid ; try destruct v ; ssprove_valid ; rewrite notin_cons ; now apply /andP).

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
    ltac:(refine ([package
       #def #[ SET ] (v : chSETORinp) : chSETORout
       {
         k ← get (chOption t_OrZKPCommit ; K_loc ) ;;
         match k with
         | None =>
             k ←
               (if b
                then
                  av ← sample (uniform (H := Zq_pos) #|'Z_q|) ;;
                  bv ← sample (uniform (H := Zq_pos) #|'Z_q|) ;;
                  cv ← sample (uniform (H := Zq_pos) #|'Z_q|) ;;
                  dv ← sample (uniform (H := Zq_pos) #|'Z_q|) ;;
                  ev ← sample (uniform (H := Zq_pos) #|'Z_q|) ;;
                  fv ← sample (uniform (H := Zq_pos) #|'Z_q|) ;;
                  gv ← sample (uniform (H := Zq_pos) #|'Z_q|) ;;
                  hv ← sample (uniform (H := Zq_pos) #|'Z_q|) ;;
                  iv ← sample (uniform (H := Zq_pos) #|'Z_q|) ;;
                  jv ← sample (uniform (H := Zq_pos) #|'Z_q|) ;;
                  kv ← sample (uniform (H := Zq_pos) #|'Z_q|) ;;
                  ret ((
                      g ^+ (otf av) : v_G,
                      g ^+ (otf bv) : v_G,
                      g ^+ (otf cv) : v_G,
                      g ^+ (otf dv) : v_G,
                      g ^+ (otf ev) : v_G,
                      g ^+ (otf fv) : v_G,
                      (WitnessToField (otf gv)) : v_Z,
                      (WitnessToField (otf hv)) : v_Z,
                      (WitnessToField (otf iv)) : v_Z,
                      (WitnessToField (otf jv)) : v_Z,
                      (WitnessToField (otf kv)) : v_Z
                    ) : t_OrZKPCommit)
                else
                  ret v) ;;
             #put ('option t_OrZKPCommit ; K_loc) := Some k ;;
             ret (Datatypes.tt : 'unit)
         | Some _ =>
             ret (Datatypes.tt : 'unit)
         end
       } ;
     #def #[ GET ] (_ : 'unit) : chGETORout
       {
         k ← get (chOption t_OrZKPCommit ; K_loc ) ;;
         k ← match k with
           | None =>
               (@fail t_OrZKPCommit ;; ret (chCanonical t_OrZKPCommit))
           | Some x =>
               ret x
           end ;;
         ret k
       }
    ]) ; ssprove_valid ; try destruct v ; ssprove_valid ; rewrite notin_cons ; now apply /andP).

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
      ] := K_any_package (A := 'bool) (B := 'bool) (erefl) K_loc SET GET (H_disj := H_disj) b.

  Lemma Gschnorr_x_zkp_advantage :
    forall B (C : finType) H K_loc SET GET H_disj (H_pos : Positive #|C|),
    ∀ (LA : {fset Location}) (A : raw_package),
      ValidPackage LA [interface
         #val #[ SET ] : chSETBinp → chSETBout ;
         #val #[ GET ] : chGETBinp → chGETBout
      ] A_export A →
      (AdvantageE
         (K_any_package (A := B) (B := C) H K_loc SET GET (H_disj := H_disj) true)
         (K_any_package (A := B) (B := C) H K_loc SET GET (H_disj := H_disj) false) A <= 0)%R.
  Proof.
    intros.
  Admitted.

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

  Axiom ignore_Parable : forall A B, Parable A B.

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

  Fixpoint parallel_package_raw {L I E} (p : forall (n : nat), package (L n) (I n) (E n)) u : raw_package :=
    match u with
    | O => p O
    | S n => par (parallel_package_raw p n) (p (S n))
    end.
  Fixpoint combined_interfaces {T : ordType} (i : forall (n : nat), {fset T}) u : {fset T} :=
    match u with
    | O => i O
    | S n => (combined_interfaces i n) :|: (i (S n))
    end.
  Lemma parallel_package_valid : forall L I E p u,
      ValidPackage
        (combined_interfaces L u)
        (combined_interfaces I u)
        (combined_interfaces E u)
        (parallel_package_raw (L := L) (I := I) (E := E) p u).
  Proof.
    intros.
    induction u.
    - apply pack_valid.
    - simpl.
      apply valid_par.
      + apply ignore_Parable.
      + apply IHu.
      + apply p.
  Qed.
  Definition parallel_package {L I E} p u := {package _ #with parallel_package_valid L I E p u}.

  Check nat_of_ord (Ordinal (m := O) _).
  Check Ordinal.
  
  Equations parallel_package_in_raw {u : nat} (index : 'I_u) {L} {I E} (p : forall (n : 'I_u), package (L n) (I n) (E n)) : raw_package by wf (nat_of_ord index) lt :=
    parallel_package_in_raw (@Ordinal _ O i) p := p (Ordinal (m := O) i) ;
    parallel_package_in_raw (@Ordinal _ (S n) i) p := par (parallel_package_in_raw (Ordinal (m := n) (ltnW i)) p) (p (Ordinal (m := S n) i)).
  Final Obligation. easy. Defined.

  Equations combined_interfaces_in {u : nat} (index : 'I_u) {T : ordType} (i : forall (n : 'I_u), {fset T}) : {fset T} by wf (nat_of_ord index) lt :=
    combined_interfaces_in (@Ordinal _ O h) i := i (Ordinal (m := O) h) ;
    combined_interfaces_in (@Ordinal _ (S n) h) i := (combined_interfaces_in (Ordinal (m := n) (ltnW h)) i) :|: (i (Ordinal (m := S n) h)).
  Final Obligation. easy. Defined.

  Lemma parallel_package_in_valid : forall u (index : 'I_u) L I E p,
      ValidPackage
        (combined_interfaces_in index L)
        (combined_interfaces_in index I)
        (combined_interfaces_in index E)
        (parallel_package_in_raw (L := L) (I := I) (E := E) index p).
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

  Section Gschnorr_x_zkp.
    Definition SCHNORR_ (i : nat) := (Bound_nat * 18 + i)%nat.

    Definition schnorr_i_real i :
      package fset0
        [interface
           #val #[SET_x i] : chSETFinp → chSETFout ;
           #val #[GET_gx i] : chGETinp → chGETout ;
           #val #[SET_zkp i] : schnorrOutput → chSETORout
        ]
        [interface #val #[ SCHNORR_ i ] : 'unit → 'unit].
    Admitted.

    Definition schnorr_i_ideal i :
      package fset0
        [interface
           #val #[GET_gx i] : chGETinp → chGETout ;
           #val #[SET_zkp i] : schnorrOutput → chSETORout
        ]
        [interface #val #[ SCHNORR_ i ] : 'unit → 'unit].
    Admitted.

    Definition schnorr_i i (b : bool) :
      package fset0
        [interface
           #val #[SET_x i] : chSETFinp → chSETFout ;
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
             (KF_package (H_disj := H_disj_x i) (LOC_x i) (SET_x i) (GET_x i) b)
             (par
                (K_package (H_disj := H_disj_gx i) (LOC_gx i) (SET_gx i) (GET_gx i) b)
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

    Lemma Gschnorr_x_zkp_advantage :
      forall u,
      ∀ (LA : {fset Location}) (A : raw_package),
        ValidPackage LA (combined_interfaces (fun i => [interface #val #[SCHNORR_ i] : 'unit → 'unit ]) u) A_export A →
        (Advantage (Gschnorr_x_zkp u) A <= 0)%R.
    Proof.
      intros.
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
    fail. (* TODO *)
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

    Definition Gregister_i_raw i b :=
      register_i i
        ∘ (par (ID [interface #val #[SET_x i] : chSETFinp → chSETFout]) (par (schnorr_i i b) (dl_i i b)))
        ∘ (par
             (KF_package (H_disj := H_disj_x i) (LOC_x i) (SET_x i) (GET_x i) b)
             (par
                (K_package (H_disj := H_disj_gx i) (LOC_gx i) (SET_gx i) (GET_gx i) b)
                (Kzkp_package (H_disj := H_disj_zkp i) (LOC_zkp i) (SET_zkp i) (GET_zkp i) b))).

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
      rewrite <- fset0U.
      eapply valid_link.
      2:{
        rewrite <- fset0U.
        eapply valid_link.
        2:{
          rewrite <- (fsetUid [interface]).
          apply valid_par ; [ apply ignore_Parable | apply pack_valid | .. ].
          rewrite <- (fsetUid [interface]).
          apply valid_par ; [ apply ignore_Parable | apply pack_valid .. ].
        }
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

    fail. (* TODO *)
  End G_cast.

  Section G_tally.
    Definition TALLY := 1000%nat.
    fail. (* TODO *)
  End G_tally.

  Section G_ovn.
    Definition OVN := 1001%nat.

    Program Definition ovn u (b : 'bool)  :
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
        assert (b0 < u)%nat by now rewrite mem_iota in H ; Lia.lia.
        clear -H0.
        induction u.
        - discriminate.
        - simpl.
         rewrite in_fset.
         rewrite in_cat.
         apply /orP ; left.
         destruct (b0 == u) eqn:b_is_u ; move /eqP: b_is_u => b_is_u.
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
        assert (b0 < u)%nat by now rewrite mem_iota in H ; Lia.lia.
        clear -H0.
        induction u.
        - discriminate.
        - simpl.
         rewrite in_fset.
         rewrite in_cat.
         apply /orP ; left.
         destruct (b0 == u) eqn:b_is_u ; move /eqP: b_is_u => b_is_u.
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
        assert (b0 < u)%nat by now rewrite mem_iota in H ; Lia.lia.
        clear -H0.
        induction u.
        - discriminate.
        - simpl.
         rewrite in_fset.
         rewrite in_cat.
         apply /orP ; left.
         destruct (b0 == u) eqn:b_is_u ; move /eqP: b_is_u => b_is_u.
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
      ovn u b
        ∘ (par
           (parallel_package (fun i => register_i i) u)
           (parallel_package (fun i => commit_to_vote_i i) u))
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

    Lemma Govn_advantage :
      forall u,
      ∀ (LA : {fset Location}) (A : raw_package),
        ValidPackage LA [interface #val #[ OVN ] : 'unit → 'unit ] A_export A →
        (Advantage (Govn u) A <= 0)%R.
    Proof.
      intros.
    Admitted.
  End G_ovn.

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

  Lemma all_step_advantage :
    forall state (i : nat) vi,
    ∀ (LA : {fset Location}) (A : raw_package),
      ValidPackage LA [interface #val #[ FULL_PROTOCOL_INTERFACE ] : 'unit → chSingleProtocolTranscript ] A_export A →
      LA :#: Schnorr_ZKP.Schnorr.MyAlg.Sigma_locs ->
      LA :#: Schnorr_ZKP.Schnorr.MyAlg.Simulator_locs ->
      LA :#: OR_ZKP.proof_args.MyAlg.Sigma_locs ->
      LA :#: OR_ZKP.proof_args.MyAlg.Simulator_locs ->
    forall (ϵ : _),
      (forall P, ϵ_DL P <= ϵ)%R →
      forall (ψ : _),
      (forall P, ϵ_COMMIT P <= ψ)%R ->
      forall (ν : _),
      (forall P, ϵ_GPOWYINOTZERO i state P <= ν)%R →
      (AdvantageE
         (full_protocol state i vi false false false false false false false false false false false false)
         (full_protocol state i vi true true true true true true true true true true true true) A <= ((ψ + ν) + (ϵ + ϵ)) + ((ψ + ν) + (ϵ + ϵ)))%R.
  Proof.
    intros.

    (* Idealize x *)
    eapply Order.le_trans ; [ eapply Advantage_triangle with (R := pack (full_protocol state i vi true false false false false false false false false false false false)) | ].
    apply Num.Theory.lerD.
    1:{
      unfold full_protocol, pack, full_protocol_raw.
      epose Advantage_link.
      epose Advantage_par.
      epose Advantage_parR.
      rewrite <- Advantage_link.
      erewrite Advantage_par.
      + unfold KeyStore, pack, raw_KeyStore.
        erewrite Advantage_parR.
        * admit.
        * admit. (* Should just be valid.. (nominal ssprove?) *)
        * apply pack_valid.
        * apply pack_valid.
        * admit. (* flat? (nominal ssprove?) *)
        * admit. (* trimmed? (nominal ssprove?) *)
        * admit. (* trimmed? (nominal ssprove?) *)
        * admit. (* trimmed? (nominal ssprove?) *)
      + admit. (* Should just be valid.. (nominal ssprove?) *)
      + apply pack_valid.
      + apply pack_valid.
      + admit. (* flat? (nominal ssprove?) *)
      + admit. (* trimmed? (nominal ssprove?) *)
      + admit. (* trimmed? (nominal ssprove?) *)
      + admit. (* trimmed? (nominal ssprove?) *)
    }

    (* Idealize schnorr *)
    eapply Order.le_trans ; [ eapply Advantage_triangle with (R := pack (full_protocol state i vi true false false false false false false false false true false false)) | ].
    apply Num.Theory.lerD.
    1:{
      unfold full_protocol, pack, full_protocol_raw.
      epose Advantage_link.
      epose Advantage_par.
      epose Advantage_parR.
      rewrite <- Advantage_link.
      erewrite Advantage_parR.
      + unfold KeyStore, pack, raw_KeyStore.
        erewrite Advantage_par.
        * erewrite Advantage_parR.
          -- admit. (* TODO: Proof of schnorr game ! *)
          -- admit. (* Should just be valid.. (nominal ssprove?) *)
          -- apply pack_valid.
          -- apply pack_valid.
          -- admit. (* flat? (nominal ssprove?) *)
          -- admit. (* trimmed? (nominal ssprove?) *)
          -- admit. (* trimmed? (nominal ssprove?) *)
          -- admit. (* trimmed? (nominal ssprove?) *)
        * admit. (* Should just be valid.. (nominal ssprove?) *)
        * admit. (* Should just be valid.. (nominal ssprove?) *)
        * admit. (* Should just be valid.. (nominal ssprove?) *)
        * admit. (* flat? (nominal ssprove?) *)
        * admit. (* trimmed? (nominal ssprove?) *)
        * admit. (* trimmed? (nominal ssprove?) *)
        * admit. (* trimmed? (nominal ssprove?) *)
      + admit. (* Should just be valid.. (nominal ssprove?) *)
      + admit. (* Should just be valid.. (nominal ssprove?) *)
      + admit. (* Should just be valid.. (nominal ssprove?) *)
      + admit. (* flat? (nominal ssprove?) *)
      + admit. (* trimmed? (nominal ssprove?) *)
      + admit. (* trimmed? (nominal ssprove?) *)
      + admit. (* trimmed? (nominal ssprove?) *)
    }

    (* Idealize schnorr *)
    eapply Order.le_trans ; [ eapply Advantage_triangle with (R := pack (full_protocol state i vi true false false false false false false false false true false false)) | ].
    apply Num.Theory.lerD.
    1:{
      unfold full_protocol, pack, full_protocol_raw.
      epose Advantage_link.
      epose Advantage_par.
      epose Advantage_parR.
      rewrite <- Advantage_link.
      erewrite Advantage_parR.
      + unfold KeyStore, pack, raw_KeyStore.
        erewrite Advantage_par.
        * erewrite Advantage_parR.
          -- admit. (* TODO: Proof of schnorr game ! *)
          -- admit. (* Should just be valid.. (nominal ssprove?) *)
          -- apply pack_valid.
          -- apply pack_valid.
          -- admit. (* flat? (nominal ssprove?) *)
          -- admit. (* trimmed? (nominal ssprove?) *)
          -- admit. (* trimmed? (nominal ssprove?) *)
          -- admit. (* trimmed? (nominal ssprove?) *)
        * admit. (* Should just be valid.. (nominal ssprove?) *)
        * admit. (* Should just be valid.. (nominal ssprove?) *)
        * admit. (* Should just be valid.. (nominal ssprove?) *)
        * admit. (* flat? (nominal ssprove?) *)
        * admit. (* trimmed? (nominal ssprove?) *)
        * admit. (* trimmed? (nominal ssprove?) *)
        * admit. (* trimmed? (nominal ssprove?) *)
      + admit. (* Should just be valid.. (nominal ssprove?) *)
      + admit. (* Should just be valid.. (nominal ssprove?) *)
      + admit. (* Should just be valid.. (nominal ssprove?) *)
      + admit. (* flat? (nominal ssprove?) *)
      + admit. (* trimmed? (nominal ssprove?) *)
      + admit. (* trimmed? (nominal ssprove?) *)
      + admit. (* trimmed? (nominal ssprove?) *)
    }

  Qed.

  (* Lemma full_proof : *)
  (*   full_protocol *)

  Lemma protocol_dl_real_to_ideal :
    forall state (i : nat) vi,
    ∀ (LA : {fset Location}) (A : raw_package),
      ValidPackage LA [interface #val #[ FULL_PROTOCOL_INTERFACE ] : 'unit → chSingleProtocolTranscript ] A_export A →
      LA :#: Schnorr_ZKP.Schnorr.MyAlg.Sigma_locs ->
      LA :#: Schnorr_ZKP.Schnorr.MyAlg.Simulator_locs ->
      LA :#: OR_ZKP.proof_args.MyAlg.Sigma_locs ->
      LA :#: OR_ZKP.proof_args.MyAlg.Simulator_locs ->
      forall (ϵ : _),
      (forall P, ϵ_DL P <= ϵ)%R →
      forall (ψ : _),
      (forall P, ϵ_COMMIT P <= ψ)%R ->
      forall (ν : _),
      (forall P, ϵ_GPOWYINOTZERO i state P <= ν)%R →
      (AdvantageE
           (full_protocol_interface state i vi ∘ par dl_real (par schnorr_real (par (par (GPowYiNotZero_real i state) commit_real) cds_real)))
           (full_protocol_interface_step4 state i vi ∘ (par (dl_random ∘ dl_ideal) (par (dl_random2 ∘ (dl_random ∘ dl_ideal)) (par schnorr_ideal_no_assert (par (par (GPowYiNotZero_ideal i state) commit_ideal) cds_ideal_no_assert)))))
           A <= ((ψ + ν) + (ϵ + ϵ))%R)%R.
  Proof.
    intros ? ? ? ? ? ? H_LA_Schnorr_Sigma H_LA_Schnorr_Simulator H_LA_Or_Sigma H_LA_Or_Simulator ? ? ? ? ? ?.

    trimmed_package (dl_real).
    trimmed_package (dl_ideal).
    trimmed_package (dl_random).
    trimmed_package (dl_random2).

    trimmed_package (schnorr_real).
    trimmed_package (schnorr_ideal).
    trimmed_package (schnorr_ideal_no_assert).

    trimmed_package (GPowYiNotZero_real i state).
    trimmed_package (GPowYiNotZero_ideal i state).

    trimmed_package (commit_real).
    trimmed_package (commit_ideal).

    trimmed_package (cds_real).
    trimmed_package (cds_ideal).
    trimmed_package (cds_ideal_no_assert).

    pose proof (fpv := pack_valid (full_protocol_intantiated state i vi)).
    unfold full_protocol_intantiated in fpv.
    unfold pack in fpv.

    eapply Order.le_trans ; [ apply Advantage_triangle with (R := (full_protocol_interface state i vi ∘ par dl_real (par schnorr_ideal (par (par (GPowYiNotZero_ideal i state) commit_ideal) cds_ideal)))) | ].
    (* rewrite <- (add0r (ϵ + ψ)%R). *)
    apply Num.Theory.lerD.
    {
      (* replace (AdvantageE _ _ _) with (@GRing.zero R) ; [ easy | symmetry ]. *)

      unfold_advantageE.
      unshelve unfold_advantageE ; [ .. | | solve_flat ].
      all:revgoals.
      all: try (apply fsubsetxx).
      all: try rewrite <- fset0E.
      all: try rewrite !fset0U.
      all: try (apply fsubsetxx || solve_in_fset).

      eapply Order.le_trans ; [ apply Advantage_triangle with (R := (par schnorr_ideal (par (par (GPowYiNotZero_real i state) commit_real) cds_real))) | ].
      rewrite <- (add0r (ψ + ν)%R).
      apply Num.Theory.lerD ; [ replace (AdvantageE _ _ _) with (@GRing.zero R) ; [ easy | symmetry ] | ].
      {
        rewrite !(par_commut _ (par _ _)).
        unfold_advantageE.
        2: solve_flat.
        eapply schnorr_advantage.
        2,3: eassumption.

        pose (trimmed_ID ([interface #val #[SCHNORR] : schnorrInput → schnorrOutput ]
           :|: ([interface #val #[GPOWYINOTZERO] : chGPowYiNotZeroInput → chDL_Output ]
                :|: [interface #val #[COMMIT] : chDL_Output → chCommitOutput ]
                :|: [interface #val #[CDS] : CDSinput → CDSoutput ]))).
        pose (trimmed_ID [interface #val #[SCHNORR] : schnorrInput → schnorrOutput ]).

        solve_valid_package.
        1: apply H.
        1:{
          unfold idents.
          rewrite !imfsetU.
          simpl.
          rewrite <- !fset1E.
          rewrite !imfset1.
          rewrite !fset1E.
          rewrite <- !fset_cat.
          simpl.
          rewrite <- !fset1E.
          rewrite fdisjoint1s.
          rewrite !in_fset.
          easy.
        }
        1: apply valid_ID ; solve_flat.
        1: apply valid_ID ; solve_flat.
        Unshelve.
        all: try (apply fsubsetxx).
        all: try rewrite <- fset0E.
        all: try rewrite !fset0U.
        all: try now (rewrite <- !fset_cat ; simpl ; solve_in_fset).
        all: try (apply fsubsetxx || solve_in_fset).
      }

      unshelve unfold_advantageE ; [ .. | | solve_flat ].
      all:revgoals.
      all: try (apply fsubsetxx).
      all: try rewrite <- fset0E.
      all: try rewrite !fset0U.
      all: try now (rewrite <- !fset_cat ; simpl ; solve_in_fset).
      all: try (apply fsubsetxx || solve_in_fset).


      eapply Order.le_trans ; [ apply Advantage_triangle with (R := ((par (par (GPowYiNotZero_ideal i state) commit_ideal) cds_real))) | ].
      rewrite <- (addr0 (ψ + ν)%R).
      apply Num.Theory.lerD ; [ | replace (AdvantageE _ _ _) with (@GRing.zero R) ; [ easy | symmetry ] ].
      {
        rewrite !(par_commut _ cds_real).
        unfold_advantageE.
        2: solve_flat.
        Unshelve.
        all: try (apply fsubsetxx).
        all: try rewrite <- fset0E.
        all: try rewrite !fset0U.
        all: try now (rewrite <- !fset_cat ; simpl ; solve_in_fset).
        all: try (apply fsubsetxx || solve_in_fset).

        eapply Order.le_trans ; [ apply Advantage_triangle with (R := ((par (GPowYiNotZero_real i state) commit_ideal))) | ].
        apply Num.Theory.lerD.
        {
          unfold_advantageE.
          2: solve_flat.
          match goal with | |- context [ AdvantageE _ _ ?A ] => specialize (H1 A) end.
          unfold ϵ_COMMIT in H1.
          rewrite Advantage_sym.
          rewrite Advantage_E in H1.
          apply H1.
        }
        {
          rewrite !(par_commut _ commit_ideal).
          unfold_advantageE.
          2: solve_flat.
          match goal with | |- context [ AdvantageE _ _ ?A ] => specialize (H2 A) end.
          unfold ϵ_GPOWYINOTZERO in H2.
          rewrite Advantage_sym.
          rewrite Advantage_E in H2.
          apply H2.
        }
      }
      {
        unfold_advantageE.
        2: solve_flat.
        Unshelve.
        all: try (apply fsubsetxx).
        all: try rewrite <- fset0E.
        all: try rewrite !fset0U.
        all: try now (rewrite <- !fset_cat ; simpl ; solve_in_fset).
        all: try (apply fsubsetxx || solve_in_fset).

        eapply cds_advantage.
        2,3: eassumption.

        pose (trimmed_ID
          ([interface #val #[SCHNORR] : schnorrInput → schnorrOutput ]
           :|: ([interface #val #[GPOWYINOTZERO] : chGPowYiNotZeroInput → chDL_Output ]
                :|: [interface #val #[COMMIT] : chDL_Output → chCommitOutput ]
                :|: [interface #val #[CDS] : CDSinput → CDSoutput ]))).
        pose (trimmed_ID ([interface #val #[GPOWYINOTZERO] : chGPowYiNotZeroInput → chDL_Output ]
          :|: [interface #val #[COMMIT] : chDL_Output → chCommitOutput ]
          :|: [interface #val #[CDS] : CDSinput → CDSoutput ])).
        epose (trimmed_ID [interface #val #[CDS] : CDSinput → CDSoutput ]).

        solve_valid_package.
        1: apply H.

        1:{
          unfold idents.
          rewrite !imfsetU.
          simpl.
          rewrite <- !fset1E.
          rewrite !imfset1.
          rewrite !fset1E.
          rewrite <- !fset_cat.
          simpl.
          rewrite <- !fset1E.
          rewrite fdisjoint1s.
          rewrite !in_fset.
          easy.
        }

        2:{
          unfold idents.
          rewrite !imfsetU.
          simpl.
          rewrite <- !fset1E.
          rewrite !imfset1.
          rewrite !fset1E.
          rewrite <- !fset_cat.
          simpl.
          rewrite <- !fset1E.
          rewrite fdisjoint1s.
          rewrite !in_fset.
          easy.
        }

        1,2,3: apply valid_ID ; solve_flat.
      }
    }

    eapply Order.le_trans ; [ apply Advantage_triangle with (R := (full_protocol_interface state i vi ∘ par dl_real (par schnorr_ideal_no_assert (par (par (GPowYiNotZero_ideal i state) commit_ideal) cds_ideal_no_assert)))) | ].
    rewrite <- (add0r (ϵ + ϵ)%R).
    apply Num.Theory.lerD.
    {
      replace (AdvantageE _ _ _) with (@GRing.zero R) ; [ easy | symmetry ].

      apply: eq_rel_perf_ind_ignore.
      2:{
        unshelve solve_valid_package.
        all: revgoals.
        all: try (apply fsubsetxx).
        all: try rewrite <- fset0E.
        all: try rewrite !fset0U.
        all: try now (rewrite <- !fset_cat ; simpl ; solve_in_fset).
        all: try (apply fsubsetxx || solve_in_fset).
      }
      1:{
        unshelve solve_valid_package.
        all: revgoals.
        all: try (apply fsubsetxx).
        all: try rewrite <- fset0E.
        all: try rewrite !fset0U.
        all: try now (rewrite <- !fset_cat ; simpl ; solve_in_fset).
        all: try (apply fsubsetxx || solve_in_fset).
      }
      3: apply H.
      1: (apply fsubsetxx || solve_in_fset).
      2,3: apply fdisjoints0.

      unfold eq_up_to_inv.
      simplify_eq_rel inp_unit.

      simpl.

      repeat choice_type_eqP_handle.
      erewrite !cast_fun_K.
      fold chElement.

      apply (r_uniform_bij) with (f := fun x => x) ; [ now apply inv_bij | intros xi ].
      rewrite bind_rewrite.
      rewrite bind_rewrite.

      simpl.

      apply (r_uniform_bij) with (f := fun x => x) ; [ now apply inv_bij | intros ? ].

      replace (Schnorr_ZKP.Schnorr.MyParam.R
                 (g ^+ FieldToWitness (WitnessToField (otf xi)))
                 (FieldToWitness (WitnessToField (otf xi)))) with
        true.
      2:{
        symmetry.
        unfold Schnorr_ZKP.Schnorr.MyParam.R.
        rewrite eqxx.
        reflexivity.
      }
      unfold assertD at 1.



      simpl.

      ssprove_sync=> ?.
      ssprove_same_head_generic.
      rewrite !bind_assoc.
      ssprove_same_head_generic.

      simpl.
      apply (rsame_head_alt (L := fset0)) ; [ destruct (_ != _) ; ssprove_valid | done | done | intros ? ].

      ssprove_sync=> ?.

      rewrite !eqxx.
      rewrite !FieldToWitnessCancel.

      replace (_ == _) with true ; [ | symmetry ].
      2:{
        rewrite mulrC.
        rewrite trunc_pow.
        rewrite expgM.
        rewrite inv_is_inv.
        destruct vi ; now rewrite eqxx.
      }
      simpl.
      ssprove_sync=> ?.
      ssprove_sync=> ?.
      ssprove_sync=> ?.
      ssprove_sync=> ?.
      apply r_ret.
      {
        intros.
        split ; [ | easy ].
        repeat rewrite pair_equal_spec ; repeat split.
      }
    }

    eapply Order.le_trans ; [ apply Advantage_triangle with (R := (full_protocol_interface_step1 state i vi ∘ (par (dl_random ∘ dl_real) (par dl_real (par schnorr_ideal_no_assert (par (par (GPowYiNotZero_ideal i state) commit_ideal) cds_ideal_no_assert)))))) | ].
    rewrite <- (add0r (ϵ + ϵ)%R).
    apply Num.Theory.lerD.
    1:{
      replace (AdvantageE _ _ _) with (@GRing.zero R) ; [ easy | symmetry ].

      apply: eq_rel_perf_ind_ignore.
      2:{
        unshelve solve_valid_package.
        all: revgoals.
        all: try (apply fsubsetxx).
        all: try rewrite <- fset0E.
        all: try rewrite !fset0U.
        all: try now (rewrite <- !fset_cat ; simpl ; solve_in_fset).
        all: try (apply fsubsetxx || solve_in_fset).
      }
      1:{
        unshelve solve_valid_package.
        all: revgoals.
        all: try (apply fsubsetxx).
        all: try rewrite <- fset0E.
        all: try rewrite !fset0U.
        all: try now (rewrite <- !fset_cat ; simpl ; solve_in_fset).
        all: try (apply fsubsetxx || solve_in_fset).
      }
      3: apply H.
      1: (apply fsubsetxx || solve_in_fset).
      2,3: apply fdisjoints0.

      unfold eq_up_to_inv.
      simplify_eq_rel inp_unit.

      simpl.

      repeat choice_type_eqP_handle.
      erewrite !cast_fun_K.
      fold chElement.

      apply (r_uniform_bij) with (f := fun x => x) ; [ now apply inv_bij | intros xi ].
      rewrite bind_rewrite.
      rewrite bind_rewrite.

      simpl.

      repeat choice_type_eqP_handle.
      erewrite !cast_fun_K.
      fold chElement.

      simpl.

      ssprove_sync=> ?.
      ssprove_sync=> ?.

      ssprove_same_head_generic.
      ssprove_same_head_generic.

      rewrite !FieldToWitnessCancel.

      ssprove_sync=> ?.
      ssprove_sync=> ?.
      ssprove_sync=> ?.
      ssprove_sync=> ?.
      ssprove_sync=> ?.

      apply r_ret.
      split ; [ | easy ].
      repeat rewrite pair_equal_spec ; repeat split.
    }

    eapply Order.le_trans ; [ apply Advantage_triangle with (R := (full_protocol_interface_step1 state i vi ∘ (par (dl_random ∘ dl_ideal) (par dl_real (par schnorr_ideal_no_assert (par (par (GPowYiNotZero_ideal i state) commit_ideal) cds_ideal_no_assert)))))) | ].
    apply Num.Theory.lerD.
    1:{
      unfold_advantageE.
      rewrite (par_commut (dl_random ∘ dl_real)).
      rewrite (par_commut (dl_random ∘ dl_ideal)).
      unfold_advantageE.
      Unshelve.
      all: revgoals.
      all: try (apply fsubsetxx).
      all: try rewrite <- fset0E.
      all: try rewrite !fset0U.
      all: try now (rewrite <- !fset_cat ; simpl ; solve_in_fset).
      all: try (apply fsubsetxx || solve_in_fset).
      1: eapply flat_valid_package ; apply dl_random.
      match goal with | |- context [ AdvantageE _ _ ?A ] => specialize (H0 A) end.
      unfold ϵ_DL in H0.
      rewrite Advantage_sym.
      rewrite Advantage_E in H0.
      apply H0.
    }

    pose (step4 := full_protocol_interface_step4 state i vi ∘ (par (dl_random ∘ dl_ideal) (par (dl_random2 ∘ (dl_random ∘ dl_real)) (par schnorr_ideal_no_assert (par (par (GPowYiNotZero_ideal i state) commit_ideal) cds_ideal_no_assert))))).
    eassert (step4_valid : ValidPackage _ Game_import [interface #val #[ FULL_PROTOCOL_INTERFACE ] : 'unit → chSingleProtocolTranscript ] step4).
    {
      subst step4.
      unshelve solve_valid_package.
      all: revgoals.
      all: try (apply fsubsetxx).
      all: try rewrite <- fset0E.
      all: try rewrite !fset0U.
      all: try now (rewrite <- !fset_cat ; simpl ; solve_in_fset).
      all: try (apply fsubsetxx || solve_in_fset).

      eapply valid_par_upto.
      1:{
        rewrite <- H5 at 1.
        erewrite !link_trim_commut.
        apply parable_par_r.
        1:{
          rewrite <- H6 at 1.
          erewrite !link_trim_commut.
          solve_Parable.
        }
        apply parable_par_r.
        1:{
          rewrite <- H9 at 1.
          solve_Parable.
        }
        apply parable_par_r.
        1:{
          apply parable_par_r.
          1:{
            rewrite <- H11.
            solve_Parable.
          }
          rewrite <- H13.
          solve_Parable.
        }
        rewrite <- H16.
        solve_Parable.
      }
      1:{ solve_valid_package.
          Unshelve.
          all: revgoals.
          all: try (apply fsubsetxx).
          all: try rewrite <- fset0E.
          all: try rewrite !fset0U.
          all: try now (rewrite <- !fset_cat ; simpl ; solve_in_fset).
          all: try (apply fsubsetxx || solve_in_fset).
          all: shelve. }
      1:{ solve_valid_package.
          Unshelve.
          all: revgoals.
          all: try (apply fsubsetxx).
          all: try rewrite <- fset0E.
          all: try rewrite !fset0U.
          all: try now (rewrite <- !fset_cat ; simpl ; solve_in_fset).
          all: try (apply fsubsetxx || solve_in_fset).
          all: shelve. }
      all: revgoals.
      all: try (apply fsubsetxx).
      all: try rewrite <- fset0E.
      all: try rewrite !fset0U.
      all: try now (rewrite <- !fset_cat ; simpl ; solve_in_fset).
      all: try (apply fsubsetxx || solve_in_fset).
    }
    eapply Order.le_trans ; [ apply Advantage_triangle with (R := step4) | ].
    rewrite <- (add0r ϵ%R).
    apply Num.Theory.lerD.
    2:{
      subst step4.
      unfold_advantageE.

      trimmed_package (dl_random2).

      unfold_advantageE.
      2: solve_flat.
      Unshelve.
      all: revgoals.
      all: try (apply fsubsetxx).
      all: try rewrite <- fset0E.
      all: try rewrite !fset0U.
      all: try now (rewrite <- !fset_cat ; simpl ; solve_in_fset).
      all: try (apply fsubsetxx || solve_in_fset).

      rewrite !(par_commut _ (par schnorr_ideal_no_assert _)).
      unfold_advantageE.
      2: solve_flat.
      Unshelve.
      all: revgoals.
      all: try (apply fsubsetxx).
      all: try rewrite <- fset0E.
      all: try rewrite !fset0U.
      all: try now (rewrite <- !fset_cat ; simpl ; solve_in_fset).
      all: try (apply fsubsetxx || solve_in_fset).

      unfold_advantageE.

      match goal with | |- context [ AdvantageE _ _ ?A ] => specialize (H0 A) end.
      unfold ϵ_DL in H0.
      rewrite Advantage_sym.
      rewrite Advantage_E in H0.
      apply H0.
    }

    pose (step1 := (full_protocol_interface_step1 state i vi ∘ (par (dl_random ∘ dl_ideal) (par dl_real (par schnorr_ideal_no_assert (par (par (GPowYiNotZero_ideal i state) commit_ideal) cds_ideal_no_assert)))))).
    eassert (step1_valid : ValidPackage _ Game_import [interface #val #[ FULL_PROTOCOL_INTERFACE ] : 'unit → chSingleProtocolTranscript ] step1).
    {
      subst step1.
      unshelve solve_valid_package.
      all: revgoals.
      all: try (apply fsubsetxx).
      all: try rewrite <- fset0E.
      all: try rewrite !fset0U.
      all: try now (rewrite <- !fset_cat ; simpl ; solve_in_fset).
      all: try (apply fsubsetxx || solve_in_fset).
    }

    pose (step2 := full_protocol_interface_step2 state i vi ∘ (par (dl_random ∘ dl_ideal) (par dl_real (par schnorr_ideal_no_assert (par (par (GPowYiNotZero_ideal i state) commit_ideal) cds_ideal_no_assert))))).
    eassert (step2_valid : ValidPackage _ Game_import [interface #val #[ FULL_PROTOCOL_INTERFACE ] : 'unit → chSingleProtocolTranscript ] step2).
    {
      subst step2.
      unshelve solve_valid_package.

      all: revgoals.
      all: try (apply fsubsetxx).
      all: try rewrite <- fset0E.
      all: try rewrite !fset0U.
      all: try now (rewrite <- !fset_cat ; simpl ; solve_in_fset).
      all: try (apply fsubsetxx || solve_in_fset).
    }

    split_advantage step2.
    {
      subst step1 step2.

      replace (AdvantageE _ _ _) with (@GRing.zero R) ; [ easy | symmetry ].

      apply: eq_rel_perf_ind_ignore.
      1: (apply fsubsetxx || solve_in_fset).
      2,3: apply fdisjoints0.

      unfold eq_up_to_inv.
      simplify_eq_rel inp_unit.

      simpl.

      repeat choice_type_eqP_handle.
      erewrite !cast_fun_K.
      fold chElement.

      simpl.

      eapply r_const_sample_R ; [ apply LosslessOp_uniform | intros ].

      eapply r_transR.
      1: apply swap_samples.

      (** Reflexivity from here on *)

      repeat choice_type_eqP_handle.
      erewrite !cast_fun_K.
      fold chElement.

      simpl.

      ssprove_sync=> ?.
      ssprove_sync=> ?.
      ssprove_sync=> ?.
      ssprove_sync=> ?.
      ssprove_same_head_generic.
      ssprove_same_head_generic.
      apply (r_reflexivity_alt (L := fset0)) ; [ | easy | easy ].
      ssprove_valid.
    }

    pose (step3 := full_protocol_interface_step3 state i vi ∘ (par (dl_random ∘ dl_ideal) (par dl_real (par schnorr_ideal_no_assert (par (par (GPowYiNotZero_ideal i state) commit_ideal) cds_ideal_no_assert))))).
    eassert (step3_valid : ValidPackage _ Game_import [interface #val #[ FULL_PROTOCOL_INTERFACE ] : 'unit → chSingleProtocolTranscript ] step3).
    {
      subst step3.
      unshelve solve_valid_package.
      all: revgoals.
      all: try (apply fsubsetxx).
      all: try rewrite <- fset0E.
      all: try rewrite !fset0U.
      all: try now (rewrite <- !fset_cat ; simpl ; solve_in_fset).
      all: try (apply fsubsetxx || solve_in_fset).
    }

    split_advantage step3.
    {
      subst step2 step3.

      replace (AdvantageE _ _ _) with (@GRing.zero R) ; [ easy | symmetry ].

      apply: eq_rel_perf_ind_ignore.
      1: (apply fsubsetxx || solve_in_fset).
      2,3: apply fdisjoints0.

      unfold eq_up_to_inv.
      simplify_eq_rel inp_unit.

      simpl.

      repeat choice_type_eqP_handle.
      erewrite !cast_fun_K.
      fold chElement.

      simpl.

      repeat choice_type_eqP_handle.
      erewrite !cast_fun_K.
      fold chElement.

      simpl.
      ssprove_sync=> _.

      eapply r_transR.
      1:{
        apply (r_uniform_bij) with (f := fun x => x) ; [ now apply inv_bij | intros ? ].
        apply (r_uniform_bij) with (f := fun x => x) ; [ now apply inv_bij | intros ? ].
        apply (r_uniform_bij) with (f := fun x => x) ; [ now apply inv_bij | intros ? ].
        eapply bobble_sampleC.
        ssprove_same_head_generic.
        eapply bobble_sampleC.
        apply r_bind_feq ; [ apply rreflexivity_rule | intros ].
        apply (r_uniform_bij) with (f := fun x => x) ; [ now apply inv_bij | intros ? ].
        apply rreflexivity_rule.
      }

      ssprove_sync=> f0.

      eapply r_transR.
      1:{
        eapply r_transR.
        1:{
          apply (r_uniform_bij) with (f := fun x => x) ; [ now apply inv_bij | intros ? ].
          apply swap_samples.
        }
        apply swap_samples.
      }

      ssprove_sync=> f1.
      ssprove_sync=> f2.
      ssprove_sync=> f3.

      ssprove_same_head_generic.
      ssprove_same_head_generic.

      apply (r_reflexivity_alt (L := fset0)) ; [ssprove_valid | easy | easy].
    }


    {
      subst step3 step4.

      replace (AdvantageE _ _ _) with (@GRing.zero R) ; [ easy | symmetry ].

      apply: eq_rel_perf_ind_ignore.
      1: (apply fsubsetxx || solve_in_fset).
      2,3: apply fdisjoints0.

      unfold eq_up_to_inv.
      simplify_eq_rel inp_unit.

      simpl.

      repeat choice_type_eqP_handle.
      erewrite !cast_fun_K.
      fold chElement.

      simpl.

      repeat choice_type_eqP_handle.
      erewrite !cast_fun_K.
      fold chElement.

      simpl.

      (* eapply r_const_sample_L ; [ apply LosslessOp_uniform | intros ]. *)
      ssprove_sync=> ?.
      ssprove_sync=> ?.
      ssprove_sync=> ?.
      ssprove_sync=> ?.
      ssprove_same_head_generic.
      rewrite !bind_assoc.
      ssprove_same_head_generic.
      simpl.

      eapply r_transL.
      1:{
        apply r_nice_swap_rule ; [ easy | easy | ].
        apply r_bind_assertD.
      }
      eapply r_transR.
      1:{
        apply r_nice_swap_rule ; [ easy | easy | ].
        apply r_bind_assertD.
      }

      apply r_assertD_same.
      intros.

      rewrite bind_rewrite.

      repeat choice_type_eqP_handle.
      erewrite !cast_fun_K.
      fold chElement.

      simpl.

      eapply (r_uniform_bij) with (f := (fun x => fto ((otf x) * inv a0))%R).
      1:{
        assert (inv a0 \is a GRing.unit).
        {
          rewrite <- FieldToWitnessCancel.
          apply rmorph_unit.
          rewrite unitfE.

          apply /eqP.
          apply (ssrbool.elimN eqP) in e.
          red ; intros.
          apply e.
          symmetry in H17.
          rewrite H17.
          rewrite FieldToWitnessCancel.
          rewrite inv_is_inv.

          reflexivity.
        }

        eapply (Bijective (g := fun x => fto ((otf x) / inv a0)%R)).
        {
          unfold cancel.
          simpl.
          intros.
          rewrite otf_fto.
          rewrite <- mulrA.
          rewrite mulrV.
          2: apply H17.
          rewrite mulr1.
          rewrite fto_otf.
          reflexivity.
        }
        {
          unfold cancel.
          simpl.
          intros.
          rewrite otf_fto.
          rewrite mulrVK.
          2: apply H17.
          rewrite fto_otf.
          reflexivity.
        }
      }
      intros.
      ssprove_sync=> ?.
      (* ssprove_same_head_generic. *)
      ssprove_sync=> ?.
      ssprove_sync=> ?.
      ssprove_sync=> ?.
      ssprove_sync=> ?.
      apply r_ret.
      split ; [ | easy ].

      intros.
      rewrite !rmorphM.
      rewrite !FieldToWitnessCancel.
      rewrite !otf_fto.
      reflexivity.
    }
  Qed. (* Fail Timeout 5 Qed. Admitted. (* 123.43 secs *) *)

  Lemma all_step_advantage :
    forall state (i : nat),
    ∀ (LA : {fset Location}) (A : raw_package),
      ValidPackage LA [interface #val #[ FULL_PROTOCOL_INTERFACE ] : 'unit → chSingleProtocolTranscript ] A_export A →
      LA :#: Schnorr_ZKP.Schnorr.MyAlg.Sigma_locs ->
      LA :#: Schnorr_ZKP.Schnorr.MyAlg.Simulator_locs ->
      LA :#: OR_ZKP.proof_args.MyAlg.Sigma_locs ->
      LA :#: OR_ZKP.proof_args.MyAlg.Simulator_locs ->
    forall (ϵ : _),
      (forall P, ϵ_DL P <= ϵ)%R →
      forall (ψ : _),
      (forall P, ϵ_COMMIT P <= ψ)%R ->
      forall (ν : _),
      (forall P, ϵ_GPOWYINOTZERO i state P <= ν)%R →
      (AdvantageE
         (full_protocol_interface state i true ∘ par dl_real (par schnorr_real (par (par (GPowYiNotZero_real i state) commit_real) cds_real)))
        (full_protocol_interface state i false ∘ par dl_real (par schnorr_real (par (par (GPowYiNotZero_real i state) commit_real) cds_real))) A <= ((ψ + ν) + (ϵ + ϵ)) + ((ψ + ν) + (ϵ + ϵ)))%R.
  Proof.
    intros ? ? ? ? ? H_LA_Schnorr_Sigma H_LA_Schnorr_Simulator H_LA_Or_Sigma H_LA_Or_Simulator ? ? ? ? ? ?.

    (* Close in from the left *)
    eapply Order.le_trans ; [ apply Advantage_triangle with (R := (full_protocol_interface_step4 state i true ∘ (par (dl_random ∘ dl_ideal) (par (dl_random2 ∘ (dl_random ∘ dl_ideal)) (par schnorr_ideal_no_assert (par (par (GPowYiNotZero_ideal i state) commit_ideal) cds_ideal_no_assert)))))) | ].
    apply Num.Theory.lerD.
    1: eapply (protocol_dl_real_to_ideal) ; eassumption.

    (* Close in from the right *)
    eapply Order.le_trans ; [ apply Advantage_triangle with (R := (full_protocol_interface_step4 state i false ∘ (par (dl_random ∘ dl_ideal) (par (dl_random2 ∘ (dl_random ∘ dl_ideal)) (par schnorr_ideal_no_assert (par (par (GPowYiNotZero_ideal i state) commit_ideal) cds_ideal_no_assert)))))) | ].
    rewrite <- (add0r ((ψ + ν) + (ϵ + ϵ))%R).
    apply Num.Theory.lerD.
    2: rewrite Advantage_sym ; eapply (protocol_dl_real_to_ideal) ; eassumption.

    replace (AdvantageE _ _ _) with (@GRing.zero R) ; [ easy | symmetry ].
    {
      trimmed_package (dl_real).
      trimmed_package (dl_ideal).
      trimmed_package (dl_random).
      trimmed_package (dl_random2).

      trimmed_package (schnorr_real).
      trimmed_package (schnorr_ideal).
      trimmed_package (schnorr_ideal_no_assert).

      trimmed_package (GPowYiNotZero_real i state).
      trimmed_package (GPowYiNotZero_ideal i state).

      trimmed_package (commit_real).
      trimmed_package (commit_ideal).

      trimmed_package (cds_real).
      trimmed_package (cds_ideal).
      trimmed_package (cds_ideal_no_assert).

      trimmed_package (full_protocol_interface_step4 state i false).

      assert (forall vi, ValidPackage Schnorr_ZKP.Schnorr.MyAlg.Sigma_locs Game_import
    [interface #val #[FULL_PROTOCOL_INTERFACE] : chGPowYiNotZeroInput → chSingleProtocolTranscript ]
    (full_protocol_interface_step4 state i vi
     ∘ par (dl_random ∘ dl_ideal)
         (par (dl_random2 ∘ dl_random ∘ dl_ideal)
            (par schnorr_ideal_no_assert
               (par (par (GPowYiNotZero_ideal i state) commit_ideal)
                  cds_ideal_no_assert))))).
      {
        intros.

        unshelve solve_valid_package.
        all: revgoals.
        all: try (apply fsubsetxx || solve_in_fset).

        eapply valid_par_upto.
        1:{
          rewrite <- H5 at 1.
          erewrite !link_trim_commut.
          apply parable_par_r.
          1:{
            rewrite <- H6 at 1.
            erewrite !link_trim_commut.
            solve_Parable.
          }
          apply parable_par_r.
          1:{
            rewrite <- H9 at 1.
            solve_Parable.
          }
          apply parable_par_r.
          1:{
            apply parable_par_r.
            1:{
              rewrite <- H11.
              solve_Parable.
            }
            rewrite <- H13.
            solve_Parable.
          }
          rewrite <- H16.
          solve_Parable.
        }
        1:{ solve_valid_package. }
        1:{
          eapply valid_par_upto.
          1:{
            rewrite <- H6 at 1.
            erewrite !link_trim_commut.
            apply parable_par_r.
            1:{
              rewrite <- H9 at 1.
              solve_Parable.
            }
            apply parable_par_r.
            1:{
              apply parable_par_r.
              1:{
                rewrite <- H11.
                solve_Parable.
              }
              rewrite <- H13.
              solve_Parable.
            }
          rewrite <- H16.
          solve_Parable.
        }
        1:{
          eapply valid_link.
          1: apply dl_random2.
          eapply valid_link.
          1: apply dl_random.
          apply dl_ideal.
        }
        1:{
          eapply valid_par_upto.
          1:{
            apply parable_par_r.
            1:{
              apply parable_par_r.
              1:{
                solve_Parable.
              }
              solve_Parable.
            }
            solve_Parable.
          }
          1: apply schnorr_ideal_no_assert.
          1:{
            eapply valid_par_upto.
            1: solve_Parable.
            1:{
              eapply valid_par_upto.
              1: solve_Parable.
              1: apply GPowYiNotZero_ideal.
              1: apply commit_ideal.
              all: apply fsubsetxx.
            }
            1: apply cds_ideal_no_assert.
            all: apply fsubsetxx.
          }
          all: apply fsubsetxx.
        }
        all: apply fsubsetxx.
        }
        3: rewrite <- !fset_cat ; simpl.
        3: solve_in_fset.
        1,2: try rewrite <- !fset0E.
        1,2: try rewrite !fsetU0.
        all: try (apply fsubsetxx || solve_in_fset).

        Unshelve.
        all: try (apply fsubsetxx || solve_in_fset).
      }

      apply: eq_rel_perf_ind_ignore.
      1: apply fsubsetxx.
      2,3: apply H_LA_Schnorr_Sigma.
      unfold eq_up_to_inv.
      simplify_eq_rel inp_unit.

      repeat choice_type_eqP_handle.
      erewrite !cast_fun_K.
      fold chElement.

      ssprove_code_simpl.
      simpl.
      ssprove_sync=> ?.
      ssprove_sync=> ?.
      ssprove_sync=> ?.
      ssprove_sync=> ?.
      ssprove_same_head_generic.

      erewrite !cast_fun_K.
      ssprove_same_head_generic.

      ssprove_sync=> _.

      simpl.
      eapply (r_uniform_bij) with (f := (fun (x : Arit (uniform #|'Z_q|)) => fto (otf x + 1)%R)) ; [ | intros ? ].
      1:{
        eapply (Bijective (g := (fun (x : Arit (uniform #|'Z_q|)) => fto (otf x - 1)%R))).
        {
          unfold cancel.
          intros.
          rewrite otf_fto.
          rewrite addrK.
          rewrite fto_otf.
          reflexivity.
        }
        {
          unfold cancel.
          intros.
          rewrite otf_fto.
          rewrite <- addrA.
          rewrite addNr.
          rewrite addr0.
          rewrite fto_otf.
          reflexivity.
        }
      }

      rewrite !FieldToWitnessCancel.
      rewrite !otf_fto.
      rewrite trunc_pow.
      rewrite expgD.
      rewrite mulg1.

      ssprove_sync=> ?.
      ssprove_sync=> ?.
      ssprove_sync=> ?.
      ssprove_sync=> ?.
      ssprove_sync=> ?.
      apply r_ret.
      easy.
    }
  Qed.


  Program Definition real_protocol (i : nat) (state : t_OvnContractState) (vi : 'bool) :
    package fset0
      [interface]
      [interface #val #[ FULL_PROTOCOL_INTERFACE ] : 'unit → chSingleProtocolTranscript ]
    :=
    [package
        #def #[ FULL_PROTOCOL_INTERFACE ] (_ : 'unit) : chSingleProtocolTranscript
        {
          xi ← sample (uniform #|'Z_q|) ;; let xi := WitnessToField (otf xi) : v_Z in
          ri ← sample (uniform #|'Z_q|) ;; let ri := WitnessToField (otf ri) in

          temp ← is_state (register_vote (ret_both ((i, xi, ri) : t_RegisterParam)) (ret_both state)) ;;
          state ← match temp : t_Result (v_A × t_OvnContractState) t_ParseError with
          | Result_Ok_case (_ , new_state) => ret new_state
          | Result_Err_case _ => ret (chCanonical t_OvnContractState)
            end ;;
          round_1 ←
              (zkp_i ← is_state (A := t_SchnorrZKPCommit) ((f_zkp_xis (ret_both (state : t_OvnContractState))).a[ ret_both (i : int32) ]) ;;
              g_pow_xi ← is_state (A := v_G) ((f_g_pow_xis (ret_both (state : t_OvnContractState))).a[ ret_both (i : int32) ]) ;;
              ret (zkp_i , g_pow_xi)) ;;
          (* TODO: allow modification of state *)

          temp ← is_state (commit_to_vote (ret_both ((i, xi, is_pure f_field_zero, is_pure f_field_zero, is_pure f_field_zero, vi) : t_CastVoteParam)) (ret_both (state : t_OvnContractState))) ;;
          state ← match temp : t_Result (v_A × t_OvnContractState) t_ParseError with
          | Result_Ok_case (_ , new_state) => ret new_state
          | Result_Err_case _ => ret (chCanonical t_OvnContractState)
            end ;;
          round_2 ← is_state (A := f_Z) ((f_commit_vis (ret_both (state : t_OvnContractState))).a[ ret_both (i : int32) ]) ;;
            (* TODO: allow modification of state *)

          w ← sample (uniform #|'Z_q|) ;; let w := WitnessToField (otf w) in
          r ← sample (uniform #|'Z_q|) ;; let r := WitnessToField (otf r) in
          d ← sample (uniform #|'Z_q|) ;; let d := WitnessToField (otf d) in
          temp ← is_state (cast_vote (ret_both ((i, xi, w, r, d, vi) : t_CastVoteParam)) (ret_both (state : t_OvnContractState))) ;;
          state ← match temp : t_Result (v_A × t_OvnContractState) t_ParseError with
          | Result_Ok_case (_ , new_state) => ret new_state
          | Result_Err_case _ => ret (chCanonical t_OvnContractState)
            end ;;
          round_3 ← (
              vote_i ← is_state (A := v_G) ((f_g_pow_xi_yi_vis (ret_both (state : t_OvnContractState))).a[ ret_both (i : int32) ]) ;;
              or_zkp_i ← is_state (A := t_OrZKPCommit) ((f_zkp_vis (ret_both (state : t_OvnContractState))).a[ ret_both (i : int32) ]) ;;
              ret (or_zkp_i, vote_i)) ;;
          (* TODO: allow modification of state *)

          ret ((round_1, round_2) , round_3)
        }
    ].
  Solve All Obligations with now intros ; apply nseq_n_pos, HOP.n_pos.
  Next Obligation.
    fold chElement in *.
    intros.
    ssprove_valid.
    all: try (apply valid_scheme ; rewrite <- fset0E ; apply (ChoiceEquality.is_valid_code (both_prog_valid _))).
    1: try destruct x0 , s.
    3: try destruct x3 , s.
    5: try destruct x6 , s.
    all: ssprove_valid.
  Qed.
  Fail Next Obligation.

  Lemma real_to_full_protocol_advantage :
    forall state (i : nat) vi,
      (Z.to_nat (unsigned (i : int32)) < from_uint_size (is_pure n))%coq_nat ->
    ∀ (LA : {fset Location}) (A : raw_package),
      ValidPackage LA [interface #val #[ FULL_PROTOCOL_INTERFACE ] : 'unit → chSingleProtocolTranscript ] A_export A →
      (AdvantageE
         (real_protocol i state vi)
         (full_protocol_interface state i vi ∘ par dl_real (par schnorr_real (par (par (GPowYiNotZero_real i state) commit_real) cds_real)))
         A = 0)%R.
  Proof.
    intros state i vi i_lt_n.
    intros.

    trimmed_package (dl_real).
    trimmed_package (dl_ideal).
    trimmed_package (dl_random).

    trimmed_package (schnorr_real).
    trimmed_package (schnorr_ideal).
    trimmed_package (schnorr_ideal_no_assert).

    trimmed_package (GPowYiNotZero_real i state).
    trimmed_package (GPowYiNotZero_ideal i state).

    trimmed_package (commit_real).
    trimmed_package (commit_ideal).

    trimmed_package (cds_real).
    trimmed_package (cds_ideal).
    trimmed_package (cds_ideal_no_assert).

    pose proof (fpv := pack_valid (full_protocol_intantiated state i vi)).

    apply: eq_rel_perf_ind_ignore.
    1: (apply fsubsetxx || solve_in_fset || shelve).
    2,3: apply fdisjoints0.

    unfold eq_up_to_inv.
    simplify_eq_rel inp_unit.

    repeat choice_type_eqP_handle.
    erewrite !cast_fun_K.
    fold chElement.

    apply (r_uniform_bij) with (f := fun x => x) ; [ now apply inv_bij | intros xi ].
    rewrite bind_rewrite.
    simpl.

    replace (Schnorr_ZKP.Schnorr.MyParam.R _ _) with true ; [ | symmetry ].
    2:{
      unfold Schnorr_ZKP.Schnorr.MyParam.R.
      now rewrite eqxx.
    }
    simpl assertD.
    simpl.

    apply (r_uniform_bij) with (f := fun x => x) ; [ now apply inv_bij | intros ri ].

    (* Round 1 / Register vote *)
    unfold register_vote at 1.

    rewrite bind_assoc.
    rewrite bind_assoc.
    rewrite bind_rewrite.
    rewrite bind_assoc.
    rewrite bind_rewrite.
    simpl.
    rewrite bind_assoc.

    apply somewhat_let_substitution.
    apply somewhat_substitution.
    rewrite bind_rewrite.

    apply somewhat_let_substitution.
    progress repeat replace (f_rp_zkp_random _) with (ret_both (WitnessToField (otf ri))) by now apply both_eq.
    progress repeat replace (f_rp_xi _) with (ret_both (WitnessToField (otf xi))) by now apply both_eq.
    progress repeat replace (f_rp_i _) with (ret_both (i : int32)) by now apply both_eq.

    rewrite <- conversion_is_true.
    ssprove_same_head_generic.

    apply somewhat_let_substitution.
    apply somewhat_substitution.
    rewrite bind_rewrite.

    apply somewhat_let_substitution.
    apply somewhat_substitution.
    rewrite bind_rewrite.

    apply somewhat_let_substitution.
    apply somewhat_substitution.
    rewrite bind_rewrite.

    apply somewhat_let_substitution.
    apply somewhat_substitution.
    rewrite bind_rewrite.

    rewrite bind_assoc.
    rewrite bind_assoc.
    apply somewhat_substitution.
    rewrite bind_rewrite.
    simpl.

    rewrite bind_assoc.
    match goal with | |- context [ ⊢ ⦃ _ ⦄ bind (is_state ?a) ?f ≈ _ ⦃ _ ⦄ ] => apply (somewhat_substitution a f) end.

    repeat set (update_at_usize _ _ _).
    rewrite (hacspec_function_guarantees (fun x => array_index x _)).
    rewrite <- hacspec_function_guarantees.

    eassert (forall state (v : both (nseq_ _ (from_uint_size (is_pure n)))), is_pure (f_zkp_xis (Build_t_OvnContractState [ state ] ( f_round1 := v))) = is_pure (f_zkp_xis state)).
    {
      clear ; intros.
      unfold f_zkp_xis at 1.
      unfold Build_t_OvnContractState at 1.
      simpl.
      reflexivity.
    }

    eassert (forall state (v : both (nseq_ _ (from_uint_size (is_pure n)))), is_pure (f_zkp_xis (Build_t_OvnContractState [ state ] ( f_zkp_xis := v))) = is_pure v).
    {
      clear ; intros.
      unfold f_zkp_xis at 1.
      unfold Build_t_OvnContractState at 1.
      simpl.
      reflexivity.
    }

    rewrite H13.
    rewrite H14.
    clear H13 H14.

    rewrite <- (hacspec_function_guarantees (fun x => array_index x _)).
    subst b0.
    replace (cast_int (ret_both i)) with (ret_both (i : int32)).
    2:{ apply both_eq.
        simpl.
        unfold cast_int at 1, lift1_both at 1, bind_both, bind_raw_both.
        simpl.
        rewrite wrepr_unsigned.
        reflexivity.
    }

    set (f_zkp_xis _).
    setoid_rewrite (array_update_eq b0 (ret_both a) i i_lt_n).
    subst b0.
    simpl.

    rewrite bind_assoc.

    repeat set (update_at_usize _ _ _).
    Misc.pattern_rhs_approx.
    match goal with | |- context [ ⊢ ⦃ _ ⦄ bind _ ?f ≈ _ ⦃ _ ⦄ ] => set f end.

    apply somewhat_substitution.

    rewrite (hacspec_function_guarantees (fun x => array_index x _)).
    rewrite <- hacspec_function_guarantees.

      eassert (forall state (v : both (nseq_ _ (from_uint_size (is_pure n)))),
                  is_pure (f_g_pow_xis (Build_t_OvnContractState [ state ] ( f_g_pow_xis := v)))
                  = is_pure v).
      {
        clear ; intros.
        unfold f_g_pow_xis at 1.
        unfold Build_t_OvnContractState at 1.
        simpl.
        reflexivity.
      }

      eassert (forall state (v : both (nseq_ _ (from_uint_size (is_pure n)))),
                  is_pure (f_g_pow_xis (Build_t_OvnContractState [ state ] ( f_zkp_xis := v)))
                  =
                    is_pure (f_g_pow_xis (state))).
      {
        clear ; intros.
        unfold f_g_pow_xis at 1.
        unfold Build_t_OvnContractState at 1.
        simpl.
        reflexivity.
      }

      eassert (forall state (v : both (nseq_ _ (from_uint_size (is_pure n)))),
                  is_pure (f_g_pow_xis (Build_t_OvnContractState [ state ] ( f_round1 := v)))
                  = is_pure (f_g_pow_xis (state))).
      {
        clear ; intros.
        unfold f_g_pow_xis at 1.
        unfold Build_t_OvnContractState at 1.
        simpl.
        reflexivity.
      }

      rewrite H16.
      rewrite H15.
      rewrite H14.
      clear H14 H15 H16.


    rewrite <- (hacspec_function_guarantees (fun x => array_index x _)).
    subst b.
    replace (cast_int (ret_both i)) with (ret_both (i : int32)).
    2:{ apply both_eq.
        simpl.
        unfold cast_int at 1, lift1_both at 1, bind_both, bind_raw_both.
        simpl.
        rewrite wrepr_unsigned.
        reflexivity.
    }

    setoid_rewrite (array_update_eq _ (ret_both _) i i_lt_n).
    rewrite bind_rewrite.
    subst r H13.
    hnf.
    rewrite bind_rewrite.

    (* Round 2 / commit_to_vote *)
    unfold commit_to_vote at 1.

    rewrite bind_assoc.
    rewrite bind_assoc.
    rewrite bind_rewrite.
    rewrite bind_assoc.
    rewrite bind_rewrite.
    simpl.
    rewrite bind_assoc.

    apply somewhat_let_substitution.
    apply somewhat_substitution.
    rewrite bind_rewrite.

    apply somewhat_let_substitution.

    progress repeat replace (f_cvp_xi _) with (ret_both (WitnessToField (otf xi))) by now apply both_eq.
    progress repeat replace (f_cvp_vote _) with (ret_both (vi : 'bool)) by now apply both_eq.
    progress repeat replace (f_cvp_i _) with (ret_both (i : int32)) by now apply both_eq.

    apply somewhat_substitution.
    rewrite (hacspec_function_guarantees (compute_g_pow_yi _)).

    eassert (forall state (v : both (nseq_ _ (from_uint_size (is_pure n)))),
                is_pure (f_g_pow_xis (Build_t_OvnContractState [ state ] ( f_g_pow_xis := v)))
                = is_pure v).
    {
      clear ; intros.
      unfold f_g_pow_xis at 1.
      unfold Build_t_OvnContractState at 1.
      simpl.
      reflexivity.
    }

    eassert (forall state (v : both (nseq_ _ (from_uint_size (is_pure n)))),
                is_pure (f_g_pow_xis (Build_t_OvnContractState [ state ] ( f_zkp_xis := v)))
                =
                  is_pure (f_g_pow_xis (state))).
    {
      clear ; intros.
      unfold f_g_pow_xis at 1.
      unfold Build_t_OvnContractState at 1.
      simpl.
      reflexivity.
    }

    eassert (forall state (v : both (nseq_ _ (from_uint_size (is_pure n)))),
                is_pure (f_g_pow_xis (Build_t_OvnContractState [ state ] ( f_round1 := v)))
                = is_pure (f_g_pow_xis (state))).
    {
      clear ; intros.
      unfold f_g_pow_xis at 1.
      unfold Build_t_OvnContractState at 1.
      simpl.
      reflexivity.
    }

    rewrite H15.
    rewrite H14.
    rewrite H13.
    clear H13 H14 H15.
    replace (cast_int (ret_both i)) with (ret_both (i : int32)).
    2:{ apply both_eq.
        simpl.
        unfold cast_int at 1, lift1_both at 1, bind_both, bind_raw_both.
        simpl.
        rewrite wrepr_unsigned.
        reflexivity.
    }

    rewrite <- hacspec_function_guarantees.
    rewrite compute_g_pow_yi_update_eq. 2: apply i_lt_n.
    rewrite bind_rewrite.

    apply somewhat_let_substitution.
    (* ssprove_same_head a0. *)
    apply somewhat_substitution.
    rewrite bind_rewrite.
    rewrite (bind_assoc (is_state (compute_g_pow_yi _ _))).
    apply somewhat_substitutionR.
    set (a0 := (is_pure (compute_g_pow_yi (ret_both i) (f_g_pow_xis (ret_both _))))).
    rewrite !bind_rewrite.

    apply somewhat_let_substitution.
    unfold commit_to at 1.
    eapply r_bind_feq_alt.
    {
      rewrite bind_ret.
      rewrite !FieldToWitnessCancel.
      set (s := is_pure _).
      set (s0 := (_ * _)%g).
      assert (s = s0) ; subst s s0.
      {
        unfold compute_group_element_for_vote at 1.

        rewrite mulrC.
        rewrite trunc_pow.
        rewrite expgM.
        rewrite inv_is_inv.

        Misc.push_down_sides.
        rewrite <- pow_witness_to_field.
        rewrite <- conversion_is_true.
        destruct vi ; [ rewrite rmorph1 | rewrite rmorph0 ] ; reflexivity.
      }
      rewrite H13.
      apply (r_reflexivity_alt (L := fset0)) ; [ ssprove_valid | easy | easy ].
      all: try (apply valid_scheme ; rewrite <- fset0E ; apply (ChoiceEquality.is_valid_code (both_prog_valid _))).
    }
    intros.
    apply somewhat_substitution.
    rewrite !bind_rewrite.
    (* apply somewhat_substitution. *)
    (* rewrite !bind_rewrite. *)
    simpl.

    (* Round 3 / cast_vote *)

    unfold cast_vote at 1.

    rewrite !eqxx.
    replace (_ == _) with true ; [ | symmetry].
    2:{
      rewrite !FieldToWitnessCancel.
      rewrite mulrC.
        rewrite trunc_pow.
        rewrite expgM.
        rewrite inv_is_inv.
        destruct vi ; now rewrite eqxx.
    }
    simpl assertD.
    simpl.

    apply (r_uniform_bij) with (f := fun x => x) ; [ now apply inv_bij | intros w ].
    apply (r_uniform_bij) with (f := fun x => x) ; [ now apply inv_bij | intros r ].
    apply (r_uniform_bij) with (f := fun x => x) ; [ now apply inv_bij | intros d ].

    rewrite bind_assoc.
    rewrite bind_assoc.
    rewrite bind_rewrite.

    rewrite bind_assoc.
    rewrite bind_assoc.
    rewrite bind_assoc.
    simpl.

    rewrite bind_assoc.
    apply somewhat_let_substitution.
    apply somewhat_substitution.
    rewrite bind_rewrite.
    apply somewhat_let_substitution.

    progress repeat replace (f_cvp_xi _) with (ret_both (WitnessToField (otf xi))) by now apply both_eq.
    progress repeat replace (f_cvp_zkp_random_w _) with (ret_both (WitnessToField (otf w))) by now apply both_eq.
    progress repeat replace (f_cvp_zkp_random_r _) with (ret_both (WitnessToField (otf r))) by now apply both_eq.
    progress repeat replace (f_cvp_zkp_random_d _) with (ret_both (WitnessToField (otf d))) by now apply both_eq.
    progress repeat replace (f_cvp_vote _) with (ret_both (vi : 'bool)) by now apply both_eq.
    progress repeat replace (f_cvp_i _) with (ret_both (i : int32)) by now apply both_eq.

    set (ret_both (is_pure _)).
    apply r_bind_feq_alt.
    {
      replace b with (ret_both a0) ; subst a0 b.
      2:{
        symmetry.
        repeat set (update_at_usize _ _ _).
        f_equal.

        replace (cast_int (ret_both i)) with (ret_both (i : int32)).
        2:{ apply both_eq.
            simpl.
            unfold cast_int at 1, lift1_both at 1, bind_both, bind_raw_both.
            simpl.
            rewrite wrepr_unsigned.
            reflexivity.
        }

        rewrite hacspec_function_guarantees.

        eassert (forall state (v : both (nseq_ _ (from_uint_size (is_pure n)))),
                    is_pure (f_g_pow_xis (Build_t_OvnContractState [ state ] ( f_g_pow_xis := v)))
                    = is_pure v).
        {
          clear ; intros.
          unfold f_g_pow_xis at 1.
          unfold Build_t_OvnContractState at 1.
          simpl.
          reflexivity.
        }

        eassert (forall state (v : both (nseq_ _ (from_uint_size (is_pure n)))),
                    is_pure (f_g_pow_xis (Build_t_OvnContractState [ state ] ( f_zkp_xis := v)))
                    =
                      is_pure (f_g_pow_xis (state))).
        {
          clear ; intros.
          unfold f_g_pow_xis at 1.
          unfold Build_t_OvnContractState at 1.
          simpl.
          reflexivity.
        }

        eassert (forall state (v : both (nseq_ _ (from_uint_size (is_pure n)))),
                    is_pure (f_g_pow_xis (Build_t_OvnContractState [ state ] ( f_round1 := v)))
                    = is_pure (f_g_pow_xis (state))).
        {
          clear ; intros.
          unfold f_g_pow_xis at 1.
          unfold Build_t_OvnContractState at 1.
          simpl.
          reflexivity.
        }

        eassert (forall state (v : both (nseq_ _ (from_uint_size (is_pure n)))),
                    is_pure (f_g_pow_xis (Build_t_OvnContractState [ state ] ( f_commit_vis := v)))
                    = is_pure (f_g_pow_xis (state))).
        {
          clear ; intros.
          unfold f_g_pow_xis at 1.
          unfold Build_t_OvnContractState at 1.
          simpl.
          reflexivity.
        }

        rewrite H16.
        rewrite H15.
        rewrite H14.
        rewrite H13.
        clear H13 H14 H15 H16.

        subst b.
        rewrite <- hacspec_function_guarantees.
        rewrite compute_g_pow_yi_update_eq. 2: apply i_lt_n.
        reflexivity.
      }
      apply (r_reflexivity_alt (L := fset0)).
      1: apply valid_scheme ; rewrite <- fset0E ; apply (ChoiceEquality.is_valid_code (both_prog_valid _)).
      1,2:easy.
    }
    intros.

    apply somewhat_let_substitution.
    apply somewhat_substitution.
    rewrite bind_rewrite.

    apply somewhat_let_substitution.
    apply somewhat_substitution.
    rewrite bind_rewrite.

    apply somewhat_let_substitution.
    apply somewhat_substitution.
    rewrite bind_rewrite.

    apply somewhat_let_substitution.
    apply somewhat_substitution.
    rewrite bind_rewrite.

    rewrite bind_assoc.
    rewrite bind_assoc.
    apply somewhat_substitution.
    rewrite bind_rewrite.
    simpl.

    rewrite bind_assoc.
    apply somewhat_substitution.

    clear -i_lt_n.

    eapply r_transL.
    {
      apply r_bind_feq.
      {
        apply r_ret.
        intros.

        rewrite pair_equal_spec ; split ; [ | subst ; easy ].

        repeat set (update_at_usize _ _ _).
        rewrite (hacspec_function_guarantees (fun x => array_index x _)).
        rewrite <- (hacspec_function_guarantees f_g_pow_xi_yi_vis).

        eassert (forall state (v : both (nseq_ _ (from_uint_size (is_pure n)))),
                    is_pure (f_g_pow_xi_yi_vis (Build_t_OvnContractState [ state ] ( f_zkp_vis := v)))
                    = is_pure (f_g_pow_xi_yi_vis (state))).
        {
          clear ; intros.
          unfold f_g_pow_xis at 1.
          unfold Build_t_OvnContractState at 1.
          simpl.
          reflexivity.
        }
        rewrite H0 ; clear H0.
        simpl.

        eassert (forall state (v : both (nseq_ _ (from_uint_size (is_pure n)))),
                    is_pure (f_g_pow_xi_yi_vis (Build_t_OvnContractState [ state ] ( f_g_pow_xi_yi_vis := v)))
                    = is_pure v).
        {
          clear ; intros.
          unfold f_g_pow_xis at 1.
          unfold Build_t_OvnContractState at 1.
          simpl.
          reflexivity.
        }
        rewrite H0 ; clear H0.

        subst b4.
        rewrite <- (hacspec_function_guarantees (fun x => array_index x _)).

        replace (cast_int (ret_both i)) with (ret_both (i : int32)).
        2:{ apply both_eq.
            simpl.
            unfold cast_int at 1, lift1_both at 1, bind_both, bind_raw_both.
            simpl.
            rewrite wrepr_unsigned.
            reflexivity.
        }

        setoid_rewrite (array_update_eq _ (ret_both _) i i_lt_n).
        simpl.
        reflexivity.
      }
      intros.
      apply rreflexivity_rule.
    }
    rewrite bind_rewrite.

    rewrite bind_assoc.
    match goal with | |- context [ ⊢ ⦃ _ ⦄ bind (is_state ?a) ?f ≈ _ ⦃ _ ⦄ ] => apply (somewhat_substitution a f) end.

    eapply r_transL.
    {
      apply r_bind_feq.
      {
        apply r_ret.
        intros.

        rewrite pair_equal_spec ; split ; [ | subst ; easy ].

        repeat set (update_at_usize _ _ _).
        rewrite (hacspec_function_guarantees (fun x => array_index x _)).
        rewrite <- (hacspec_function_guarantees f_zkp_vis).

        eassert (forall state (v : both (nseq_ _ (from_uint_size (is_pure n)))),
                    is_pure (f_zkp_vis (Build_t_OvnContractState [ state ] ( f_zkp_vis := v)))
                    = is_pure v).
        {
          clear ; intros.
          unfold f_g_pow_xis at 1.
          unfold Build_t_OvnContractState at 1.
          simpl.
          reflexivity.
        }
        rewrite H0 ; clear H0.
        rewrite <- (hacspec_function_guarantees (fun x => array_index x _)).
        simpl.

        subst b5.
        replace (cast_int (ret_both i)) with (ret_both (i : int32)).
        2:{ apply both_eq.
            simpl.
            unfold cast_int at 1, lift1_both at 1, bind_both, bind_raw_both.
            simpl.
            rewrite wrepr_unsigned.
            reflexivity.
        }

        setoid_rewrite (array_update_eq _ (ret_both _) i i_lt_n).
        simpl.
        reflexivity.
      }
      intros.
      apply rreflexivity_rule.
    }
    rewrite bind_rewrite.
    rewrite bind_rewrite.
    apply r_ret.
    intros.
    split ; [ | easy ].

    repeat rewrite pair_equal_spec ; repeat split.
    {
      simpl.
      clear -i_lt_n.
      repeat set (update_at_usize _ _ _).
      unfold Build_t_OvnContractState at 1 ; simpl.
      subst b2.

      setoid_rewrite (array_update_eq _ (ret_both _) i i_lt_n).
      reflexivity.
    }
    {
      unfold compute_group_element_for_vote at 1.
      rewrite !FieldToWitnessCancel.
      rewrite mulrC.
      rewrite trunc_pow.
      rewrite expgM.
      rewrite inv_is_inv.

        simpl.
        (* rewrite hacspec_function_guarantees2. *)
        (* rewrite (hacspec_function_guarantees2 f_pow). *)
        subst b.

        replace (cast_int (ret_both i)) with (ret_both (i : int32)).
        2:{ apply both_eq.
            simpl.
            unfold cast_int at 1, lift1_both at 1, bind_both, bind_raw_both.
            simpl.
            rewrite wrepr_unsigned.
            reflexivity.
        }


        rewrite hacspec_function_guarantees.

        eassert (forall state (v : both (nseq_ _ (from_uint_size (is_pure n)))),
                    is_pure (f_g_pow_xis (Build_t_OvnContractState [ state ] ( f_g_pow_xis := v)))
                    = is_pure v).
        {
          clear ; intros.
          unfold f_g_pow_xis at 1.
          unfold Build_t_OvnContractState at 1.
          simpl.
          reflexivity.
        }

        eassert (forall state (v : both (nseq_ _ (from_uint_size (is_pure n)))),
                    is_pure (f_g_pow_xis (Build_t_OvnContractState [ state ] ( f_zkp_xis := v)))
                    =
                      is_pure (f_g_pow_xis (state))).
        {
          clear ; intros.
          unfold f_g_pow_xis at 1.
          unfold Build_t_OvnContractState at 1.
          simpl.
          reflexivity.
        }

        eassert (forall state (v : both (nseq_ _ (from_uint_size (is_pure n)))),
                    is_pure (f_g_pow_xis (Build_t_OvnContractState [ state ] ( f_round1 := v)))
                    = is_pure (f_g_pow_xis (state))).
        {
          clear ; intros.
          unfold f_g_pow_xis at 1.
          unfold Build_t_OvnContractState at 1.
          simpl.
          reflexivity.
        }

        eassert (forall state (v : both (nseq_ _ (from_uint_size (is_pure n)))),
                    is_pure (f_g_pow_xis (Build_t_OvnContractState [ state ] ( f_commit_vis := v)))
                    = is_pure (f_g_pow_xis (state))).
        {
          clear ; intros.
          unfold f_g_pow_xis at 1.
          unfold Build_t_OvnContractState at 1.
          simpl.
          reflexivity.
        }

        rewrite (hacspec_function_guarantees (compute_g_pow_yi (ret_both i))).
        rewrite H3.
        rewrite H2.
        rewrite H1.
        rewrite H0.
        clear H0 H1 H2 H3.
        rewrite <- (hacspec_function_guarantees (compute_g_pow_yi (ret_both i))).

        rewrite compute_g_pow_yi_update_eq. 2: apply i_lt_n.
        Misc.push_down_sides.
        rewrite <- pow_witness_to_field.
        rewrite <- conversion_is_true.
        destruct vi ; [ rewrite rmorph1 | rewrite rmorph0 ] ; reflexivity.
    }
  Qed. (* Fail Timeout 5 Qed. Admitted. (* 319.394 secs *) *)

  Lemma real_protocol_is_maximum_balloc_secrecy_hiding :
    forall state (i : nat),
      (Z.to_nat (unsigned (i: int32)) < from_uint_size (is_pure n))%coq_nat ->
    ∀ (LA : {fset Location}) (A : raw_package),
      ValidPackage LA [interface #val #[ FULL_PROTOCOL_INTERFACE ] : 'unit → chSingleProtocolTranscript ] A_export A →
      LA :#: Schnorr_ZKP.Schnorr.MyAlg.Sigma_locs ->
      LA :#: Schnorr_ZKP.Schnorr.MyAlg.Simulator_locs ->
      LA :#: OR_ZKP.proof_args.MyAlg.Sigma_locs ->
    forall (ϵ : _),
    (forall P, ϵ_DL P <= ϵ)%R →
    forall (ψ : _),
    (forall P, ϵ_COMMIT P <= ψ)%R ->
    forall (ν : _),
    (forall P, ϵ_GPOWYINOTZERO i state P <= ν)%R →
    (AdvantageE
       (real_protocol i state true)
       (real_protocol i state false) A <= ((ψ + ν) + (ϵ + ϵ)) + ((ψ + ν) + (ϵ + ϵ)))%R.
  Proof.
    intros.

    (* Close in from the left *)
    eapply Order.le_trans ; [ eapply Advantage_triangle with (R := _) | ].

    replace (AdvantageE _ _ _) with (@GRing.zero R) ; [ rewrite add0r | symmetry ] ; revgoals.

    1: eapply (real_to_full_protocol_advantage state i true H) ; eassumption.

    rewrite Advantage_sym.

    eapply Order.le_trans ; [ eapply Advantage_triangle with (R := _) | ].

    replace (AdvantageE _ _ _) with (@GRing.zero R) ; [ rewrite add0r | symmetry ] ; revgoals.
    1: eapply (real_to_full_protocol_advantage state i false) ; eassumption.

    rewrite Advantage_sym.

    eapply all_step_advantage ; try eassumption.
  Qed.

  (*** /Solution *)

End OVN_proof.
