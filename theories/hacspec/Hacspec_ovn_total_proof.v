From mathcomp Require Import all_ssreflect fingroup.fingroup ssreflect.
Set Warnings "-notation-overridden,-ambiguous-paths".
From Crypt Require Import choice_type Package Prelude.
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

From Crypt Require Import jasmin_word.

From Crypt Require Import Schnorr SigmaProtocol.

From Relational Require Import OrderEnrichedCategory GenericRulesSimple.

Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp Require Import all_ssreflect all_algebra reals distr realsum
  fingroup.fingroup solvable.cyclic prime ssrnat ssreflect ssrfun ssrbool ssrnum
  eqtype choice seq.
Set Warnings "notation-overridden,ambiguous-paths".

From Mon Require Import SPropBase.

From Crypt Require Import Axioms ChoiceAsOrd SubDistr Couplings
  UniformDistrLemmas FreeProbProg Theta_dens RulesStateProb UniformStateProb
  pkg_core_definition choice_type pkg_composition pkg_rhl Package Prelude
  SigmaProtocol.

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
  From Crypt Require Import choice_type Package Prelude.
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
  Solve All Obligations with now intros ; destruct from_uint_size.
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
  Solve All Obligations with now intros ; destruct from_uint_size.
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
  Solve All Obligations with now intros ; destruct from_uint_size.
  Fail Next Obligation.

  Definition dl_real_ : loc_package [interface] [interface #val #[ DL_RANDOM ] : 'unit → chDLRandom] := {locpackage (pack dl_random ∘ pack dl_real) #with ltac:(unshelve solve_valid_package ; apply fsubsetxx)} .

  Definition dl_ideal_ : loc_package [interface] [interface #val #[ DL_RANDOM ] : 'unit → chDLRandom] := {locpackage (pack dl_random ∘ pack dl_ideal) #with ltac:(unshelve solve_valid_package ; apply fsubsetxx)} .

  Definition DL_game :
    loc_GamePair [interface
         #val #[ DL_RANDOM ] : 'unit → chDLRandom
      ] :=
    λ b,
      if b then dl_real_ else dl_ideal_.

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
        all: (apply fsubsetxx || solve_in_fset || shelve).
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
        (* instantiate (1 := ((LA :|: Schnorr_ZKP.Schnorr.MyAlg.Sigma_locs))). *)
        unshelve solve_valid_package.
        all: revgoals.
        1: instantiate (1 := LA).
        all: try (apply fsubsetxx || solve_in_fset).
        1: apply H.
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
    Unshelve.
    refine fset0.
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
  Solve All Obligations with now intros ; destruct from_uint_size.
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
  Solve All Obligations with now intros ; destruct from_uint_size.
  Fail Next Obligation.

  (* hash_is_psudorandom / commit - game *)
  Definition Commit_game :
    loc_GamePair [interface
         #val #[ COMMIT ] : chCommitInput → chCommitOutput
      ] :=
    λ b,
      if b then {locpackage commit_real} else {locpackage commit_ideal}.

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
  Solve All Obligations with now intros ; destruct from_uint_size.
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
  Solve All Obligations with now intros ; destruct from_uint_size.
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
      if b then {locpackage (GPowYiNotZero_real i state)} else {locpackage (GPowYiNotZero_ideal i state)}.

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

  Notation " 'chSingleProtocolTranscript' " :=
    ((t_SchnorrZKPCommit × v_G) × (v_Z) × (t_OrZKPCommit × v_G))
    (in custom pack_type at level 2).

  Definition FULL_PROTOCOL_INTERFACE : nat := 102.
  Definition SECOND_STEP : nat := 103.

  Program Definition full_protocol_interface (state : t_OvnContractState) (i : nat) (vi : 'bool) :
    package fset0
      [interface
         #val #[ DL ] : chDLInput → chDLOutput
       ; #val #[ SCHNORR ] : schnorrInput → schnorrOutput
       ; #val #[ GPOWYINOTZERO ] : chGPowYiNotZeroInput → chGPowYiNotZeroOutput
       ; #val #[ COMMIT ] : chCommitInput → chCommitOutput
       ; #val #[ CDS ] : CDSinput → CDSoutput
      ]
      [interface
         #val #[ FULL_PROTOCOL_INTERFACE ] : 'unit → chSingleProtocolTranscript
      ] :=
    {package [fmap (FULL_PROTOCOL_INTERFACE, ('unit; (((t_SchnorrZKPCommit × v_G) × (v_Z) × (t_OrZKPCommit × v_G)) ; fun (_ : 'unit) => _)))]}.
  Next Obligation.
    intros.
    refine (
          #import {sig #[ DL ] : chDLInput → chDLOutput }
          as dl ;;
          #import {sig #[ SCHNORR ] : schnorrInput → schnorrOutput }
          as schnorr ;;
          #import {sig #[ GPOWYINOTZERO ] : chGPowYiNotZeroInput → chGPowYiNotZeroOutput }
          as g_pow_yi_nz ;;
          #import {sig #[ COMMIT ] : chCommitInput → chCommitOutput }
          as commit_to ;;
          #import {sig #[ CDS ] : CDSinput → CDSoutput }
          as CDS ;;
          xi ← sample (uniform #|'Z_q|) ;; let xi := WitnessToField (otf xi) in
          g_pow_xi ← dl xi ;;
          zkp_i ← schnorr (xi, g_pow_xi) ;;
          g_pow_yi ← g_pow_yi_nz Datatypes.tt ;;
          g_pow_xy ← dl (WitnessToField (FieldToWitness xi * (inv g_pow_yi)))%R ;;
          vote_i ← ret ((g_pow_xy : gT) * g^+(if vi then 1 else 0)%R)%g ;;
          commit ← commit_to vote_i ;;
          cds_i ← CDS ((g_pow_xi, g_pow_yi, vote_i), (xi, vi)) ;;
          ret (((zkp_i, g_pow_xi, commit : f_Z, (cds_i : t_OrZKPCommit, vote_i))) : (((t_SchnorrZKPCommit × v_G) × v_Z) × (t_OrZKPCommit × v_G))%pack)
    ).
  Defined.
  Next Obligation.
    intros.
    unfold full_protocol_interface_obligation_1.
    fold chElement.
    eapply (valid_package_cons _ _ _ _ _ _ [] []).
    - apply valid_empty_package.
    - intros.
      ssprove_valid.
    - try (rewrite <- fset0E ; setoid_rewrite @imfset0 ; rewrite in_fset0 ; reflexivity).
  Qed.
  Fail Next Obligation.

  Program Definition full_protocol_interface_step1 (state : t_OvnContractState) (i : nat) (vi : 'bool) :
    package fset0
      [interface
         #val #[ DL ] : chDLInput → chDLOutput
       ; #val #[ SCHNORR ] : schnorrInput → schnorrOutput
       ; #val #[ GPOWYINOTZERO ] : chGPowYiNotZeroInput → chGPowYiNotZeroOutput
       ; #val #[ COMMIT ] : chCommitInput → chCommitOutput
       ; #val #[ CDS ] : CDSinput → CDSoutput
       ; #val #[ DL_RANDOM ] : 'unit → chDLRandom
      ]
      [interface
         #val #[ FULL_PROTOCOL_INTERFACE ] : 'unit → chSingleProtocolTranscript
      ] := {package [fmap (FULL_PROTOCOL_INTERFACE, ('unit; (((t_SchnorrZKPCommit × v_G) × (v_Z) × (t_OrZKPCommit × v_G)) ; fun (_ : 'unit) => _)))]}.
  Next Obligation.
    intros.
    refine (
          #import {sig #[ DL ] : chDLInput → chDLOutput }
          as dl ;;
          #import {sig #[ SCHNORR ] : schnorrInput → schnorrOutput }
          as schnorr ;;
          #import {sig #[ GPOWYINOTZERO ] : chGPowYiNotZeroInput → chGPowYiNotZeroOutput }
          as g_pow_yi_nz ;;
          #import {sig #[ COMMIT ] : chCommitInput → chCommitOutput }
          as commit_to ;;
          #import {sig #[ CDS ] : CDSinput → CDSoutput }
          as CDS ;;
          #import {sig #[ DL_RANDOM ] : 'unit → chDLRandom }
          as dl_random ;;
          '(g_pow_xi, xi) ← dl_random Datatypes.tt ;;
          zkp_i ← schnorr (xi, g_pow_xi) ;;
          g_pow_yi ← g_pow_yi_nz Datatypes.tt ;;
          g_pow_xy ← dl (WitnessToField (FieldToWitness xi * (inv g_pow_yi)))%R ;;
          vote_i ← ret ((g_pow_xy : gT) * g^+(if vi then 1 else 0)%R)%g ;;
          commit ← commit_to vote_i ;;
          cds_i ← CDS ((g_pow_xi, g_pow_yi, vote_i), (xi, vi)) ;;
          ret (((zkp_i, g_pow_xi, commit, (cds_i : t_OrZKPCommit, vote_i))) : (((t_SchnorrZKPCommit × v_G) × v_Z) × (t_OrZKPCommit × v_G))%pack)
      ).
  Defined.
  Next Obligation.
    intros.
    unfold full_protocol_interface_step1_obligation_1.
    fold chElement.
    eapply (valid_package_cons _ _ _ _ _ _ [] []).
    - apply valid_empty_package.
    - intros.
      ssprove_valid.
    - try (rewrite <- fset0E ; setoid_rewrite @imfset0 ; rewrite in_fset0 ; reflexivity).
  Qed.
  Fail Next Obligation.

  Program Definition full_protocol_interface_step2 (state : t_OvnContractState) (i : nat) (vi : 'bool) :
    package fset0
      [interface
         #val #[ DL ] : chDLInput → chDLOutput
       ; #val #[ SCHNORR ] : schnorrInput → schnorrOutput
       ; #val #[ GPOWYINOTZERO ] : chGPowYiNotZeroInput → chGPowYiNotZeroOutput
       ; #val #[ COMMIT ] : chCommitInput → chCommitOutput
       ; #val #[ CDS ] : CDSinput → CDSoutput
       ; #val #[ DL_RANDOM ] : 'unit → chDLRandom
      ]
      [interface
         #val #[ FULL_PROTOCOL_INTERFACE ] : 'unit → chSingleProtocolTranscript
      ] :=
    {package [fmap (FULL_PROTOCOL_INTERFACE, ('unit; (((t_SchnorrZKPCommit × v_G) × (v_Z) × (t_OrZKPCommit × v_G)) ; fun (_ : 'unit) => _)))]}.
  Next Obligation.
    intros.
    refine (
          #import {sig #[ DL_RANDOM ] : 'unit → chDLRandom }
          as dl_random ;;
          #import {sig #[ DL ] : chDLInput → chDLOutput }
          as dl ;;
          #import {sig #[ SCHNORR ] : schnorrInput → schnorrOutput }
          as schnorr ;;
          #import {sig #[ GPOWYINOTZERO ] : chGPowYiNotZeroInput → chGPowYiNotZeroOutput }
          as g_pow_yi_nz ;;
          #import {sig #[ COMMIT ] : chCommitInput → chCommitOutput }
          as commit_to ;;
          #import {sig #[ CDS ] : CDSinput → CDSoutput }
          as CDS ;;
          '(g_pow_xi,_) ← dl_random Datatypes.tt ;;
          xi ← sample uniform #|'Z_q| ;;
          let xi := (WitnessToField (otf xi : 'Z_q) : v_Z) in
          zkp_i ← schnorr (xi, g_pow_xi) ;;
          g_pow_yi ← g_pow_yi_nz Datatypes.tt ;;
          g_pow_xy ← dl (WitnessToField (FieldToWitness (xi) * (inv g_pow_yi)))%R ;;
          vote_i ← ret ((g_pow_xy : gT) * g^+(if vi then 1 else 0)%R)%g ;;
          commit ← commit_to vote_i ;;
          cds_i ← CDS ((g_pow_xi, g_pow_yi, vote_i), (xi, vi)) ;;
          ret (((zkp_i, g_pow_xi, commit, (cds_i : t_OrZKPCommit, vote_i))) : (((t_SchnorrZKPCommit × v_G) × v_Z) × (t_OrZKPCommit × v_G))%pack)).
  Defined.
  Next Obligation.
    intros.
    unfold full_protocol_interface_step2_obligation_1.
    eapply (valid_package_cons _ _ _ _ _ _ [] []).
    - apply valid_empty_package.
    - intros.
      ssprove_valid.
    - try (rewrite <- fset0E ; setoid_rewrite @imfset0 ; rewrite in_fset0 ; reflexivity).
  Qed.

  Program Definition full_protocol_interface_step3 (state : t_OvnContractState) (i : nat) (vi : 'bool) :
    package fset0
      [interface
         #val #[ DL ] : chDLInput → chDLOutput
       ; #val #[ SCHNORR ] : schnorrInput → schnorrOutput
       ; #val #[ GPOWYINOTZERO ] : chGPowYiNotZeroInput → chGPowYiNotZeroOutput
       ; #val #[ COMMIT ] : chCommitInput → chCommitOutput
       ; #val #[ CDS ] : CDSinput → CDSoutput
       ; #val #[ DL_RANDOM ] : 'unit → chDLRandom
      ]
      [interface
         #val #[ FULL_PROTOCOL_INTERFACE ] : 'unit → chSingleProtocolTranscript
      ] :=
    {package [fmap (FULL_PROTOCOL_INTERFACE, ('unit; (((t_SchnorrZKPCommit × v_G) × (v_Z) × (t_OrZKPCommit × v_G)) ; fun (_ : 'unit) => _)))]}.
  Next Obligation.
    intros.
    refine (
          #import {sig #[ DL_RANDOM ] : 'unit → chDLRandom }
          as dl_random ;;
          #import {sig #[ DL ] : chDLInput → chDLOutput }
          as dl ;;
          #import {sig #[ SCHNORR ] : schnorrInput → schnorrOutput }
          as schnorr ;;
          #import {sig #[ GPOWYINOTZERO ] : chGPowYiNotZeroInput → chGPowYiNotZeroOutput }
          as g_pow_yi_nz ;;
          #import {sig #[ COMMIT ] : chCommitInput → chCommitOutput }
          as commit_to ;;
          #import {sig #[ CDS ] : CDSinput → CDSoutput }
          as CDS ;;
          '(g_pow_xi,_) ← dl_random Datatypes.tt ;;
          zkp_i ← schnorr (WitnessToField (inv g_pow_xi), g_pow_xi) ;;
          g_pow_yi ← g_pow_yi_nz Datatypes.tt ;;
          vote_i ← ret (g^+(if vi then 1 else 0)%R)%g ;;
          xi ← sample uniform #|'Z_q| ;;
          let xi := (WitnessToField (otf xi : 'Z_q) : v_Z) in
          g_pow_xy ← dl (WitnessToField (FieldToWitness (xi) * (inv g_pow_yi)))%R ;;
            vote_i ← ret ((g_pow_xy : gT) * g^+(if vi then 1 else 0)%R)%g ;;
            commit ← commit_to vote_i ;;
            cds_i ← CDS ((g_pow_xi, g_pow_yi, vote_i), (xi, vi)) ;;
            ret (((zkp_i, g_pow_xi, commit, (cds_i : t_OrZKPCommit, vote_i))) : (((t_SchnorrZKPCommit × v_G) × v_Z) × (t_OrZKPCommit × v_G))%pack)).
  Defined.
  Next Obligation.
    intros.
    unfold full_protocol_interface_step3_obligation_1.
    eapply (valid_package_cons _ _ _ _ _ _ [] []).
    - apply valid_empty_package.
    - intros.
      ssprove_valid.
    - try (rewrite <- fset0E ; setoid_rewrite @imfset0 ; rewrite in_fset0 ; reflexivity).
  Qed.

  Program Definition dl_random2 :
    package fset0
      [interface
         #val #[ DL_RANDOM ] : 'unit → chDLRandom
      ]
      [interface
         #val #[ (DL_RANDOM+1)%nat ] : 'unit → chDLRandom
      ]
    :=
    [package
        #def #[ (DL_RANDOM+1)%nat ] (_ : 'unit) : chDLRandom
        {
          #import {sig #[ DL_RANDOM ] : 'unit → chDLRandom }
          as dl_random ;;
          res ← dl_random Datatypes.tt ;;
          ret res
        }
    ].
  Solve All Obligations with now intros ; destruct from_uint_size.
  Fail Next Obligation.

  Program Definition full_protocol_interface_step4 (state : t_OvnContractState) (i : nat) (vi : 'bool) :
    package fset0
      [interface
         #val #[ SCHNORR ] : schnorrInput → schnorrOutput
       ; #val #[ COMMIT ] : chCommitInput → chCommitOutput
       ; #val #[ GPOWYINOTZERO ] : chGPowYiNotZeroInput → chGPowYiNotZeroOutput
       ; #val #[ CDS ] : CDSinput → CDSoutput
       ; #val #[ DL_RANDOM ] : 'unit → chDLRandom
       ; #val #[ (DL_RANDOM+1)%nat ] : 'unit → chDLRandom
      ]
      [interface
         #val #[ FULL_PROTOCOL_INTERFACE ] : 'unit → chSingleProtocolTranscript
      ] :=
    {package [fmap (FULL_PROTOCOL_INTERFACE, ('unit; (((t_SchnorrZKPCommit × v_G) × (v_Z) × (t_OrZKPCommit × v_G)) ; fun (_ : 'unit) => _)))]}.
  Next Obligation.
    intros.
    refine (
        #import {sig #[ DL ] : chDLInput → chDLOutput }
        as dl ;;
          #import {sig #[ DL_RANDOM ] : 'unit → chDLRandom }
          as dl_random ;;
          #import {sig #[ (DL_RANDOM+1)%nat ] : 'unit → chDLRandom }
          as dl_random2 ;;
          #import {sig #[ SCHNORR ] : schnorrInput → schnorrOutput }
          as schnorr ;;
          #import {sig #[ GPOWYINOTZERO ] : chGPowYiNotZeroInput → chGPowYiNotZeroOutput }
          as g_pow_yi_nz ;;
          #import {sig #[ COMMIT ] : chCommitInput → chCommitOutput }
          as commit_to ;;
          #import {sig #[ CDS ] : CDSinput → CDSoutput }
          as CDS ;;
          '(g_pow_xi,_) ← dl_random Datatypes.tt ;;
          zkp_i ← schnorr (WitnessToField (inv g_pow_xi), g_pow_xi) ;;
          g_pow_yi ← g_pow_yi_nz Datatypes.tt ;;
          '(g_pow_xy,xi) ← dl_random2 Datatypes.tt ;;
          vote_i ← ret ((g_pow_xy : gT) * g^+(if vi then 1 else 0)%R)%g ;;
          commit ← commit_to vote_i ;;
          cds_i ← CDS ((g_pow_xi, g_pow_yi, vote_i), (xi, vi)) ;;
          ret (((zkp_i, g_pow_xi, commit, (cds_i : t_OrZKPCommit, vote_i))) : (((t_SchnorrZKPCommit × v_G) × v_Z) × (t_OrZKPCommit × v_G))%pack)).
  Defined.
  Next Obligation.
    intros.
    unfold full_protocol_interface_step4_obligation_1.
    eapply (valid_package_cons _ _ _ _ _ _ [] []).
    - apply valid_empty_package.
    - intros.
      ssprove_valid.
    - try (rewrite <- fset0E ; setoid_rewrite @imfset0 ; rewrite in_fset0 ; reflexivity).
  Qed.

  (** All steps *)

  Program Definition full_protocol_intantiated (state : t_OvnContractState) (i : nat) (vi : 'bool) : package fset0 [interface]
      [interface
         #val #[ FULL_PROTOCOL_INTERFACE ] : 'unit → chSingleProtocolTranscript
      ] :=
    {package (full_protocol_interface state i vi ∘ par dl_real (par schnorr_real (par (par (GPowYiNotZero_real i state) commit_real) cds_real)))}.
  Next Obligation.
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

    unshelve solve_valid_package.
    all: revgoals.
    all: try (apply fsubsetxx).
    all: try rewrite <- fset0E.
    all: try rewrite !fset0U.
    1: rewrite <- !fset_cat ; simpl.
    all: try (apply fsubsetxx || solve_in_fset).
  Qed.
  Fail Next Obligation.

  (* Theorem valid_link_inv : *)
  (*   forall L I E1 E2 p1 p2, *)
  (*     trimmed E1 p1 -> *)
  (*     trimmed E2 p2 -> *)
  (*     ValidPackage L I (E1 :|: E2) (p1 ∘ p2) -> *)
  (*     ValidPackage L I E1 p1 /\ ValidPackage L I E2 p2. *)
  (* Proof. *)
  (*   intros. *)

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
          symmetry in H16.
          rewrite H16.
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
          2: apply H16.
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
          2: apply H16.
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
  Time Qed.

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
  Solve All Obligations with now intros ; destruct from_uint_size.
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

  Lemma array_update_eq : forall {A : choice_type} (b5 : both (nseq_ A (from_uint_size (is_pure n)))) b (i : int32) H,
      is_pure (array_index
                 (n_seq_array_or_seq
                    (update_at_usize b5 (ret_both i) b)
                    (* (HOGaFE.GroupAndField.OVN.compute_g_pow_yi_obligations_obligation_1 *)
                    (*    (update_at_usize b5 (ret_both i) b)) *)
                    H)
                 (ret_both i)) =
        is_pure b.
  Proof.
    clear ; intros.
    admit.
  Admitted.

  Lemma compute_g_pow_yi_update_eq : forall (b5 : both (nseq_ v_G (from_uint_size (is_pure n)))) b (i : int32),
      is_pure (compute_g_pow_yi
                 (ret_both i)
                 (update_at_usize b5 (ret_both i) b)) =
                 is_pure (compute_g_pow_yi
                            (ret_both i)
                            b5
                          ).
  Proof.
    clear ; intros.
    admit.
  Admitted.

  Lemma real_to_full_protocol_advantage :
    forall state (i : nat) vi,
    ∀ (LA : {fset Location}) (A : raw_package),
      ValidPackage LA [interface #val #[ FULL_PROTOCOL_INTERFACE ] : 'unit → chSingleProtocolTranscript ] A_export A →
      (AdvantageE
         (real_protocol i state vi)
         (full_protocol_interface state i vi ∘ par dl_real (par schnorr_real (par (par (GPowYiNotZero_real i state) commit_real) cds_real)))
         A = 0)%R.
  Proof.
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
    rewrite (hacspec_function_guarantees (fun x => n_seq_array_or_seq x _)).
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

    rewrite <- (hacspec_function_guarantees (fun x => n_seq_array_or_seq x _)).
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
    setoid_rewrite (array_update_eq b0 (ret_both a) i real_protocol_obligation_1).
    subst b0.
    simpl.

    rewrite bind_assoc.

    repeat set (update_at_usize _ _ _).
    Misc.pattern_rhs_approx.
    match goal with | |- context [ ⊢ ⦃ _ ⦄ bind _ ?f ≈ _ ⦃ _ ⦄ ] => set f end.

    apply somewhat_substitution.

    rewrite (hacspec_function_guarantees (fun x => array_index x _)).
    rewrite (hacspec_function_guarantees (fun x => n_seq_array_or_seq x _)).
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


    rewrite <- (hacspec_function_guarantees (fun x => n_seq_array_or_seq x _)).
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

    setoid_rewrite (array_update_eq _ (ret_both _) i real_protocol_obligation_2).
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
    rewrite compute_g_pow_yi_update_eq.
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
    apply somewhat_substitution.
    rewrite !bind_rewrite.
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
        rewrite compute_g_pow_yi_update_eq.
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

    replace (ret _) with (ret (is_pure (ret_both
                                          (is_pure
                                             (compute_group_element_for_vote
                                                (ret_both
                                                (WitnessToField (otf xi)))
                                                (ret_both vi) b))))).
    2:{
      clear.
      repeat set (update_at_usize _ _ _).
      rewrite (hacspec_function_guarantees (fun x => array_index (n_seq_array_or_seq x _) _)).
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
    rewrite H ; clear H.

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
    rewrite H ; clear H.

    subst b4.
    rewrite <- (hacspec_function_guarantees (fun x => array_index (n_seq_array_or_seq x _) _)).

    replace (cast_int (ret_both i)) with (ret_both (i : int32)).
    2:{ apply both_eq.
        simpl.
        unfold cast_int at 1, lift1_both at 1, bind_both, bind_raw_both.
        simpl.
        rewrite wrepr_unsigned.
        reflexivity.
    }

    setoid_rewrite (array_update_eq _ (ret_both _) i real_protocol_obligation_4).
    reflexivity.
    }
    rewrite bind_rewrite.


    rewrite bind_assoc.
    match goal with | |- context [ ⊢ ⦃ _ ⦄ bind (is_state ?a) ?f ≈ _ ⦃ _ ⦄ ] => apply (somewhat_substitution a f) end.

    apply r_ret.
    intros ; split ; [ | easy ].

    clear.

    {
      repeat set (update_at_usize _ _ _).

      eassert (forall state (v : both (nseq_ _ (from_uint_size (is_pure n)))),
                  is_pure (f_commit_vis (Build_t_OvnContractState [ state ] ( f_commit_vis := v)))
                  = is_pure v).
      {
        clear ; intros.
        unfold f_g_pow_xis at 1.
        unfold Build_t_OvnContractState at 1.
        simpl.
        reflexivity.
      }
      rewrite (hacspec_function_guarantees (fun x => array_index (n_seq_array_or_seq x _) _)).
      rewrite <- (hacspec_function_guarantees f_commit_vis).
      rewrite H ; clear H.
      rewrite <- (hacspec_function_guarantees (fun x => array_index (n_seq_array_or_seq x _) _)).

      rewrite array_update_eq.

      rewrite (hacspec_function_guarantees (fun x => array_index (n_seq_array_or_seq x _) _)).
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
    rewrite H ; clear H.
    rewrite <- (hacspec_function_guarantees (fun x => array_index (n_seq_array_or_seq x _) _)).
    simpl.

    rewrite pair_equal_spec ; repeat split ; [ rewrite pair_equal_spec ; repeat split ; [ try rewrite pair_equal_spec ; repeat split.. ].. ].
    1:{
      clear.
      subst b5.

      replace (cast_int (ret_both i)) with (ret_both (i : int32)).
      2:{ apply both_eq.
          simpl.
          unfold cast_int at 1, lift1_both at 1, bind_both, bind_raw_both.
          simpl.
          rewrite wrepr_unsigned.
          reflexivity.
      }

      rewrite array_update_eq.
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
        rewrite H2.
        rewrite H1.
        rewrite H0.
        rewrite H.
        clear H H0 H1 H2.
        rewrite <- (hacspec_function_guarantees (compute_g_pow_yi (ret_both i))).
        
        rewrite compute_g_pow_yi_update_eq.
        Misc.push_down_sides.
        rewrite <- pow_witness_to_field.
        rewrite <- conversion_is_true.
        destruct vi ; [ rewrite rmorph1 | rewrite rmorph0 ] ; reflexivity.
    }
    }
  Fail Timeout 5 Qed. Admitted. (* 319.394 secs *)

  Lemma real_protocol_is_maximum_balloc_secrecy_hiding :
    forall state (i : nat),
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

    1: eapply (real_to_full_protocol_advantage state i true) ; eassumption.

    rewrite Advantage_sym.

    eapply Order.le_trans ; [ eapply Advantage_triangle with (R := _) | ].

    replace (AdvantageE _ _ _) with (@GRing.zero R) ; [ rewrite add0r | symmetry ] ; revgoals.
    1: eapply (real_to_full_protocol_advantage state i false) ; eassumption.

    rewrite Advantage_sym.

    eapply all_step_advantage ; try eassumption.
  Qed.

  (*** /Solution *)

End OVN_proof.

(* (*** Broken examples *) *)

(* Program Definition full_protocol_interface_step2 (state : t_OvnContractState) (i : nat) (vi : 'bool) (f : f_Z -> ((t_SchnorrZKPCommit × v_G) × (v_Z) × (t_OrZKPCommit × v_G))) : *)
(*   package fset0 *)
(*     [interface *)
(*        #val #[ DL ] : chDLInput → chDLOutput *)
(*      ; #val #[ SCHNORR ] : schnorrInput → schnorrOutput *)
(*      ; #val #[ CDS ] : CDSinput → CDSoutput *)
(*      ; #val #[ DL_RANDOM ] : 'unit → chDLRandom *)
(*     ] *)
(*     [interface *)
(*        #val #[ FULL_PROTOCOL_INTERFACE ] : 'unit → chSingleProtocolTranscript *)
(*     ] := *)
(*   [package *)
(*      #def #[ FULL_PROTOCOL_INTERFACE ] (_ : 'unit) : chSingleProtocolTranscript *)
(*      { *)
(*        #import {sig #[ DL ] : chDLInput → chDLOutput } *)
(*        as dl ;; *)
(*        #import {sig #[ SCHNORR ] : schnorrInput → schnorrOutput } *)
(*        as schnorr ;; *)
(*        #import {sig #[ CDS ] : CDSinput → CDSoutput } *)
(*        as CDS ;; *)
(*        #import {sig #[ DL_RANDOM ] : 'unit → chDLRandom } *)
(*        as dl_random ;; *)
(*        '(g_pow_xi, x_other) ← dl_random Datatypes.tt ;; *)
(*        xi ← sample uniform #|'Z_q| ;; *)
(*        let xi : f_Z := WitnessToField (otf xi : 'Z_q) in *)
(*        f xi *)
(*  }]. *)
(* Next Obligation. *)
(*   intros. *)
(*   ssprove_valid. *)
(*   1,2: apply valid_scheme ; rewrite <- fset0E ; apply (ChoiceEquality.is_valid_code (both_prog_valid _)). *)
(* Defined. *)
