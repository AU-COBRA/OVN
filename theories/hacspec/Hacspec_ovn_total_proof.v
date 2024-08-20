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

  (* Import Schnorr_ZKP. *)
  (* Import OR_ZKP. *)

  Include HGPA.

  From OVN Require Import OVN.

  Module OVN_GroupParam <: OVN.GroupParam.

    Definition n : nat := 55.
    Lemma n_pos : Positive n. Proof. easy. Qed.

    Include HGPA.GaFP.HacspecGroup.
  End OVN_GroupParam.

  Module OVN_Param <: OVNParam.
    Definition N : nat := 55.
    Lemma N_pos : Positive N. Proof. easy. Qed.
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

  (* Definition schnorr_zkp (x : full_protocol_transcript) := *)
  (*   let '(schnorr_zkp, ddh_pk, commit, or, vote) := x in *)
  (*   schnorr_zkp. *)

  Notation " 'chInputOvn' " :=
    (protocol_input)
    (in custom pack_type at level 2).

  Notation " 'chTranscriptOvn' " :=
    (full_protocol_transcript)
    (in custom pack_type at level 2).

  Notation " 'chRound1output' " :=
    (t_SchnorrZKPCommit × v_G)
    (in custom pack_type at level 2).

  Definition ROUND1 : nat := 12.

  Program Definition round1 (i : nat) (xi : f_Z) (state : both t_OvnContractState) :
    package fset0
      [interface]
      [interface #val #[ ROUND1 ] : 'unit → chRound1output]
    :=
    [package
        #def #[ ROUND1 ] (_ : 'unit) : chRound1output
        {
          ri ← sample (uniform #|'Z_q|) ;;
          temp ← is_state (register_vote (ret_both ((i, xi, WitnessToField (otf ri)) : t_RegisterParam)) state) ;;
          match temp : t_Result (v_A × t_OvnContractState) t_ParseError with
          | Result_Ok_case (_ , new_state) =>
              zkp_i ← is_state (A := t_SchnorrZKPCommit) ((f_zkp_xis (ret_both (new_state : t_OvnContractState))).a[ ret_both (i : int32) ]) ;;
              g_pow_xi ← is_state ((f_g_pow_xis (ret_both (new_state : t_OvnContractState))).a[ ret_both (i : int32) ]) ;;
              ret (zkp_i , g_pow_xi)
          | Result_Err_case _ => ret (chCanonical t_SchnorrZKPCommit, chCanonical _)
          end
        }
    ].
  Solve All Obligations with now intros ; destruct from_uint_size.
  Next Obligation.
    fold chElement.
    intros.
    rewrite <- fset0E.
    ssprove_valid_package.
    ssprove_valid.
    1: apply (ChoiceEquality.is_valid_code (both_prog_valid _)).
    ssprove_valid'_2 ;  apply (ChoiceEquality.is_valid_code (both_prog_valid _)).
  Qed.
  Fail Next Obligation.

  Notation " 'chRound2output' " :=
    (f_Z)
    (in custom pack_type at level 2).

  Definition ROUND2 : nat := 15 + OVN_Param.N.

  Notation " 'chRound2input' " :=
    (f_Z × f_Z × f_Z)
    (in custom pack_type at level 2).

  Program Definition round2 (i : nat) (xi : f_Z) (vi : bool) (state : both t_OvnContractState) :
    package fset0
      [interface]
      [interface #val #[ ROUND2 ] : chRound2input → chRound2output]
    :=
    [package
        #def #[ ROUND2 ] ('(w,r,d) : chRound2input) : chRound2output
        {
          temp ← is_state (commit_to_vote (ret_both ((i, xi, w, r, d, vi) : t_CastVoteParam)) state) ;;
          match temp : t_Result (v_A × t_OvnContractState) t_ParseError with
          | Result_Ok_case (_ , new_state) =>
              is_state (A := f_Z) ((f_commit_vis (ret_both (new_state : t_OvnContractState))).a[ ret_both (i : int32) ])
          | Result_Err_case _ => ret (chCanonical _)
          end
        }
    ].
  Solve All Obligations with now intros ; destruct from_uint_size.
  Next Obligation.
    fold chElement.
    intros.
    rewrite <- fset0E.
    ssprove_valid_package.
    destruct x as [[w r] d].
    ssprove_valid.
    1: apply (ChoiceEquality.is_valid_code (both_prog_valid _)).
    ssprove_valid'_2 ;  apply (ChoiceEquality.is_valid_code (both_prog_valid _)).
  Qed.
  Fail Next Obligation.

  Notation " 'chRound3input' " :=
    (f_Z × f_Z × f_Z)
    (in custom pack_type at level 2).

  Notation " 'chRound3output' " :=
    (v_G × t_OrZKPCommit)
    (in custom pack_type at level 2).

  Definition ROUND3 : nat := 15 + 2 * OVN_Param.N.

  Import OR_ZKP.proof_args.Sigma.

  Program Definition simple_round3 (i : nat) (xi : f_Z) (vi : bool) (state : both t_OvnContractState) :
    package fset0
      [interface]
      [interface #val #[ ROUND3 ] : chRound3input → chRound3output]
    :=
    [package
        #def #[ ROUND3 ] ('(w,r,d) : chRound3input) : chRound3output
        {
          #import {sig #[ OR_ZKP.proof_args.Sigma.RUN ] : chRelation → chTranscript } as RUN_OR ;;

          temp ← is_state (cast_vote (ret_both ((i, xi, w, r, d, vi) : t_CastVoteParam)) state) ;;
          match temp : t_Result (v_A × t_OvnContractState) t_ParseError with
          | Result_Ok_case (_ , new_state) =>
              vote_i ← is_state (A := v_G) ((f_g_pow_xi_yi_vis (ret_both (new_state : t_OvnContractState))).a[ ret_both (i : int32) ]) ;;
              or_zkp_i ← is_state (A := t_OrZKPCommit) ((f_zkp_vis (ret_both (new_state : t_OvnContractState))).a[ ret_both (i : int32) ]) ;;
              ret (vote_i, or_zkp_i)
          | Result_Err_case _ => ret (chCanonical _, chCanonical _)
          end
        }
    ].
  Solve All Obligations with now intros ; destruct from_uint_size.
  Next Obligation.
    fold chElement.
    intros.
    ssprove_valid_package.
    destruct x as [[w r] d].
    ssprove_valid.
    1: apply valid_scheme ; rewrite <- fset0E ; apply (ChoiceEquality.is_valid_code (both_prog_valid _)).
    ssprove_valid'_2 ;  apply valid_scheme ; rewrite <- fset0E ; apply (ChoiceEquality.is_valid_code (both_prog_valid _)).
  Qed.
  Fail Next Obligation.

  Import DDH.
  Module DDHParams <: DDHParams.
    Definition Space := 'Z_q : finType.
    Definition Space_pos : Positive #|Space|.
    Proof.
      apply /card_gt0P. exists 0%R. auto.
    Qed.
  End DDHParams.
  Module DDH := DDH DDHParams HGPA.GaFP.HacspecGroup.

  Import DDH.

  Program Definition round3 (i : nat) (xi : f_Z) (vi : bool) (state : both t_OvnContractState) :
    package fset0
      [interface #val #[ OR_ZKP.proof_args.Sigma.RUN ] : chRelation → chTranscript]
      [interface #val #[ ROUND3 ] : chRound3input → chRound3output]
    :=
    [package
        #def #[ ROUND3 ] ('(w,r,d) : chRound3input) : chRound3output
        {
          #import {sig #[ OR_ZKP.proof_args.Sigma.RUN ] : chRelation → chTranscript } as RUN_OR ;;

          (* TODO: use DDH here.. *)
          let compute_group_element_for_vote := (fun (xi : both f_Z) (vote : both 'bool) (g_pow_yi : both v_G) =>
                                                   solve_lift (f_prod (f_pow g_pow_yi xi) (f_g_pow (ifb vote
                                                                                                    then f_field_one
                                                                                                    else f_field_zero))) : both v_G) in
    
          let cast_vote := fun (params : both t_CastVoteParam) (state : both (t_OvnContractState)) => 
                             g_pow_yi ← is_state (compute_g_pow_yi (cast_int (WS2 := U32) (f_cvp_i params)) (f_g_pow_xis state)) ;;
    zkp_vi ← RUN_OR (fto (g ^+ FieldToWitness xi, g_pow_yi : gT, (g_pow_yi : gT)), fto ( FieldToWitness xi , vi , (g_pow_yi : gT) )) ;;
    let zkp_vi := OR_ZKP.or_sigma_ret_to_hacspec_ret zkp_vi in
    (* zkp_vi ← is_state (zkp_one_out_of_two (f_cvp_zkp_random_w params) (f_cvp_zkp_random_r params) (f_cvp_zkp_random_d params) (ret_both g_pow_yi) (f_cvp_xi params) (f_cvp_vote params)) ;; *)
    is_state (letb g_pow_xi_yi_vi := compute_group_element_for_vote (f_cvp_xi params) (f_cvp_vote params) (ret_both g_pow_yi) in
    letb cast_vote_state_ret := f_clone state in
    letb cast_vote_state_ret := Build_t_OvnContractState[cast_vote_state_ret] (f_g_pow_xi_yi_vis := update_at_usize (f_g_pow_xi_yi_vis cast_vote_state_ret) (cast_int (WS2 := U32) (f_cvp_i params)) g_pow_xi_yi_vi) in
    letb cast_vote_state_ret := Build_t_OvnContractState[cast_vote_state_ret] (f_zkp_vis := update_at_usize (f_zkp_vis cast_vote_state_ret) (cast_int (WS2 := U32) (f_cvp_i params)) (ret_both zkp_vi)) in
    Result_Ok (prod_b (f_accept,cast_vote_state_ret)) : both (t_Result (v_A × t_OvnContractState) t_ParseError)) in


          temp ← (cast_vote (ret_both ((i, xi, w, r, d, vi) : t_CastVoteParam)) state) ;;
          match temp : t_Result (v_A × t_OvnContractState) t_ParseError with
          | Result_Ok_case (_ , new_state) =>
              vote_i ← is_state (A := v_G) ((f_g_pow_xi_yi_vis (ret_both (new_state : t_OvnContractState))).a[ ret_both (i : int32) ]) ;;
              or_zkp_i ← is_state (A := t_OrZKPCommit) ((f_zkp_vis (ret_both (new_state : t_OvnContractState))).a[ ret_both (i : int32) ]) ;;
              ret (vote_i, or_zkp_i)
          | Result_Err_case _ => ret (chCanonical _, chCanonical _)
          end
        }
    ].
  Solve All Obligations with now intros ; destruct from_uint_size.
  Solve All Obligations with now intros ; simpl ; destruct (Z.to_nat _).
  Next Obligation.
    intros.
    ssprove_valid_package.
    destruct x as [[w r] d].
    ssprove_valid.
    1: apply valid_scheme ; rewrite <- fset0E ; apply (ChoiceEquality.is_valid_code (both_prog_valid _)).
    all: ssprove_valid'_2 ;  apply valid_scheme ; rewrite <- fset0E ; apply (ChoiceEquality.is_valid_code (both_prog_valid _)).
  Qed.
  Fail Next Obligation.

  Notation " 'chProtocolOutput' " :=
    ((t_SchnorrZKPCommit × v_G) × f_Z × (v_G × t_OrZKPCommit))
    (in custom pack_type at level 2).

  Definition PROTOCOL : nat := 15 + 3 * OVN_Param.N.

  Program Definition protocol :
    package fset0
      [interface
         #val #[ ROUND1 ] : 'unit → chRound1output ;
         #val #[ ROUND2 ] : chRound2input → chRound2output ;
         #val #[ ROUND3 ] : chRound3input → chRound3output
      ]
      [interface #val #[ PROTOCOL ] : 'unit → chProtocolOutput]
    :=
    [package
        #def #[ PROTOCOL ] (_ : 'unit) : chProtocolOutput
        {
#import {sig #[ ROUND1 ] : 'unit → chRound1output } as R1 ;;
          #import {sig #[ ROUND2 ] : chRound2input → chRound2output } as R2 ;;
          #import {sig #[ ROUND3 ] : chRound3input → chRound3output } as R3 ;;

          (* xi ← sample (uniform #|'Z_q|) ;; let xi := WitnessToField (otf xi) in *)
          round_1 ← R1 Datatypes.tt ;;

          w ← sample (uniform #|'Z_q|) ;;
          r ← sample (uniform #|'Z_q|) ;;
          d ← sample (uniform #|'Z_q|) ;;
          round_2 ← R2 (WitnessToField (otf w), WitnessToField (otf r), WitnessToField (otf d)) ;;
          round_3 ← R3 (WitnessToField (otf w), WitnessToField (otf r), WitnessToField (otf d)) ;;

          ret ((round_1, round_2), round_3)
        }
    ].
  Solve All Obligations with now intros ; destruct from_uint_size.
  Fail Next Obligation.

  Definition r_bind_feq :
               forall {A B} (a b : raw_code A) (f g : A -> raw_code B) post,
               ⊢ ⦃ λ '(s₀, s₁), s₀ = s₁ ⦄ a ≈ b ⦃ Logic.eq ⦄
               → (∀ (a₀ : A), ⊢ ⦃ λ '(s₀, s₁), s₀ = s₁ ⦄ f a₀ ≈ g a₀ ⦃ post ⦄) →
               ⊢ ⦃ λ '(s₀, s₁), s₀ = s₁ ⦄ x ← a ;; f x ≈ x ← b ;; g x ⦃ post ⦄.
  Proof.
    intros.
    eapply r_bind with (mid := pre_to_post (λ '(s₀, s₁), s₀ = s₁)) ;
      [eapply rpost_weaken_rule ; [ apply H | now intros [] [] ? ]
      | intros ].
    apply rpre_hypothesis_rule ; intros ? ? [] ; eapply rpre_weaken_rule with (pre := (λ '(s₀, s₁), s₀ = s₁)) ; [ subst ; apply H0 | now simpl ; intros ? ? [] ].
  Qed.

  Definition somewhat_substitution : forall {A : choice_type} {B : choiceType} (b : both A) (f : A -> raw_code B) (c : raw_code B) pre,
      ⊢ ⦃ λ '(s₀, s₁), pre (s₀, s₁) ⦄ temp ← ret (is_pure b) ;; f temp ≈ c ⦃ λ '(b₀, s₀) '(b₁, s₁), b₀ = b₁ ∧ pre (s₀, s₁) ⦄ ->
      ⊢ ⦃ λ '(s₀, s₁), pre (s₀, s₁) ⦄ temp ← is_state b ;; f temp ≈ c ⦃ λ '(b₀, s₀) '(b₁, s₁), b₀ = b₁ ∧ pre (s₀, s₁) ⦄.
  Proof.
    clear ; intros ? ? ? ? ? ?.

    eapply r_transL.
    eapply r_bind.

    - apply r_nice_swap_rule ; [ easy | | apply p_eq ] ; now intros [] [] ; cbn.
    - intros.
      simpl.
      apply Misc.rpre_hypothesis_rule'.
      intros ? ? [[]].
      eapply rpre_weaken_rule.
      1: subst ; apply rreflexivity_rule.
      intros ? ? [].
      now subst.
  Qed.

  Definition somewhat_substitutionR : forall {A : choice_type} {B : choiceType} (b : both A) (f : A -> raw_code B) (c : raw_code B) pre,
      ⊢ ⦃ λ '(s₀, s₁), pre (s₀, s₁) ⦄ c ≈ temp ← ret (is_pure b) ;; f temp ⦃ λ '(b₀, s₀) '(b₁, s₁), b₀ = b₁ ∧ pre (s₀, s₁) ⦄ ->
      ⊢ ⦃ λ '(s₀, s₁), pre (s₀, s₁) ⦄ c ≈ temp ← is_state b ;; f temp ⦃ λ '(b₀, s₀) '(b₁, s₁), b₀ = b₁ ∧ pre (s₀, s₁) ⦄.
  Proof.
    clear ; intros ? ? ? ? ? ?.

    eapply r_transR.
    eapply r_bind.

    - apply r_nice_swap_rule ; [ easy | | apply p_eq ] ; now intros [] [] ; cbn.
    - intros.
      simpl.
      apply Misc.rpre_hypothesis_rule'.
      intros ? ? [[]].
      eapply rpre_weaken_rule.
      1: subst ; apply rreflexivity_rule.
      intros ? ? [].
      now subst.
  Qed.

  Lemma somewhat_let_substitution :
             forall {A C : choice_type} {B : choiceType} (f : C -> raw_code B) (c : raw_code B) (y : both A) (r : both A -> both C) pre,
               ⊢ ⦃ pre ⦄ b_temp ← is_state y ;; temp ← is_state (r (ret_both b_temp)) ;; f temp ≈ c ⦃ λ '(b₀, s₀) '(b₁, s₁), b₀ = b₁ ∧ pre (s₀, s₁) ⦄ ->
               ⊢ ⦃ pre ⦄ temp ← is_state (letb 'b := y in r ((b))) ;; f temp ≈ c ⦃ λ '(b₀, s₀) '(b₁, s₁), b₀ = b₁ ∧ pre (s₀, s₁) ⦄.
  Proof.
    intros.
    unfold let_both at 1.

    eapply r_transL.
    2:{ apply H. }
    rewrite <- bind_assoc.
    apply r_bind_feq.
    2:intros ; eapply rpost_weaken_rule ; [ apply rreflexivity_rule | now intros [] [] H0 ; inversion H0 ].

    pose (determ := (fun (y : both A) => both_deterministic y)).
    pose (y_det := both_deterministic y).

    pose (hd₀ := determ ).
    pose (hd₁ := deterministic_bind _ _ y_det (fun x => determ (ret_both x))).
    simpl in hd₁.

    eapply r_transL.
    1:{
      apply r_bind_feq.
      1:{
        apply r_nice_swap_rule ; [ easy | easy | ].
        epose p_eq.
        eapply rpost_weaken_rule.
        1: apply r0.
        1:now intros [] [] [[] ?].
      }
      intros.
      apply rreflexivity_rule.
    }
    simpl.

    apply both_pure_eq.
    now rewrite <- hacspec_function_guarantees.
  Qed.

  Lemma somewhat_let_substitutionR :
             forall {A C : choice_type} {B : choiceType} (f : C -> raw_code B) (c : raw_code B) (y : both A) (r : both A -> both C) pre,
               ⊢ ⦃ pre ⦄ c ≈ b_temp ← is_state y ;; temp ← is_state (r (ret_both b_temp)) ;; f temp ⦃ λ '(b₀, s₀) '(b₁, s₁), b₀ = b₁ ∧ pre (s₀, s₁) ⦄ ->
               ⊢ ⦃ pre ⦄ c ≈ temp ← is_state (letb 'b := y in r ((b))) ;; f temp ⦃ λ '(b₀, s₀) '(b₁, s₁), b₀ = b₁ ∧ pre (s₀, s₁) ⦄.
  Proof.
    intros.
    eapply r_transR.
    2:{ apply H. }
    rewrite <- bind_assoc.
    apply r_bind_feq.
    2:intros ; eapply rpost_weaken_rule ; [ apply rreflexivity_rule | now intros [] [] H0 ; inversion H0 ].

    pose (determ := (fun (y : both A) => both_deterministic y)).
    pose (y_det := both_deterministic y).

    pose (hd₀ := determ ).
    pose (hd₁ := deterministic_bind _ _ y_det (fun x => determ (ret_both x))).
    simpl in hd₁.

    eapply r_transL.
    1:{
      apply r_bind_feq.
      1:{
        apply r_nice_swap_rule ; [ easy | easy | ].
        epose p_eq.
        eapply rpost_weaken_rule.
        1: apply r0.
        1:now intros [] [] [[] ?].
      }
      intros.
      apply rreflexivity_rule.
    }
    simpl.

    apply both_pure_eq.
    now rewrite <- hacspec_function_guarantees.
  Qed.

  Ltac ssprove_valid_code :=
    rewrite <- fset0E
    ; ssprove_valid
    ; try match goal with
        | [ |- context [ is_state ?b ] ] =>
            apply (ChoiceEquality.is_valid_code (both_prog_valid b))
        end
    ; ssprove_valid'_2 ; apply (ChoiceEquality.is_valid_code (both_prog_valid _)).

  Ltac ssprove_same_head n :=
      apply (rsame_head_alt (L := fset0)) ; [ ssprove_valid_code | done | done | intros n ].

  Ltac ssprove_refl :=
      apply (r_reflexivity_alt (L := fset0)) ; [ ssprove_valid_code | done | done ].

  Ltac ssprove_sym :=
    apply r_nice_swap_rule ; [ easy | | apply p_eq ] ; now intros [] [] ; cbn.

  Lemma fsubset_trans : forall (T : ordType) (a b c : {fset T}), a :<=: b -> b :<=: c -> a :<=: c.
  Proof.
    clear ; intros.
    apply /fsetUidPr.
    apply (ssrbool.elimT fsetUidPr) in H.
    apply (ssrbool.elimT fsetUidPr) in H0.
    rewrite <- H0 at 2.
    rewrite <- H.
    rewrite <- fsetUA.
    rewrite H0.
    reflexivity.
  Qed.

  Lemma trimmed_par :
    forall I1 I2 a b, Parable (trim I1 a) (trim I2 b) -> trimmed (I1 :|: I2) (par (trim I1 a) (trim I2 b)).
  Proof.
    clear ; intros.
    unfold trimmed.
    unfold trim.
    simpl.
    unfold par.

    rewrite filterm_union.
    1:{
      assert (forall (T : ordType) (S : Type) (a : {fmap T -> S}) (f g : T -> S -> bool),
            filterm f (filterm g a) = filterm (fun t s => f t s && g t s) a).
      {
        clear ; intros T S a f g.

        unfold filterm.
        simpl.
        apply eq_fmap.
        intros ?.
        cbn.
        f_equal.
        destruct a.
        simpl.
        clear i.
        induction fmval.
        - reflexivity.
        - cbn.
          destruct g ; simpl ; destruct f ; simpl;  now rewrite IHfmval.
      }

      rewrite H0.
      rewrite H0.
      f_equal.
      1:{
        apply eq_filterm.
        intros ? ?.
        destruct y as [? [? ?]].
        rewrite in_fsetU.
        set  (_ \in _).
        set  (_ \in _).
        now destruct b0.
      }
      1:{
        apply eq_filterm.
        intros ? ?.
        destruct y as [? [? ?]].
        rewrite in_fsetU.
        set  (_ \in _).
        set  (_ \in _).
        now destruct b1.
      }
    }
    apply H.
  Qed.

  Ltac solve_Parable :=
    match goal with
    | [ |- context [ Parable (trim _ ?a) (trim _ ?b) ] ] =>
        apply parable_trim
        ; try (unfold idents
               ; rewrite <- !fset1E
               ; rewrite !imfset1
               ; now rewrite fdisjoint1s)
    end.

  Ltac solve_trimmed :=
    match goal with
    | [ |- context [ trimmed ?I (trim ?I ?a) ] ] =>
        now unfold trimmed ; rewrite trim_idemp
    | [ |- context [ trimmed _ (trim ?I2 ?b ∘ ?c) ] ] =>
        rewrite link_trim_commut ;
        solve_trimmed
          
    | [ |- context [ trimmed _ (par (trim _ ?a) (trim _ ?b ∘ ?c)) ] ] =>
        rewrite link_trim_commut ;
        solve_trimmed
    | [ |- context [ trimmed _ (par ?a ?b) ] ] =>
        apply trimmed_par ; solve_Parable
    end.

  Ltac solve_valid_package :=
    match goal with
    | [ |- context [ ValidPackage ?L ?I ?E (pack ?a) ] ] =>
        apply a
    | [ |- context [ ValidPackage ?L ?I ?E (trim ?T ?a) ] ] =>
        apply valid_trim ; solve_valid_package
    | [ |- context [ ValidPackage ?L ?I ?E (?a ∘ ?b) ] ] =>
        eapply valid_link ; solve_valid_package
    | [ |- context [ ValidPackage ?L ?I ?E (?a ∘ ?b) ] ] =>
        eapply valid_link_upto ; [ solve_valid_package | solve_valid_package | apply fsubsetxx || solve_in_fset | apply fsubsetxx || solve_in_fset ]
    | [ |- context [ ValidPackage ?L ?I ?E (par (trim _ ?a) (trim _ ?b)) ] ] =>
        eapply valid_par ; [
          solve_Parable
        | solve_valid_package | solve_valid_package ]
    | [ |- context [ ValidPackage ?L ?I ?E (par (trim _ ?a) (trim _ ?b)) ] ] =>
        eapply valid_par_upto ; [
          solve_Parable
        | solve_valid_package | solve_valid_package | apply fsubsetxx || solve_in_fset.. ]
    | [ |- context [ ValidPackage ?L ?I ?E (par (trim _ ?a) (trim _ ?b ∘ ?c)) ] ] =>
        rewrite link_trim_commut ;
        solve_valid_package
    | _ => idtac
    end.

  Ltac unfold_advantageE :=
    match goal with
    | [ |- context [ AdvantageE (?a ∘ ?b) (?a ∘ ?c) ] ] =>
        rewrite <- Advantage_link
    | [ |- context [ AdvantageE (par ?a (?b)) (par ?a (?c)) ?A ] ] =>
        erewrite (Advantage_par a b c A _ _ _ _ _)
        ; [
        | solve_valid_package | solve_valid_package | solve_valid_package
        |
        | solve_trimmed | solve_trimmed | solve_trimmed ]
    (* | [ |- context [ AdvantageE (par ?a (?b)) (par ?a (?c)) ?A ] ] => *)
    (*     pose 2%nat *)
    | _ => idtac
    end.

  Import OR_ZKP.proof_args.MyAlg.
  (* Import OR_ZKP.proof_args.MyParam. *)
  Import OR_ZKP.proof_args.Sigma.
  
  Notation " 'SHVZK_chInput' " :=
    (chProd (chProd OR_ZKP.proof_args.MyAlg.choiceStatement OR_ZKP.proof_args.MyAlg.choiceWitness) OR_ZKP.proof_args.MyAlg.choiceChallenge)
      (in custom pack_type at level 2).

  Notation " 'SHVZK_chTranscript' " :=
    (OR_ZKP.proof_args.MyAlg.choiceTranscript)
      (in custom pack_type at level 2).

  Notation " 'SHVZK_chRelation' " :=
    (chProd OR_ZKP.proof_args.MyAlg.choiceStatement OR_ZKP.proof_args.MyAlg.choiceWitness)
      (in custom pack_type at level 2).

  Definition SHVZK_ideal_aux : package (fset [::]) [interface #val #[ OR_ZKP.proof_args.Sigma.TRANSCRIPT ] : SHVZK_chInput → SHVZK_chTranscript ] [interface #val #[OR_ZKP.proof_args.Sigma.RUN] : SHVZK_chRelation → SHVZK_chTranscript ]
    :=
    [package
        #def #[ OR_ZKP.proof_args.Sigma.RUN ] (hw : SHVZK_chRelation) : SHVZK_chTranscript
        {
          #import {sig #[ OR_ZKP.proof_args.Sigma.TRANSCRIPT ] : SHVZK_chInput → SHVZK_chTranscript } as SHVZK ;;
          e ← sample uniform #|OR_ZKP.proof_args.MyParam.Challenge| ;;
          t ← SHVZK (hw, e) ;;
          ret t
        }
    ].

  Ltac trim_is_interface :=
    setoid_rewrite filterm_set ; simpl ; fold chElement ;
    rewrite <- fset1E ;
    rewrite in_fset1 ;
    simpl ;
    rewrite eqxx ;
    rewrite filterm0 ;
    reflexivity.

  Lemma maximum_ballot_secrecy_helper :
    forall (i : nat) (xi : f_Z) state,
    ∀ (LA : {fset Location}) (A : raw_package),
     ValidPackage LA [interface #val #[ PROTOCOL ] : 'unit → chProtocolOutput ] A_export A →
     fdisjoint LA OR_ZKP.proof_args.MyAlg.Sigma_locs →
     forall vi,
      AdvantageE
        (protocol ∘ (par (round1 i xi state) (par (round2 i xi vi state) (round3 i xi vi state ∘ OR_ZKP.hacspec_or_run))))
        ((protocol ∘ (par (round1 i xi state) (par (round2 i xi vi state) (round3 i xi vi state ∘ (SHVZK_ideal_aux ∘ SHVZK_ideal))))))
      A = 0%R.
  Proof.
    intros.

    assert (trimmed [interface #val #[ ROUND1 ] : 'unit → chRound1output] (round1 i xi state)) by now unfold trimmed ; trim_is_interface.
    assert (trimmed [interface #val #[ ROUND2 ] : chRound2input → chRound2output] (round2 i xi vi state)) by now unfold trimmed ; trim_is_interface.
    assert (trimmed [interface #val #[ ROUND3 ] : chRound3input → chRound3output] (round3 i xi vi state)) by now unfold trimmed ; trim_is_interface.
    
    rewrite <- H1.
    rewrite <- H2.
    rewrite <- H3.
    (* rewrite !link_trim_commut. *)

    unfold_advantageE.
    unfold_advantageE.
    2:{
      clear.
      unfold flat.

      intros n u1 u2.
      rewrite !in_fsetU.
      now do 2 (let H := fresh in
                intros H
                ; apply (ssrbool.elimT ssrbool.orP) in H
                ; destruct H
                ; rewrite <- fset1E in H
                ; rewrite in_fset1 in H
                ; apply (ssrbool.elimT eqP) in H
                ; inversion H ; subst).
    }

      unfold_advantageE.
      2:{
        clear.
        unfold flat.

        intros n u1 u2.
        now do 2 (let H := fresh in
                  intros H
                  ; rewrite <- fset1E in H
                  ; rewrite in_fset1 in H
                  ; apply (ssrbool.elimT eqP) in H
                  ; inversion H ; subst).
      }

      unfold_advantageE.

      apply (AdvantageE_le_0 _ _ _ ).
      eapply Order.le_trans ; [ apply Advantage_triangle with (R := (SHVZK_real_aux ∘ SHVZK_real)) | ].

      replace (AdvantageE _ _ _) with (@GRing.zero R) ; [ | symmetry ].
      2:{

        rewrite (OR_ZKP.run_interactive_or_shvzk LA _ _ _) ; [ done | .. ].
        2: assumption.
        1:{
          eapply (valid_link_upto).
          1:{
            eapply (valid_link).
            1:{
              eapply (valid_link).
              1:{
                eapply (valid_link).
                1:{
                  apply H.
                }
                solve_valid_package.
              }
              eapply valid_par_upto.
              2:{
                solve_valid_package.
              }
              2:{
                apply valid_ID.
                {
                  clear.
                  unfold flat.

                  intros n u1 u2.
                  rewrite !in_fsetU.
                  now do 2 (let H := fresh in
                            intros H
                            ; apply (ssrbool.elimT ssrbool.orP) in H
                            ; destruct H
                            ; rewrite <- fset1E in H
                            ; rewrite in_fset1 in H
                            ; apply (ssrbool.elimT eqP) in H
                            ; inversion H ; subst).
                }
              }
              1:{
                rewrite <- trimmed_ID.
                solve_Parable.
                try (unfold idents).
                rewrite <- !fset1E.
                rewrite imfsetU.
                rewrite !imfset1.
                rewrite fdisjoint1s.
                rewrite in_fset.
                easy.
              }
              2: rewrite <- fset0E ; rewrite fset0U ; apply fsubsetxx.
              1: apply fsubsetxx.
              solve_in_fset.
            }

            rewrite <- trimmed_ID.
            solve_valid_package.
            1:{
              apply valid_ID.
              {
                clear.
                unfold flat.

                intros n u1 u2.
                now do 2 (let H := fresh in
                          intros H
                          ; rewrite <- fset1E in H
                          ; rewrite in_fset1 in H
                          ; apply (ssrbool.elimT eqP) in H
                          ; inversion H ; subst).
              }
            }
          }
          1:{
            rewrite <- fset0E. rewrite fset0U.
            solve_valid_package.
          }
          2: apply fsub0set.
          1:{
            Unshelve.
            2, 3: apply fset0.
            rewrite !fset0U.
            rewrite !fsetU0.
            apply fsubsetxx.
          }
        }
      }
      rewrite add0r.

      rewrite <- Advantage_link.

      erewrite OR_ZKP.shvzk_success with (LA := _) ; [ | .. ].
      2:{
        solve_valid_package.
        1: apply H.
        1:{
          rewrite <- trimmed_ID.
          solve_valid_package.
          1:{
            try (unfold idents).
            rewrite <- !fset1E.
            rewrite imfsetU.
            rewrite !imfset1.
            rewrite fdisjoint1s.
            rewrite in_fset.
            easy.
          }
          apply valid_ID.
          {
            clear.
            unfold flat.

            intros n u1 u2.
            rewrite !in_fsetU.
            now do 2 (let H := fresh in
                      intros H
                      ; apply (ssrbool.elimT ssrbool.orP) in H
                      ; destruct H
                      ; rewrite <- fset1E in H
                      ; rewrite in_fset1 in H
                      ; apply (ssrbool.elimT eqP) in H
                      ; inversion H ; subst).
          }
        }
        1:{
          rewrite <- trimmed_ID.
          rewrite <- fset0E ; rewrite fset0U.
          eapply valid_par_upto.
          2:{
            solve_valid_package.}
            2:{
              solve_valid_package.
              apply valid_ID.
              {
                clear.
                unfold flat.

                intros n u1 u2.
                now do 2 (let H := fresh in
                          intros H
                          ; rewrite <- fset1E in H
                          ; rewrite in_fset1 in H
                          ; apply (ssrbool.elimT eqP) in H
                          ; inversion H ; subst).
              }
            }
            1: solve_Parable.
          all: apply fsubsetxx || solve_in_fset.
        }
      }
      1: easy.
      Unshelve.
      2, 3: apply fset0.
      rewrite <- fset0E.
      rewrite !fset0U.
      rewrite !fsetU0.
      assumption.
  Qed.

  Lemma maximum_ballot_secrecy :
    forall (i : nat) (xi : f_Z) state,
    ∀ (LA : {fset Location}) (A : raw_package),
     ValidPackage LA [interface #val #[ PROTOCOL ] : 'unit → chProtocolOutput ] A_export A →
     fdisjoint LA OR_ZKP.proof_args.MyAlg.Sigma_locs →
     let prot := fun vi => (protocol ∘ (par (round1 i xi state) (par (round2 i xi vi state) (round3 i xi vi state ∘ OR_ZKP.hacspec_or_run)))) in
      AdvantageE
        (prot true)
        (prot false)
      A = 0%R.
  Proof.
    intros.

    subst prot ; hnf.

    apply (AdvantageE_le_0 _ _ _ ).
    eapply Order.le_trans ; [ apply Advantage_triangle with (R := (protocol
        ∘ par (round1 i xi state)
            (par (round2 i xi true state) (round3 i xi true state ∘ SHVZK_ideal_aux ∘ SHVZK_ideal)))) | ].

    rewrite (maximum_ballot_secrecy_helper i xi state LA A H H0 true) ; rewrite add0r.

    rewrite Advantage_sym.
    eapply Order.le_trans ; [ apply Advantage_triangle with (R := (protocol
                                                                     ∘ par (round1 i xi state)
                                                                     (par (round2 i xi false state) (round3 i xi false state ∘ SHVZK_ideal_aux ∘ SHVZK_ideal)))) | ].
    rewrite (maximum_ballot_secrecy_helper i xi state LA A H H0 false) ; rewrite add0r.
    rewrite Advantage_sym.

    assert (trimmed [interface #val #[ ROUND1 ] : 'unit → chRound1output] (round1 i xi state)) by now unfold trimmed ; trim_is_interface.
    assert (trimmed [interface #val #[ ROUND2 ] : chRound2input → chRound2output] (round2 i xi true state)) by now unfold trimmed ; trim_is_interface.
    assert (trimmed [interface #val #[ ROUND3 ] : chRound3input → chRound3output] (round3 i xi true state)) by now unfold trimmed ; trim_is_interface.
    assert (trimmed [interface #val #[ ROUND2 ] : chRound2input → chRound2output] (round2 i xi false state)) by now unfold trimmed ; trim_is_interface.
    assert (trimmed [interface #val #[ ROUND3 ] : chRound3input → chRound3output] (round3 i xi false state)) by now unfold trimmed ; trim_is_interface.

    rewrite <- H1.
    rewrite <- H2.
    rewrite <- H3.
    rewrite <- H4.
    rewrite <- H5.
    (* rewrite !link_trim_commut. *)

    unfold_advantageE.
    unfold_advantageE.
    2:{
      clear.
      unfold flat.

      intros n u1 u2.
      rewrite !in_fsetU.
      now do 2 (let H := fresh in
                intros H
                ; apply (ssrbool.elimT ssrbool.orP) in H
                ; destruct H
                ; rewrite <- fset1E in H
                ; rewrite in_fset1 in H
                ; apply (ssrbool.elimT eqP) in H
                ; inversion H ; subst).
    }

    replace (AdvantageE _ _ _) with (@GRing.zero R) ; [ easy | symmetry ].

    apply: eq_rel_perf_ind_ignore.
    all: fold chElement.

    1:{
      eapply valid_par_upto.
      2,3: solve_valid_package.
      2,3,4: apply fsubsetxx || solve_in_fset.
      rewrite link_trim_commut.
      solve_Parable.
    }

    1:{
      eapply valid_par_upto.
      2,3: solve_valid_package.
      2,3,4: apply fsubsetxx || solve_in_fset.
      rewrite link_trim_commut.
      solve_Parable.
    }

    1: rewrite fset0U ; apply fsubsetxx.

    2:{
      solve_valid_package.
      1: apply H.
      rewrite <- trimmed_ID.

      eapply valid_par_upto.
      2: solve_valid_package.
      2:{
        apply valid_trim.
        apply valid_ID.
        {
          clear.
          unfold flat.

          intros n u1 u2.
          rewrite !in_fsetU.
          now do 2 (let H := fresh in
                    intros H
                    ; apply (ssrbool.elimT ssrbool.orP) in H
                    ; destruct H
                    ; rewrite <- fset1E in H
                    ; rewrite in_fset1 in H
                    ; apply (ssrbool.elimT eqP) in H
                    ; inversion H ; subst).
        }
      }
      2,3,4: apply fsubsetxx || solve_in_fset.
      solve_Parable.
      1:{
        try (unfold idents).
        rewrite <- !fset1E.
        rewrite imfsetU.
        rewrite !imfset1.
        rewrite fdisjoint1s.
        rewrite in_fset.
        easy.
      }
    }

    Unshelve. 4: apply fset0.
    2: rewrite <- !fset0E ; rewrite !fset0U ; rewrite !fsetU0 ; apply fdisjoints0.
    2: rewrite <- !fset0E ; rewrite !fset0U ; rewrite !fsetU0 ; apply fdisjoints0.

    unfold trimmed in *.
    clear H1.
    set (trim _ (round2 _ _ true _)) in * ; rewrite H2 ; subst f ; clear H2.
    set (trim _ (round3 _ _ true _)) in * ; rewrite H3 ; subst f ; clear H3.
    set (trim _ (round2 _ _ false _)) in * ; rewrite H4 ; subst f ; clear H4.
    set (trim _ (round3 _ _ false _)) in * ; rewrite H5 ; subst f ; clear H5.

    {
      clear H.
      unfold eq_up_to_inv.

      (* simplify_eq_rel inp. *) (* TODO: Does not work? *)
      intros.
      unfold get_op_default.

      rewrite in_fset in H.
      rewrite <- !fset1E in H.
      simpl in H.

      apply (ssrbool.elimT ssrbool.orP) in H ; simpl in H.
      destruct H.
      {
        apply (ssrbool.elimT eqP) in H.
        inversion H ; subst.
        clear H.
        
        simpl.

        choice_type_eqP_handle.
        choice_type_eqP_handle.

        destruct x as [[w r] d].
        unfold cast_fun.
        simpl.

        unfold eq_rect_r.
        simpl.
        fold chElement.

        (* DDH assumption *)
        unfold commit_to_vote at 1 2.

        rewrite <- bind_ret at 1.
        rewrite <- bind_ret.

        rewrite !bind_assoc ;rewrite !bind_rewrite ; fold chElement.
        rewrite !bind_assoc ;rewrite !bind_rewrite ; fold chElement.
        rewrite !bind_assoc.

        do 2 replace (f_cvp_i _) with (ret_both (i : int32)) by now apply both_eq.
        do 2 replace (f_cvp_xi _) with (ret_both (xi)) by now apply both_eq.

        replace (f_cvp_vote _) with (ret_both (true : 'bool)) by now apply both_eq.
        replace (f_cvp_vote _) with (ret_both (false : 'bool)) by now apply both_eq.

        ssprove_same_head x0. (* f_accept *)
        rewrite !bind_assoc.

        apply somewhat_substitution.
        apply somewhat_substitutionR.
        rewrite !bind_rewrite.
        rewrite !bind_assoc.
        apply somewhat_substitution.
        apply somewhat_substitutionR.
        rewrite !bind_rewrite.
        rewrite !bind_assoc.
        apply somewhat_substitution.
        apply somewhat_substitutionR.
        rewrite !bind_rewrite.
        rewrite !bind_assoc.
        apply somewhat_substitution.
        apply somewhat_substitutionR.
        rewrite !bind_rewrite.
        rewrite !bind_assoc.
        apply somewhat_substitution.
        apply somewhat_substitutionR.
        rewrite !bind_rewrite.
        rewrite !bind_assoc.
        rewrite !bind_rewrite.
        rewrite !bind_assoc.

        (* bind commit_to *)
        set (pre := fun _ => _).
        eapply r_bind with (mid := pre_to_post pre).
        {
          unfold commit_to at 1 2.
          admit. (* DDH assumption / commit hiding *)
        }
        intros.
        apply rpre_hypothesis_rule
        ; intros ? ? []
        ; apply rpre_weaken_rule with (pre := pre) ; [ | now intros ? ? [] ; subst ]
        ; subst ; clear H1 ; subst pre.

        simpl.
        ssprove_refl.
      }
      {
        apply (ssrbool.elimT ssrbool.orP) in H ; simpl in H.
        destruct H ; [ | easy].
        apply (ssrbool.elimT eqP) in H.
        inversion H ; subst.
        clear H.

        simpl.

        choice_type_eqP_handle.
        choice_type_eqP_handle.

        destruct x as [[w r] d].

        
        unfold cast_fun.
        simpl.

        unfold eq_rect_r.
        simpl.
        fold chElement.

        simpl.

        ssprove_code_simpl.
        
        setoid_rewrite bind_assoc.
        ssprove_code_simpl.
        ssprove_code_simpl_more.
        setoid_rewrite (code_link_scheme _ _ (is_state _)).
        2, 3: ssprove_valid_code.

        do 2 replace (f_cvp_i _) with (ret_both (i : int32)) by now apply both_eq.
        do 2 replace (f_cvp_xi _) with (ret_both xi) by now apply both_eq.

        replace (f_cvp_vote _) with (ret_both (true : 'bool)) by now apply both_eq.
        replace (f_cvp_vote _) with (ret_both (false : 'bool)) by now apply both_eq.

        ssprove_same_head g_pow_yi.

        apply (r_uniform_bij) with (f := fun x => x) ; [ now apply inv_bij | intros a ].
        unfold cast_fun.
        simpl.

        unfold eq_rect_r.
        simpl.
        fold chElement.

        unfold assertD.
        rewrite !otf_fto.
        
        replace (OR_ZKP.proof_args.MyParam.R _ _) with true.
        2:{
          symmetry.
          unfold OR_ZKP.proof_args.MyParam.R.
          rewrite !eqxx.
          

        replace (OR_ZKP.proof_args.MyParam.R _ _) with true by admit.

        simpl.
        apply (r_uniform_bij) with (f := fun x => x) ; [ now apply inv_bij | intros w0 ].
        apply (r_uniform_bij) with (f := fun x => x) ; [ now apply inv_bij | intros r0 ].
        apply (r_uniform_bij) with (f := fun x => x) ; [ now apply inv_bij | intros d0 ].

        ssprove_same_head x0.
        simpl.
        ssprove_code_simpl.
        ssprove_code_simpl_more.
        setoid_rewrite (code_link_scheme _ _ _).
        2, 3, 4, 5: ssprove_valid_code.

        set (pre := fun _ => _).
        eapply r_bind with (mid := pre_to_post pre).
        {

          rewrite <- bind_ret at 1.
          rewrite <- bind_ret.

          set (lift_both (f_prod _ _)).
          set (lift_both (f_prod _ _)).

          apply (somewhat_let_substitution  _ _ b _ pre).
          Misc.pattern_lhs_approx.
          set (let_both _ _ ).
          pattern b0 in b1.
          set (fun _ => _) in b1.
          refine (somewhat_let_substitutionR  _ H b0 y pre _).
          subst H b1 y b b0 ; hnf in *.

          eapply r_bind with (mid := pre_to_post pre).
          {
            (* DDH assumption, g^xi yi + vi hides xi and vi, for known g^yi *)
            admit.
          }
          intros.
          apply rpre_hypothesis_rule
          ; intros ? ? []
          ; apply rpre_weaken_rule with (pre := pre) ; [ | now intros ? ? [] ; subst ]
          ; subst ; clear H1 ; subst pre.

          ssprove_refl.
        }
        intros.
        apply rpre_hypothesis_rule
        ; intros ? ? []
        ; apply rpre_weaken_rule with (pre := pre) ; [ | now intros ? ? [] ; subst ]
        ; subst ; clear H1 ; subst pre.

        ssprove_refl.
      }
    }
  Qed.
  
End OVN_proof.
