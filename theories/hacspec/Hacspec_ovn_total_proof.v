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

(* From Hammer Require Import Reflect. *)
(* From Hammer Require Import Hammer. *)
(* Hammer_version. *)
(* Hammer_objects. *)

(* (* Set Hammer Z3. *) *)
(* (* Unset Hammer Parallel. *) *)
(* (* (* (* disable the preliminary sauto tactic *) *) *) *)
(* (* (* Set Hammer SAutoLimit 0. *) *) *)
(* (* Set Hammer GSMode 1. *) *)
(* (* Set Hammer ATPLimit 30. *) *)
(* (* Hammer_cleanup. *) *)

(* Require Import SMTCoq.SMTCoq. *)
(* (* Set SMT Solver "z3". (** Use Z3, also "CVC4" **) *) *)

(* From mathcomp Require Import ring. *)

From OVN Require Import Hacspec_ovn.
From OVN Require Import Hacspec_helpers.
From OVN Require Import Hacspec_ovn_group_and_field.
From OVN Require Import Hacspec_ovn_sigma_setup.
From OVN Require Import Hacspec_ovn_schnorr.
From OVN Require Import Hacspec_ovn_or.

Module OVN_proof (HGPA : HacspecGroupParamAxiom).
  Module Schnorr_ZKP := OVN_schnorr_proof HGPA.
  Module OR_ZKP := OVN_or_proof HGPA.

  Import Schnorr_ZKP.
  Import OR_ZKP.

  Include HGPA.

  (* begin details : helper defintions *)
  Definition somewhat_let_substitution :
               forall {A C : choice_type} {B : choiceType} (f : C -> raw_code B) (c : raw_code B) (y : both A) (r : both A -> both C),
                 (forall x, deterministic (f x)) ->
          ⊢ ⦃ λ '(s₀, s₁), s₀ = s₁ ⦄ b_temp ← is_state y ;; temp ← is_state (r (ret_both b_temp)) ;; f temp ≈ c ⦃ λ '(b₀, s₀) '(b₁, s₁), b₀ = b₁ ∧ s₀ = s₁ ⦄ ->
          ⊢ ⦃ λ '(s₀, s₁), s₀ = s₁ ⦄ temp ← is_state (letb 'b := y in r b) ;; f temp ≈ c ⦃ λ '(b₀, s₀) '(b₁, s₁), b₀ = b₁ ∧ s₀ = s₁ ⦄.
  Proof.
    intros.
  Admitted.
  (* end details : helper defintions *)

  Notation " 'chState' " :=
    t_OvnContractState
    (in custom pack_type at level 2).

  Notation " 'chCastVoteCtx' " :=
    t_CastVoteParam
    (in custom pack_type at level 2).

  Notation " 'chInp' " :=
    (t_OvnContractState × (int32 × f_Z × 'bool))
    (in custom pack_type at level 2).

  Notation " 'chOut' " :=
    (chOption (t_OvnContractState))
    (in custom pack_type at level 2).

  Notation " 'chAuxInp' " :=
    (OR_ZKP.MyAlg.choiceStatement × OR_ZKP.MyAlg.choiceWitness)
    (in custom pack_type at level 2).

  Notation " 'chAuxOut' " :=
    (OR_ZKP.MyAlg.choiceTranscript)
    (in custom pack_type at level 2).

  (* × t_CastVoteParam = (int32 × v_Z × v_Z × v_Z × v_Z × 'bool) *)

  Definition MAXIMUM_BALLOT_SECRECY_SETUP : nat := 10.
  Definition MAXIMUM_BALLOT_SECRECY_RETURN : nat := 11.
  Definition MAXIMUM_BALLOT_SECRECY : nat := 12.

  Program Definition maximum_ballot_secrecy_real_setup :
    package (fset [])
      [interface]
      [interface
         #val #[ MAXIMUM_BALLOT_SECRECY_SETUP ] : chInp → chAuxInp
      ] :=
    [package
      #def #[ MAXIMUM_BALLOT_SECRECY_SETUP ] ('(state_inp, (cvp_i, cvp_xi, cvp_vote)) : chInp) : chAuxInp
      {
        let state := ret_both (state_inp : t_OvnContractState) in

        (* before zkp_vi *)
        g_pow_yi ← is_state (compute_g_pow_yi (cast_int (WS2 := _) (ret_both cvp_i)) (f_g_pow_xis state)) ;;

        (* zkp_vi *)
        (* (f_cvp_zkp_random_w params) (f_cvp_zkp_random_r params) (f_cvp_zkp_random_d params) g_pow_yi (f_cvp_xi params) (f_cvp_vote params) *)
        let cStmt : OR_ZKP.MyAlg.choiceStatement := fto ((is_pure (f_g_pow (ret_both cvp_xi)) , g_pow_yi : gT , g_pow_yi : gT) : OR_ZKP.MyParam.Statement) in (* x, h , y *)
        let cWitn : OR_ZKP.MyAlg.choiceWitness := fto ((FieldToWitness (is_pure (ret_both cvp_xi)) : 'Z_q, is_pure (ret_both (cvp_vote : 'bool)), g_pow_yi) : OR_ZKP.MyParam.Witness) in (* xi, vi, h *)
        ret (cStmt, cWitn)
    }].
  Next Obligation.
    eapply (valid_package_cons _ _ _ _ _ _ [] []).
    - apply valid_empty_package.
    - intros [].
      simpl.
      ssprove_valid'_2.
      all: repeat (apply valid_sampler ; intros).
      all: ssprove_valid'_2.
      all: try (apply (valid_injectMap (I1 := fset0)) ; [ apply fsub0set | rewrite <- fset0E ]).
      all: try apply (ChoiceEquality.is_valid_code (both_prog_valid _)).
      all: repeat (apply valid_sampler ; intros).
      all: repeat (rewrite !otf_fto ; ssprove_valid'_2).
    - unfold "\notin".
      rewrite <- !fset0E.
      rewrite imfset0.
      rewrite in_fset0.
      easy.
  Qed.
  Fail Next Obligation.

  Notation " 'chMidInp' " :=
    (t_OvnContractState × (int32 × f_Z × 'bool) × OR_ZKP.MyAlg.choiceTranscript)
    (in custom pack_type at level 2).
  
  Program Definition maximum_ballot_secrecy_real_return :
    package (fset [])
      [interface]
      [interface
         #val #[ MAXIMUM_BALLOT_SECRECY_RETURN ] : chMidInp → chOut
      ] :=
    [package
       #def #[ MAXIMUM_BALLOT_SECRECY_RETURN ] ('(state_inp, (cvp_i, cvp_xi, cvp_vote), transcript) : chMidInp) : chOut
       {
         let state := ret_both (state_inp : t_OvnContractState) in

         (* before zkp_vi *)
         g_pow_yi ← is_state (compute_g_pow_yi (cast_int (WS2 := _) (ret_both cvp_i)) (f_g_pow_xis state)) ;;
        let g_pow_yi := ret_both g_pow_yi in

        let zkp_vi := ret_both (OR_ZKP.or_sigma_ret_to_hacspec_ret transcript) in

        (* after zkp_vi *)
        temp ← is_state (
            letb g_pow_xi_yi_vi := compute_group_element_for_vote (ret_both cvp_xi) (ret_both (cvp_vote : 'bool)) g_pow_yi in
            letb cast_vote_state_ret := f_clone state in
            letb cast_vote_state_ret := Build_t_OvnContractState[cast_vote_state_ret] (f_g_pow_xi_yi_vis := update_at_usize (f_g_pow_xi_yi_vis cast_vote_state_ret) (cast_int (WS2 := _) (ret_both cvp_i)) g_pow_xi_yi_vi) in
            letb cast_vote_state_ret := Build_t_OvnContractState[cast_vote_state_ret] (f_zkp_vis := update_at_usize (f_zkp_vis cast_vote_state_ret) (cast_int (WS2 := _) (ret_both cvp_i)) zkp_vi) in
            (prod_b (f_accept,cast_vote_state_ret))) ;;
        ret (Some temp.2)
       }].
  Next Obligation.
    eapply (valid_package_cons _ _ _ _ _ _ [] []).
    - apply valid_empty_package.
    - intros [].
      simpl.
      ssprove_valid'_2.
      all: repeat (apply valid_sampler ; intros).
      all: ssprove_valid'_2.
      all: try (apply (valid_injectMap (I1 := fset0)) ; [ apply fsub0set | rewrite <- fset0E ]).
      all: try apply (ChoiceEquality.is_valid_code (both_prog_valid _)).
      all: repeat (apply valid_sampler ; intros).
      all: repeat (rewrite !otf_fto ; ssprove_valid'_2).
      all: now rewrite in_fset ; repeat (rewrite in_cons ; simpl) ; rewrite eqxx.
    - unfold "\notin".
      rewrite <- !fset0E.
      rewrite imfset0.
      rewrite in_fset0.
      easy.
  Qed.
  Fail Next Obligation.

  Program Definition maximum_ballot_secrecy :
    package (fset [])
      [interface
         #val #[ Sigma.RUN ] : chAuxInp → chAuxOut ;
         #val #[ MAXIMUM_BALLOT_SECRECY_RETURN ] : chMidInp → chOut ;
         #val #[ MAXIMUM_BALLOT_SECRECY_SETUP ] : chInp → chAuxInp
      ]
      [interface
         #val #[ MAXIMUM_BALLOT_SECRECY ] : chInp → chOut
      ] :=
    [package
      #def #[ MAXIMUM_BALLOT_SECRECY ] ('(state_inp, (cvp_i, cvp_xi, cvp_vote)) : chInp) : chOut
      {
        #import {sig #[ MAXIMUM_BALLOT_SECRECY_SETUP ] : chInp → chAuxInp } as SETUP ;;
        #import {sig #[ Sigma.RUN ] : chAuxInp → chAuxOut } as RUN ;;
        #import {sig #[ MAXIMUM_BALLOT_SECRECY_RETURN ] : chMidInp → chOut } as OUTPUT ;;

        '(cStmt, cWitn) ← SETUP (state_inp, (cvp_i, cvp_xi, cvp_vote)) ;;
        transcript ← RUN (cStmt, cWitn) ;;
        res ← OUTPUT (state_inp, (cvp_i, cvp_xi, cvp_vote), transcript) ;;
        ret res
      }
    ].
  Next Obligation.
    eapply (valid_package_cons _ _ _ _ _ _ [] []).
    - apply valid_empty_package.
    - intros [].
      simpl.
      ssprove_valid'_2.
      all: repeat (apply valid_sampler ; intros).
      all: ssprove_valid'_2.
      all: try (apply (valid_injectMap (I1 := fset0)) ; [ apply fsub0set | rewrite <- fset0E ]).
      all: try apply (ChoiceEquality.is_valid_code (both_prog_valid _)).
      all: repeat (apply valid_sampler ; intros).
      all: repeat (rewrite !otf_fto ; ssprove_valid'_2).
      all: now rewrite in_fset ; repeat (rewrite in_cons ; simpl) ; rewrite eqxx.
    - unfold "\notin".
      rewrite <- !fset0E.
      rewrite imfset0.
      rewrite in_fset0.
      easy.
  Qed.
  Fail Next Obligation.

  Notation " 'chAuxSimInp' " :=
    (OR_ZKP.MyAlg.choiceStatement × OR_ZKP.MyAlg.choiceChallenge)
    (in custom pack_type at level 2).

  Notation " 'chAuxSimOut' " :=
    (OR_ZKP.MyAlg.choiceTranscript)
      (in custom pack_type at level 2).

  Program Definition maximum_ballot_secrecy_ideal_setup:
    package (fset [])
      [interface]
      [interface #val #[ MAXIMUM_BALLOT_SECRECY_SETUP ] : chInp → chAuxInp] :=
    [package
      #def #[ MAXIMUM_BALLOT_SECRECY_SETUP ] ('(state, (cvp_i, cvp_xi, cvp_vote)) : chInp) : chAuxInp
      {
        let state := ret_both (state : t_OvnContractState) in
        let p_i := ret_both cvp_i : both int32 in

        yi ← sample (uniform #|'Z_q|) ;;
        (* c ← sample (uniform #|'Z_q|) ;; *)

        h ← is_state (compute_g_pow_yi (cast_int (WS2 := _) p_i) (f_g_pow_xis state)) ;;

        let y := g ^+ (otf yi * FieldToWitness cvp_xi + (if cvp_vote then 1 else 0))%R in

        ret (fto (is_pure (f_g_pow (ret_both cvp_xi)) : gT, h : gT, y), fto ( FieldToWitness cvp_xi, cvp_vote, h : gT ))
        (* ret (fto (x : gT, h : gT, y), c) *)
      }].
  Next Obligation.
    eapply (valid_package_cons _ _ _ _ _ _ [] []).
    - apply valid_empty_package.
    - intros [].
      simpl.
      destruct s0 as [[? ?] ?].
      ssprove_valid'_2.
      all: repeat (apply valid_sampler ; intros).
      all: ssprove_valid'_2.
      all: try destruct (otf s8), s12, (otf s11), s15 as [[? ?] ?], (otf s9), s19 as [[? ?] ?]. 
      all: try (apply (valid_injectMap (I1 := fset0)) ; [ apply fsub0set | rewrite <- fset0E ]).
      all: try apply (ChoiceEquality.is_valid_code (both_prog_valid _)).
      all: repeat (apply valid_sampler ; intros).
      all: repeat (rewrite !otf_fto ; ssprove_valid'_2).
      all: ssprove_valid'_2.
      (* 1,2: now rewrite in_fset in_cons eqxx. *)
    - unfold "\notin". 
      rewrite <- !fset0E.
      rewrite imfset0.
      rewrite in_fset0.
      easy.
  Qed.
  Fail Next Obligation.

  Program Definition maximum_ballot_secrecy_ideal_return :
    package (fset [])
      [interface]
      [interface
         #val #[ MAXIMUM_BALLOT_SECRECY_RETURN ] : chMidInp → chOut
      ] :=
    [package
       #def #[ MAXIMUM_BALLOT_SECRECY_RETURN ] ('(state, (cvp_i, cvp_xi, cvp_vote), transcript) : chMidInp) : chOut
      {
        let state := ret_both (state : t_OvnContractState) in

        let p_i := ret_both cvp_i : both int32 in
        let '(zkp_xhy, zkp_abab, zkp_c, zkp_rdrd) := transcript in
        let '(x,h,y) := otf zkp_xhy in
        let '(zkp_a1, zkp_b1, zkp_a2, zkp_b2) := otf zkp_abab in
        let '(zkp_r1, zkp_d1, zkp_r2, zkp_d2) := otf zkp_rdrd in

        let zkp_c := WitnessToField (otf zkp_c : 'Z_q) : f_Z in

        let zkp_r1 := WitnessToField (zkp_r1 : 'Z_q) : f_Z in
        let zkp_d1 := WitnessToField (zkp_d1 : 'Z_q) : f_Z in
        let zkp_r2 := WitnessToField (zkp_r2 : 'Z_q) : f_Z in
        let zkp_d2 := WitnessToField (zkp_d2 : 'Z_q) : f_Z in

        res ← is_state (
            letb zkp_vi :=
              Build_t_OrZKPCommit
                (f_or_zkp_x := ret_both x)
                (f_or_zkp_y := ret_both y)
                (f_or_zkp_a1 := ret_both zkp_a1)
                (f_or_zkp_b1 := ret_both zkp_b1)
                (f_or_zkp_a2 := ret_both zkp_a2)
                (f_or_zkp_b2 := ret_both zkp_b2)
                (f_or_zkp_c := ret_both zkp_c)
                (f_or_zkp_d1 := ret_both zkp_d1)
                (f_or_zkp_d2 := ret_both zkp_d2)
                (f_or_zkp_r1 := ret_both zkp_r1)
                (f_or_zkp_r2 := ret_both zkp_r2)
              in
            letb g_pow_xi_yi_vi_list := update_at_usize (f_g_pow_xi_yi_vis state) (cast_int (WS2 := U32) (p_i)) (ret_both y) in
            letb state := (Build_t_OvnContractState[state] (f_g_pow_xi_yi_vis := g_pow_xi_yi_vi_list)) in
            letb zkp_vi_list := update_at_usize (f_zkp_vis state) (cast_int (WS2 := U32) (p_i)) (zkp_vi) in
            letb state := (Build_t_OvnContractState[state] (f_zkp_vis := zkp_vi_list))
        in
        state) ;;
                          (* params.cvp_i as usize *)
          (* g_pow_xi_yi_vis *)
            (* zkp_vis *)
        ret (Some res)
    }].
    Next Obligation.
    eapply (valid_package_cons _ _ _ _ _ _ [] []).
    - apply valid_empty_package.
    - intros [].
      simpl.
      ssprove_valid'_2.
      all: repeat (apply valid_sampler ; intros).
      all: ssprove_valid'_2.
      all: try destruct (otf s0), s13, (otf s6), s16 as [[? ?] ?], (otf s1), s20 as [[? ?] ?]. 
      all: try (apply (valid_injectMap (I1 := fset0)) ; [ apply fsub0set | rewrite <- fset0E ]).
      all: try apply (ChoiceEquality.is_valid_code (both_prog_valid _)).
      all: repeat (apply valid_sampler ; intros).
      all: repeat (rewrite !otf_fto ; ssprove_valid'_2).
      all: ssprove_valid'_2.
      (* all: now rewrite in_fset ; repeat (rewrite in_cons ; simpl) ; rewrite eqxx. *)
    - unfold "\notin".
      rewrite <- !fset0E.
      rewrite imfset0.
      rewrite in_fset0.
      easy.
  Qed.
  Fail Next Obligation.

  Program Definition maximum_ballot_secrecy_real_par0 : package
      (MyAlg.Sigma_locs)
      [interface]
      [interface
         #val #[Sigma.RUN] : chAuxInp → chAuxSimOut ;
         #val #[MAXIMUM_BALLOT_SECRECY_RETURN] : chMidInp → chOut
      ] :=
    mkpackage (par hacspec_or_run maximum_ballot_secrecy_real_return) _.
  Next Obligation.
    eapply valid_package_inject_export.
    2:{
      pose (valid_par _ _ _ _ _ _ _ _ _ (pack_valid hacspec_or_run) (pack_valid maximum_ballot_secrecy_real_return) ).
      (* *)
      rewrite <- fset0E in v.
      rewrite fsetU0 in v.
      rewrite <- fset0E in v.
      rewrite fset0U in v.
      rewrite fset0E in v.

      apply v.
    }

    rewrite <- !fset_cat.
    apply fsubsetxx.
  Qed.

  Lemma maximum_ballot_secrecy_real_parable : Parable maximum_ballot_secrecy_real_par0 maximum_ballot_secrecy_real_setup.
  Proof.
    unfold Parable.
    rewrite !domm_set ; unfold ".1".
    rewrite domm0.
    rewrite !fsetU0.
    rewrite fdisjointUl.
    rewrite !fdisjoint1s.
    easy.
  Qed.

  Program Definition maximum_ballot_secrecy_real :
    package
      (MyAlg.Sigma_locs)
      [interface #val #[Sigma.RUN] : chAuxInp → chAuxSimOut ]
      [interface #val #[MAXIMUM_BALLOT_SECRECY] : chInp → chOut ]
    :=
    mkpackage (maximum_ballot_secrecy ∘ (par (par hacspec_or_run maximum_ballot_secrecy_real_return) maximum_ballot_secrecy_real_setup)) _.
  Next Obligation.
    rewrite <- fset0U. rewrite fset0E.
    eapply valid_link.
    1: apply maximum_ballot_secrecy.
    eapply (valid_par_upto
             _ _ _ _ _ _ _ _ _ _ _
             maximum_ballot_secrecy_real_parable
           ).
    1: apply maximum_ballot_secrecy_real_par0.
    1: apply maximum_ballot_secrecy_real_setup.
    1: rewrite <- !fset0E, fsetU0 ; apply fsubsetxx.
    1: rewrite <- !fset0E, fsetU0 ; apply fsub0set.
    1: rewrite <- !fset_cat ; apply fsubsetxx.
  Qed.
  Fail Next Obligation.
  
  
  Notation " 'SHVZK_chInput' " :=
    (chProd (chProd MyAlg.choiceStatement MyAlg.choiceWitness) MyAlg.choiceChallenge)
      (in custom pack_type at level 2).
  
  Notation " 'SHVZK_chTranscript' " :=
    (OR_ZKP.MyAlg.choiceTranscript)
      (in custom pack_type at level 2).

  Notation " 'SHVZK_chRelation' " :=
    (chProd MyAlg.choiceStatement MyAlg.choiceWitness)
      (in custom pack_type at level 2).

  Definition SHVZK_ideal_aux : package (fset [::]) [interface #val #[ Sigma.TRANSCRIPT ] : SHVZK_chInput → SHVZK_chTranscript ] [interface #val #[Sigma.RUN] : SHVZK_chRelation → SHVZK_chTranscript ]
    :=
    [package
        #def #[ Sigma.RUN ] (hw : SHVZK_chRelation) : SHVZK_chTranscript
        {
          #import {sig #[ Sigma.TRANSCRIPT ] : SHVZK_chInput → SHVZK_chTranscript } as SHVZK ;;
          e ← sample uniform #|MyParam.Challenge| ;;
          t ← SHVZK (hw, e) ;;
          ret t
        }
    ].
  
  Program Definition maximum_ballot_secrecy_ideal_par0 : package
      (MyAlg.Simulator_locs)
      [interface]
      [interface
         #val #[Sigma.RUN] : chAuxInp → chAuxSimOut ;
         #val #[MAXIMUM_BALLOT_SECRECY_RETURN] : chMidInp → chOut
      ] :=
    mkpackage (par (SHVZK_ideal_aux ∘ Sigma.SHVZK_ideal) maximum_ballot_secrecy_ideal_return) _.
  Next Obligation.
    eapply valid_package_inject_export.
    2:{
      epose (valid_par _ _ _ _ _ _ (SHVZK_ideal_aux ∘ Sigma.SHVZK_ideal) _ _ _ (pack_valid maximum_ballot_secrecy_ideal_return) ).
      (* *)
      rewrite <- fset0E in v.
      rewrite fsetU0 in v.
      rewrite <- fset0E in v.
      rewrite fset0U in v.
      rewrite fset0E in v.

      rewrite fsetUid in v.

      apply v.
    }

    rewrite <- !fset_cat.
    apply fsubsetxx.
  Qed.

  Lemma maximum_ballot_secrecy_ideal_parable : Parable maximum_ballot_secrecy_ideal_par0 maximum_ballot_secrecy_ideal_setup.
  Proof.
    unfold Parable.
    rewrite !domm_set ; unfold ".1".
    rewrite domm0.
    rewrite !fsetU0.
    rewrite fdisjointUl.
    rewrite !fdisjoint1s.
    easy.
  Qed.

  Program Definition maximum_ballot_secrecy_ideal :
    package
      (MyAlg.Simulator_locs)
      [interface #val #[Sigma.RUN] : chAuxInp → chAuxSimOut ]
      [interface #val #[MAXIMUM_BALLOT_SECRECY] : chInp → chOut ] :=
    mkpackage (maximum_ballot_secrecy ∘ par (par (SHVZK_ideal_aux ∘ Sigma.SHVZK_ideal) maximum_ballot_secrecy_ideal_return) maximum_ballot_secrecy_ideal_setup) _.
  Next Obligation.
    rewrite <- fset0U. rewrite fset0E.
    eapply valid_link.
    1: apply maximum_ballot_secrecy.
    eapply (valid_par_upto
             _ _ _ _ _ _ _ _ _ _ _
             maximum_ballot_secrecy_ideal_parable
           ).
    1: apply maximum_ballot_secrecy_ideal_par0.
    1: apply maximum_ballot_secrecy_ideal_setup.
    1: rewrite <- !fset0E, fsetU0 ; apply fsubsetxx.
    1: rewrite <- !fset0E, fsetU0 ; apply fsub0set.
    1: rewrite <- !fset_cat ; apply fsubsetxx.
  Qed.
  Fail Next Obligation.

  Definition ɛ_maximum_ballot_secrecy A :=
    AdvantageE
      (maximum_ballot_secrecy_real)
      (maximum_ballot_secrecy_ideal)
      A.

  Lemma maximum_ballot_secrecy_setup_success:
    maximum_ballot_secrecy_real_setup ≈₀ maximum_ballot_secrecy_ideal_setup.
  Proof.
    intros.
    unfold ɛ_maximum_ballot_secrecy.
    unfold maximum_ballot_secrecy_real.
    unfold maximum_ballot_secrecy_ideal.
    apply: eq_rel_perf_ind_eq.
    all: ssprove_valid.
    1:{
      unfold eq_up_to_inv.
      intros.
      unfold get_op_default.

      Opaque MyAlg.Simulate.

      simpl (lookup_op _ _) ; fold chElement.

      rewrite !setmE.
      rewrite <- fset1E in H.
      rewrite in_fset1 in H.
      apply (ssrbool.elimT eqP) in H.
      inversion H ; subst.

      rewrite eqxx.
      simpl.

      destruct choice_type_eqP ; [ | now apply r_ret ].
      destruct choice_type_eqP ; [ | now apply r_ret ].
      subst.
      rewrite !cast_fun_K.
      clear e e0.

      destruct x as [state [[cvp_i cvp_xi] cvp_vote]].
      apply r_const_sample_R ; [ admit | intros ].

      eapply r_bind ; [ apply rreflexivity_rule | intros ].
      apply r_ret.
      intros. inversion H0 ; subst ; clear H0.
      split ; [ | reflexivity ].
      f_equal.
      f_equal.
      f_equal.
      admit.
  Admitted.

  Lemma maximum_ballot_secrecy_return_success:
    maximum_ballot_secrecy_real_return ≈₀ maximum_ballot_secrecy_ideal_return.
  Proof.
    intros.
    unfold ɛ_maximum_ballot_secrecy.
    unfold maximum_ballot_secrecy_real.
    unfold maximum_ballot_secrecy_ideal.
    apply: eq_rel_perf_ind_eq.
    all: ssprove_valid.
    1:{
      unfold eq_up_to_inv.
      intros.
      unfold get_op_default.

      Opaque MyAlg.Simulate.

      simpl (lookup_op _ _) ; fold chElement.

      rewrite !setmE.
      rewrite <- fset1E in H.
      rewrite in_fset1 in H.
      apply (ssrbool.elimT eqP) in H.
      inversion H ; subst.

      rewrite eqxx.
      simpl.

      destruct choice_type_eqP ; [ | now apply r_ret ].
      destruct choice_type_eqP ; [ | now apply r_ret ].
      subst.
      rewrite !cast_fun_K.
      clear e e0.

      destruct x as [[state [[cvp_i cvp_xi] cvp_vote]] transcript].
      destruct transcript as [[[zkp_xhy zkp_abab] zkp_c] zkp_rdrd].
      destruct (otf zkp_xhy) as [[x h] y].
      destruct (otf zkp_abab) as [[[zkp_a1 zkp_b1] zkp_a2] zkp_b2].
      destruct (otf zkp_rdrd) as [[[zkp_r1 zkp_d1] zkp_r2] zkp_d2].

      

      (* apply somewhat_substitution ; [ admit | admit | rewrite bind_rewrite ]. *)
      (* cbn. *)
      (* setoid_rewrite bind_ret. *)
      (* apply somewhat_substitution ; [ admit | admit | rewrite bind_rewrite ]. *)

      (* eapply somewhat_let_substitution. ; [admit | ]. *)
      
      (* apply r_const_sample_R ; [ admit | intros ]. *)

      (* eapply r_bind ; [ apply rreflexivity_rule | intros ]. *)
      (* apply r_ret. *)
      (* intros. inversion H0 ; subst ; clear H0. *)
      (* split ; [ | reflexivity ]. *)
      (* f_equal. *)
      (* f_equal. *)
      (* f_equal. *)
      (* admit. *)
  Admitted.


  Lemma swap_two_fset :
    (forall T a b, fset (T := T) [a;b] = fset [b;a]).
  Admitted.

  Lemma swap_three_fset :
    (forall T a b c, fset (T := T) [a;b;c] = fset [c;a;b]).
  Admitted.

  Lemma maximum_ballot_secrecy_success:
    ∀ LA A,
      ValidPackage LA [interface
                         #val #[ MAXIMUM_BALLOT_SECRECY ] : chInp → chOut
        ] A_export A →
      fdisjoint LA MyAlg.Sigma_locs →
      ɛ_maximum_ballot_secrecy A = 0%R.
  Proof.
    intros.

    unfold ɛ_maximum_ballot_secrecy.
    From Crypt Require Import SigmaProtocol.

    Set Printing Coercions.
    apply (AdvantageE_le_0 _ _ _ ).
    unfold maximum_ballot_secrecy_real, maximum_ballot_secrecy_ideal, pack.
    rewrite <- Advantage_link.

    (* Setup is equal *)
    eapply Order.le_trans ; [ apply Advantage_triangle with (R := (par (par OR_ZKP.hacspec_or_run maximum_ballot_secrecy_real_return) maximum_ballot_secrecy_ideal_setup)) | ].
    
    set (AdE := AdvantageE _ _) at 2.
    rewrite (Advantage_par maximum_ballot_secrecy_real_par0 maximum_ballot_secrecy_real_setup maximum_ballot_secrecy_ideal_setup).
    2: apply (flat_valid_package _ _ _ _ (pack_valid maximum_ballot_secrecy_real_setup)).
    2, 3, 4: repeat (apply trimmed_empty_package || apply trimmed_package_cons).
    subst AdE.

    erewrite maximum_ballot_secrecy_setup_success with (LA := (LA :|: fset [::]) :|: (MyAlg.Sigma_locs :|: fset [::])) ; [ rewrite add0r | .. ].
    3,4: rewrite <- fset0E ; rewrite fsetU0 ; apply fdisjoints0.
    2:{
      eapply valid_link.
      1:{
        eapply valid_link.
        1: apply H.
        apply maximum_ballot_secrecy.
      }

      eapply valid_par_upto.
      {
        unfold Parable.
        rewrite <- !fset1E.
        rewrite !domm_set ; unfold ".1".
        rewrite domm0.
        rewrite !fsetU0.
        rewrite fdisjointUl.
        rewrite !fdisjoint1s.
        reflexivity.
      }
      {
        apply maximum_ballot_secrecy_real_par0.
      }
      {
        apply valid_ID.
        apply (flat_valid_package _ _ _ _ (pack_valid maximum_ballot_secrecy_real_setup)).
      }
      {
        apply fsubsetxx.
      }
      {
        rewrite <- fset0E.
        rewrite fset0U.
        apply fsubsetxx.
      }
      {
        rewrite <- fset_cat.
        apply fsubsetxx.
      }
    }

    do 2 rewrite <- (par_commut maximum_ballot_secrecy_ideal_setup _ _).
    rewrite (Advantage_par maximum_ballot_secrecy_ideal_setup maximum_ballot_secrecy_real_par0 maximum_ballot_secrecy_ideal_par0).
    2: apply (flat_valid_package _ _ _ _ (pack_valid maximum_ballot_secrecy_real_par0)).
    2, 3, 4: repeat (apply trimmed_empty_package || apply trimmed_package_cons).

    unfold maximum_ballot_secrecy_real_par0, maximum_ballot_secrecy_ideal_par0, pack.


    (* Return is equal *)
    eapply Order.le_trans ; [ apply Advantage_triangle with (R := (par OR_ZKP.hacspec_or_run maximum_ballot_secrecy_ideal_return)) | ].

    set (AdE := AdvantageE _ _) at 2.
    rewrite (Advantage_par hacspec_or_run maximum_ballot_secrecy_real_return maximum_ballot_secrecy_ideal_return).
    2: apply (flat_valid_package _ _ _ _ (pack_valid maximum_ballot_secrecy_real_return)).
    2, 3, 4: repeat (apply trimmed_empty_package || apply trimmed_package_cons).
    subst AdE.

    erewrite maximum_ballot_secrecy_return_success with (LA := ((LA  :|: fset [::]) :|: fset [::]) :|: (MyAlg.Sigma_locs :|: fset [::])) ; [ rewrite add0r | .. ].
    3,4: rewrite <- fset0E ; rewrite fsetU0 ; apply fdisjoints0.
    2:{
      eapply valid_link.
      2:{
        eapply valid_par_upto.
        {
          unfold Parable.
          rewrite !domm_set ; unfold ".1".
          rewrite domm0.
          rewrite !fsetU0.
          rewrite domm_ID_fset.
          rewrite !fdisjoint1s.
          rewrite notin_fset.
          reflexivity.
        }
        {
          apply hacspec_or_run.
        }
        {
          apply valid_ID.
          apply (flat_valid_package _ _ _ _ (pack_valid maximum_ballot_secrecy_real_return)).
        }
        {
          apply fsubsetxx.
        }
        {
          rewrite <- fset0E.
          rewrite fset0U.
          apply fsubsetxx.
        }
        {
          rewrite <- fset_cat.
          simpl.
          apply fsubsetxx.
        }
      }
      1:{
        eapply valid_link.
        1:{
          eapply valid_link.
          1: apply H.
          apply maximum_ballot_secrecy.
        }

        eapply valid_par_upto.
        {
          unfold Parable.
          rewrite !domm_set ; unfold ".1".
          rewrite domm0.
          rewrite !fsetU0.
          rewrite domm_ID_fset.
          rewrite !fdisjoint1s.
          rewrite notin_fset.
          reflexivity.
        }
        {
          apply maximum_ballot_secrecy_ideal_setup.
        }
        {
          apply valid_ID.
          apply (flat_valid_package _ _ _ _ (pack_valid maximum_ballot_secrecy_real_par0)).
        }
        {
          rewrite <- fset0E.
          rewrite fset0U.
          apply fsubsetxx.
        }
        {
          rewrite <- fset0E.
          rewrite fset0U.
          apply fsubsetxx.
        }
        {
          rewrite <- fset_cat.
          simpl.
          
          rewrite swap_three_fset.
          apply fsubsetxx.
        }
      }
    }

    do 2 rewrite <- (par_commut maximum_ballot_secrecy_ideal_return _ _).
    rewrite (Advantage_par maximum_ballot_secrecy_ideal_return hacspec_or_run (pack Sigma.SHVZK_real_aux ∘ pack Sigma.SHVZK_ideal)).
    2: apply (flat_valid_package _ _ _ _ (pack_valid hacspec_or_run)).
    4: unfold trimmed ; rewrite <- link_trim_commut ; f_equal.
    2, 3, 4: repeat (apply trimmed_empty_package || apply trimmed_package_cons).

    (* OR zkp is equal *)
    eapply Order.le_trans ; [
        eapply (Advantage_triangle_chain (hacspec_or_run)
                 [
                   (pack Sigma.RUN_interactive);
                   ((Sigma.SHVZK_real_aux ∘ Sigma.SHVZK_real))
                 ]
                (SHVZK_ideal_aux ∘ Sigma.SHVZK_ideal) _)
        | unfold advantage_sum ].

    erewrite (hacspec_vs_RUN_interactive) with (LA := ((LA  :|: fset [::]) :|: fset [::]) :|: (fset [::] :|: fset [::])) ; [ rewrite add0r | .. ].
    3: rewrite <- !fset0E ; rewrite !fsetU0 ; apply H0.
    2:{
      eapply valid_link.
      2:{
        eapply valid_par_upto.
        {
          unfold Parable.
          rewrite !domm_set ; unfold ".1".
          rewrite domm0.
          rewrite !fsetU0.
          rewrite domm_ID_fset.
          rewrite !fdisjoint1s.
          rewrite notin_fset.
          reflexivity.
        }
        {
          apply maximum_ballot_secrecy_ideal_return.
        }
        {
          apply valid_ID.
          apply (flat_valid_package _ _ _ _ (pack_valid hacspec_or_run)).
        }
        {
          apply fsubsetxx.
        }
        {
          rewrite <- fset0E.
          rewrite fset0U.
          apply fsubsetxx.
        }
        {
          rewrite <- fset_cat.
          simpl.
          apply fsubsetxx.
        }
      }
      1:{
        eapply valid_link.
        1:{
          eapply valid_link.
          1: apply H.
          apply maximum_ballot_secrecy.
        }

        eapply valid_par_upto.
        {
          unfold Parable.
          rewrite !domm_set ; unfold ".1".
          rewrite domm0.
          rewrite !fsetU0.
          rewrite domm_ID_fset.
          rewrite !fdisjoint1s.
          rewrite notin_fset.
          reflexivity.
        }
        {
          apply maximum_ballot_secrecy_ideal_setup.
        }
        {
          apply valid_ID.
          apply (flat_valid_package _ _ _ _ (pack_valid maximum_ballot_secrecy_real_par0)).
        }
        {
          rewrite <- fset0E.
          rewrite fset0U.
          apply fsubsetxx.
        }
        {
          rewrite <- fset_cat.
          simpl.

          rewrite swap_two_fset.
          apply fsubsetxx.
        }
        {
          rewrite <- fset_cat.
          simpl.

          rewrite swap_three_fset.
          apply fsubsetxx.
        }
      }
    }

    erewrite (Sigma.run_interactive_shvzk MyAlg.Simulator_locs (fun x => {code r ← sample uniform #|MyParam.Challenge| ;; MyAlg.Simulate x r })) with (LA := ((LA  :|: fset [::]) :|: fset [::]) :|: (fset [::] :|: fset [::])) ; [ rewrite add0r | .. ].
    3: rewrite <- !fset0E ; rewrite !fsetU0 ; apply H0.
    2:{
      eapply valid_link.
      2:{
        eapply valid_par_upto.
        {
          unfold Parable.
          rewrite !domm_set ; unfold ".1".
          rewrite domm0.
          rewrite !fsetU0.
          rewrite domm_ID_fset.
          rewrite !fdisjoint1s.
          rewrite notin_fset.
          reflexivity.
        }
        {
          apply maximum_ballot_secrecy_ideal_return.
        }
        {
          apply valid_ID.
          apply (flat_valid_package _ _ _ _ (pack_valid hacspec_or_run)).
        }
        {
          apply fsubsetxx.
        }
        {
          rewrite <- fset0E.
          rewrite fset0U.
          apply fsubsetxx.
        }
        {
          rewrite <- fset_cat.
          simpl.
          apply fsubsetxx.
        }
      }
      1:{
        eapply valid_link.
        1:{
          eapply valid_link.
          1: apply H.
          apply maximum_ballot_secrecy.
        }

        eapply valid_par_upto.
        {
          unfold Parable.
          rewrite !domm_set ; unfold ".1".
          rewrite domm0.
          rewrite !fsetU0.
          rewrite domm_ID_fset.
          rewrite !fdisjoint1s.
          rewrite notin_fset.
          reflexivity.
        }
        {
          apply maximum_ballot_secrecy_ideal_setup.
        }
        {
          apply valid_ID.
          apply (flat_valid_package _ _ _ _ (pack_valid maximum_ballot_secrecy_real_par0)).
        }
        {
          rewrite <- fset0E.
          rewrite fset0U.
          apply fsubsetxx.
        }
        {
          rewrite <- fset_cat.
          simpl.
          rewrite swap_two_fset.
          apply fsubsetxx.
        }
        {
          rewrite <- fset_cat.
          simpl.
          rewrite swap_three_fset.
          apply fsubsetxx.
        }
      }
    }

    rewrite <- Advantage_link.

    erewrite OR_ZKP.shvzk_success with (LA := ((((LA  :|: fset [::])  :|: fset [::])  :|: fset [::]) :|: fset [::] (* Problem here, MyAlg.Sigma_locs not allowed in adversary locations! *))) ; [ | .. ].
    3: rewrite <- !fset0E ; rewrite !fsetU0.
    3: apply H0.
    2:{
      eapply valid_link.
      1:{
        eapply valid_link.
        1:{
          eapply valid_link.
          1:{
            eapply valid_link.
            1: apply H.
            apply maximum_ballot_secrecy.
          }

          eapply valid_par_upto.
          {
            unfold Parable.
            rewrite !domm_set ; unfold ".1".
            rewrite domm0.
            rewrite !fsetU0.
            rewrite domm_ID_fset.
            rewrite !fdisjoint1s.
            rewrite notin_fset.
            reflexivity.
          }
          {
            apply maximum_ballot_secrecy_ideal_setup.
          }
          {
            apply valid_ID.
            apply (flat_valid_package _ _ _ _ (pack_valid maximum_ballot_secrecy_ideal_par0)).
          }
          {
            rewrite <- fset0E.
            rewrite fset0U.
            apply fsubsetxx.
          }
          {
            rewrite <- fset_cat.
            simpl.
            apply fsubsetxx.
          }
          {
            rewrite <- fset_cat.
            simpl.
            rewrite swap_three_fset.
            apply fsubsetxx.
          }
        }
        eapply valid_par_upto.
        {
          unfold Parable.
          rewrite !domm_set ; unfold ".1".
          rewrite domm0.
          rewrite !fsetU0.
          rewrite domm_ID_fset.
          rewrite !fdisjoint1s.
          rewrite notin_fset.
          reflexivity.
        }
        {
          apply maximum_ballot_secrecy_ideal_return.
        }
        {
          apply valid_ID.
          apply (flat_valid_package _ _ _ _ (pack_valid hacspec_or_run)).
        }
        {
          rewrite <- fset0E.
          rewrite fset0U.
          apply fsubsetxx.
        }
        {
          rewrite <- fset_cat.
          simpl.
          apply fsubsetxx.
        }
        {
          rewrite <- fset_cat.
          simpl.
          rewrite swap_two_fset.
          apply fsubsetxx.
        }
      }

      apply SHVZK_ideal_aux.
    }
    easy.
  Qed.

End OVN_proof.
