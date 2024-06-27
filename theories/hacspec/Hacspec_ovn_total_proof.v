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

From mathcomp Require Import ring.

From OVN Require Import Hacspec_ovn.
From OVN Require Import Hacspec_helpers.
From OVN Require Import Hacspec_ovn_group_and_field.
From OVN Require Import Hacspec_ovn_sigma_setup.
From OVN Require Import Hacspec_ovn_schnorr.
From OVN Require Import Hacspec_ovn_or.

Module OVN_proof (SG : SecureGroup) (HGPA : HacspecGroupParamAxiom SG).
  Module Schnorr_ZKP := OVN_schnorr_proof SG HGPA.
  Module OR_ZKP := OVN_or_proof SG HGPA.

  Import OR_ZKP.
  Import Schnorr_ZKP.

  (* Redifinition *)
  #[export] Instance Bool_pos : Positive #|'bool|.
  Proof.
    rewrite card_bool. done.
  Defined.

  Axiom power_is_pos : Positive (2^32).

  Check (_ : 'unit).

  (* Definition choiceWitness : choice_type := 'fin #||. *)
  Notation " 'chState' " :=
    t_OvnContractState
    (in custom pack_type at level 2).

  Notation " 'chCastVoteCtx' " :=
    t_CastVoteParam
    (in custom pack_type at level 2).

  Notation " 'chInp' " :=
    (t_OvnContractState × t_CastVoteParam)
    (in custom pack_type at level 2).

  Notation " 'chOut' " :=
    (chOption t_OvnContractState)
    (in custom pack_type at level 2).



  Definition MAXIMUM_BALLOT_SECRECY : nat := 10.

  Module ConcertDefinitions := OVNConcert OVN_impl.

  Program Definition maximum_ballot_secrecy_real :
    package (fset [])
      [interface]
      [interface #val #[ MAXIMUM_BALLOT_SECRECY ] : chInp → chOut] :=
    [package
      #def #[ MAXIMUM_BALLOT_SECRECY ] ('(state, ctx) : chInp) : chOut
      {
        (* is_state ( *)
        (*     matchb (@cast_vote *)
        (*               t_CastVoteParam *)
        (*               (ConcertDefinitions.t_CastVoteParam_t_Sized) *)
        (*               (ConcertDefinitions.t_CastVoteParam_t_HasReceiveContext) *)
        (*               (ret_both (ctx : t_CastVoteParam)) *)
        (*               (ret_both (state : t_OvnContractState))) *)
        (*     with *)
        (*     | Result_Ok_case (_, s) => ret_both (Some (s : t_OvnContractState) : chOption t_OvnContractState) *)
        (*     | Result_Err_case _ => ret_both (None : chOption t_OvnContractState) *)
        (*     end : both (chOption (t_OvnContractState))) *)

        temp ← is_state (@cast_vote
                           (ConcertDefinitions.t_CastVoteParam_t_Sized)
                           (ConcertDefinitions.t_CastVoteParam_t_HasReceiveContext)
                           (ret_both (ctx : t_CastVoteParam)) (ret_both (state : t_OvnContractState))) ;;
        match temp : t_Result (v_A × t_OvnContractState) _ with
        | Result_Ok_case (_, s) => ret (Some s)
        | Result_Err_case _ => ret None
        end
      }
    ].
  Next Obligation.
    fold chElement.
    eapply (valid_package_cons _ _ _ _ _ _ [] []).
    - apply valid_empty_package.
    - intros [].
      simpl.
      rewrite <- !fset0E.
      ssprove_valid'_2.
      all: apply (ChoiceEquality.is_valid_code (both_prog_valid _)).
    - unfold "\notin".
      rewrite <- !fset0E.
      rewrite imfset0.
      rewrite in_fset0.
      easy.
  Qed.

  Program Definition maximum_ballot_secrecy_ideal:
    package (fset [])
      [interface]
      [interface #val #[ MAXIMUM_BALLOT_SECRECY ] : chInp → chOut] :=
    [package
      #def #[ MAXIMUM_BALLOT_SECRECY ] ('(state, ctx) : chInp) : chOut
      {
        let state := ret_both (state : t_OvnContractState) in
        let ctx := (ret_both (ctx : t_CastVoteParam)) in
        let p_i := f_cvp_i ctx : both int32 in
        x ← is_state (f_g_pow (f_cvp_xi ctx)) ;;
        h ← is_state (compute_g_pow_yi (cast_int (WS2 := _) (f_cvp_i ctx)) (f_g_pow_xis state)) ;;
        z ← sample (uniform (H := _) #|Finite.clone _ 'F_q|) ;;
        c ← sample (uniform (H := _) #|Finite.clone _ 'F_q|) ;;
        let y := g ^+ otf z in
        '(zkp_xhy, zkp_abab, zkp_c, zkp_rdrd) ← MyAlg.Simulate (fto (x : gT,h : gT,y)) c ;;
        let '(x,h,y) := otf zkp_xhy in
        let '(zkp_a1, zkp_b1, zkp_a2, zkp_b2) := otf zkp_abab in
        let '(zkp_r1, zkp_d1, zkp_r2, zkp_d2) := otf zkp_rdrd in

        let zkp_c := OR_ZKP.WitnessToField (otf zkp_c : 'F_q) : f_Z in

        let zkp_r1 := OR_ZKP.WitnessToField (zkp_r1 : 'F_q) : f_Z in
        let zkp_d1 := OR_ZKP.WitnessToField (zkp_d1 : 'F_q) : f_Z in
        let zkp_r2 := OR_ZKP.WitnessToField (zkp_r2 : 'F_q) : f_Z in
        let zkp_d2 := OR_ZKP.WitnessToField (zkp_d2 : 'F_q) : f_Z in
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
      }
    ].
  Next Obligation.
    apply /card_gt0P.
    simpl.
    exists 0%R.
    easy.
  Qed.
  Next Obligation.
    eapply (valid_package_cons _ _ _ _ _ _ [] []).
    - apply valid_empty_package.
    - intros [].
      simpl.
      ssprove_valid'_2.
      all: try apply (ChoiceEquality.is_valid_code (both_prog_valid _)).
      repeat (apply valid_sampler ; intros).
      repeat (rewrite !otf_fto ; ssprove_valid'_2).
    - unfold "\notin".
      rewrite <- !fset0E.
      rewrite imfset0.
      rewrite in_fset0.
      easy.
  Qed.

  Definition ɛ_maximum_ballot_secrecy A := AdvantageE maximum_ballot_secrecy_real maximum_ballot_secrecy_ideal A.

  Definition deterministic_bind :
    forall {A B} (b : raw_code A) (f : A -> raw_code B)
      (H : deterministic b)
      (H0 : forall x, deterministic (f x)),
      deterministic (temp ← b ;; f temp).
  Proof.
    intros.
    induction H.
    - simpl.
      apply H0.
    - simpl.
      apply deterministic_get.
      apply X.
    - simpl.
      apply deterministic_put.
      apply IHdeterministic.
  Defined.

  Definition det_iff_sem :
    ∀ {A B : choice_type} (pre : precond) (post : postcond A B) (c₀ : raw_code A) (c₁ : raw_code B)
      (hd₀ : deterministic c₀) (hd₁ : deterministic c₁),
      det_jdg pre post c₀ c₁ hd₀ hd₁ <-> ⊢ ⦃ pre ⦄ c₀ ≈ c₁ ⦃ post ⦄.
  Proof.
    split ; [ apply det_to_sem | apply sem_to_det ].
  Qed.

  Lemma rsymmetry_iff :
    ∀ {A₀ A₁ : ord_choiceType} {pre : precond} {post}
      {c₀ : raw_code A₀} {c₁ : raw_code A₁},
      ⊢ ⦃ λ '(h₁, h₀), pre (h₀, h₁) ⦄ c₁ ≈ c₀
        ⦃ λ '(a₁, h₁) '(a₀, h₀), post (a₀, h₀) (a₁, h₁) ⦄ <->
      ⊢ ⦃ pre ⦄ c₀ ≈ c₁ ⦃ post ⦄.
  Proof.
    intros A₀ A₁ pre post c₀ c₁.
    split.
    - apply rsymmetry.
    - intros.
      apply rsymmetry.
      apply better_r.
      eapply r_swap_post ; [ prop_fun_eq ; reflexivity | ].
      apply H.
  Qed.

  Lemma det_jdg_sym : forall {A : choice_type} {P Q} (c0 c1 : raw_code A) h0 h1,
      det_jdg P Q c0 c1 h0 h1 <->
      det_jdg (λ '(h₁, h₀), P (h₀, h₁)) (λ '(a₁, h₁) '(a₀, h₀), Q (a₀, h₀) (a₁, h₁)) c1 c0 h1 h0.
  Proof.
    intros.
    rewrite det_iff_sem.
    rewrite det_iff_sem.
    now rewrite rsymmetry_iff.
  Qed.

  Lemma det_jdg_trans :
    forall {A : choice_type} {P Q} (c0 c1 c2 : raw_code A) h0 h1 h2,
    forall (Hq : forall {a b c}, Q a b -> Q b c -> Q a c),
    forall (Hp : forall {a c}, P (a, c) -> exists b, P (a, b) /\ P (b, c)),
      det_jdg P Q c0 c1 h0 h1 ->
      det_jdg P Q c1 c2 h1 h2 ->
      det_jdg P Q c0 c2 h0 h2.
  Proof.
    intros A P Q c0 c1 c2 h0 h1 h2 Hq Hp H01 H12.

    unfold det_jdg in H01.
    unfold det_jdg in H12.
    intros s0 s2 H.
    destruct (Hp s0 s2 H) as [s1 []].
    
    refine (Hq _ (det_run c1 s1) _ _ _).
    - apply H01.
      apply H0.
    - apply H12.
      apply H1.
  Qed.

  Lemma det_jdg_bind_l : forall {A : choice_type} {P Q} (c0 c1 : raw_code A) f h0 h1 hf,
      det_jdg P Q c0 c1 h0 h1 ->
      (
        forall x c s₀,
          Q (det_run (ret x) (h := deterministic_ret x) s₀) c ->
          Q (det_run (f x) (h := hf x) s₀) c) ->
      det_jdg P Q (b ← c0 ;; f b) c1 (deterministic_bind c0 f h0 hf) h1
      .
  Proof.
    intros A P Q c0 c1 f h0 h1 hf H HQ_ext.
    intros ? ? ?.
    specialize (H s₀ s₁ H0).

    clear H0.
    generalize dependent s₀.
    induction h0 ; intros.
    - now apply HQ_ext.
    - now apply H.
    - apply IHh0.
      assumption.
  Qed.

  Lemma det_jdg_bind_r : forall {A : choice_type} {P Q} (c0 c1 : raw_code A) f h0 h1 hf,
      det_jdg P Q c0 c1 h0 h1 ->
      (
        forall x c s₁,
          Q c (det_run (ret x) (h := deterministic_ret x) s₁) ->
          Q c (det_run (f x) (h := hf x) s₁)) ->
      det_jdg P Q c0 (b ← c1 ;; f b) h0 (deterministic_bind c1 f h1 hf)
      .
  Proof.
    intros A P Q c0 c1 f h0 h1 hf H HQ_ext.
    intros ? ? ?.
    specialize (H s₀ s₁ H0).

    clear H0.
    generalize dependent s₁.
    induction h1 ; intros.
    - now apply HQ_ext.
    - now apply H.
    - simpl.
      apply IHh1.
      assumption.
  Qed.

  Lemma det_jdg_bind : forall {A : choice_type} {P Q} (c0 c1 : raw_code A) f g h0 h1 hf hg,
      det_jdg P Q c0 c1 h0 h1 ->
      ((forall x y s₀ s₁, Q (det_run (ret x) (h := deterministic_ret x) s₀) (det_run (ret y) (h := deterministic_ret y) s₁) ->
                  Q (det_run (f x) (h := hf x) s₀) (det_run (g y) (h := hg y) s₁))) ->
      det_jdg P Q (b ← c0 ;; f b) (b ← c1 ;; g b) (deterministic_bind c0 f h0 hf) (deterministic_bind c1 g h1 hg)
      .
  Proof.
    intros A P Q c0 c1 f g h0 h1 hf hg H HQ_ext.
    intros ? ? ?.
    specialize (H s₀ s₁ H0).
    clear H0.

    generalize dependent s₀.
    generalize dependent s₁.
    induction h1.
    - induction h0 ; intros.
      + now apply HQ_ext.
      + simpl.
        now apply H.
      + simpl.
        now apply IHh0.
    - intros.
      now apply H.
    - intros.
      now apply IHh1.
  Qed.

  Definition somewhat_substitution : forall {A B : choice_type} (b : both A) (f : A -> raw_code B) (c : raw_code B),
      (forall x, deterministic (f x)) ->
          ⊢ ⦃ λ '(s₀, s₁), s₀ = s₁ ⦄ ret (is_pure b) ≈ is_state b ⦃ λ '(b₀, s₀) '(b₁, s₁), b₀ = b₁ ∧ s₀ = s₁ ⦄ ->
          ⊢ ⦃ λ '(s₀, s₁), s₀ = s₁ ⦄ temp ← ret (is_pure b) ;; f temp ≈ c ⦃ λ '(b₀, s₀) '(b₁, s₁), b₀ = b₁ ∧ s₀ = s₁ ⦄ ->
          ⊢ ⦃ λ '(s₀, s₁), s₀ = s₁ ⦄ temp ← is_state b ;; f temp ≈ c ⦃ λ '(b₀, s₀) '(b₁, s₁), b₀ = b₁ ∧ s₀ = s₁ ⦄.
  Proof.
    clear ; intros ? ? ? ? ? ? b_eq ?.

    eapply r_transL.
    2: apply H.
    eapply r_bind.

    - apply b_eq.
    - intros.
      simpl.
      apply rpre_hypothesis_rule'.
      intros ? ? [].
      eapply rpre_weaken_rule.
      1: subst ; apply rreflexivity_rule.
      intros ? ? [].
      now subst.
  Qed.

  Lemma maximum_ballot_secrecy_success:
    ∀ LA A,
      ValidPackage LA [interface
                         #val #[ MAXIMUM_BALLOT_SECRECY ] : chInp → chOut
        ] A_export A →
      fdisjoint LA fset0 →
      ɛ_maximum_ballot_secrecy A = 0%R.
  Proof.
    intros.
    unfold ɛ_maximum_ballot_secrecy.
    unfold maximum_ballot_secrecy_real.
    unfold maximum_ballot_secrecy_ideal.
    apply: eq_rel_perf_ind_eq.
    all: ssprove_valid.
    (* 1:{ instantiate (1 := heap_ignore Sigma_locs). *)
    (*     ssprove_invariant. *)
    (*     apply fsubsetUl. } *)
    2,3: rewrite - fset0E ; apply fdisjoints0.
    1:{
      unfold eq_up_to_inv.
      intros.
      unfold get_op_default.

      (* rewrite <- fset1E in H0. *)
      (* apply (ssrbool.elimT (fset1P _ _)) in H0. *)
      (* inversion H0. *)

      Opaque MyAlg.Simulate.

      simpl (lookup_op _ _).
      fold chElement.

      (* set (setm _ _ _ _). *)
      (* unfold mkdef in o. *)
      (* simpl in o. *)

      (* subst o. *)
      rewrite !setmE.
      rewrite <- fset1E in H1.
      rewrite in_fset1 in H1.
      apply (ssrbool.elimT eqP) in H1.
      inversion H1 ; subst.

      rewrite eqxx.
      simpl.

      destruct choice_type_eqP ; [ | now apply r_ret ].
      destruct choice_type_eqP ; [ | now apply r_ret ].
      subst.
      rewrite !cast_fun_K.
      clear e e0.

      destruct x as [? ?].

      unfold cast_vote at 1.
      rewrite !bind_assoc; rewrite !bind_rewrite.
      rewrite !bind_assoc; rewrite !bind_rewrite.
      fold chElement.
      rewrite !bind_assoc.
      apply (@somewhat_substitution _ ((chOption t_OvnContractState)) f_accept) ; [admit | admit | rewrite bind_rewrite].
      rewrite !bind_assoc; rewrite !bind_rewrite.
      rewrite !bind_assoc; rewrite !bind_rewrite.
      rewrite !bind_assoc; rewrite !bind_rewrite.
      rewrite !bind_assoc; rewrite !bind_rewrite.
      rewrite !bind_assoc; rewrite !bind_rewrite.
      rewrite !bind_assoc.
      apply (@somewhat_substitution _ ((chOption t_OvnContractState)) (compute_group_element_for_vote _ _ _)) ; [admit | admit | rewrite bind_rewrite].
      rewrite !bind_rewrite.
      rewrite !bind_assoc; rewrite !bind_rewrite.
      rewrite !bind_assoc; rewrite !bind_rewrite.
      rewrite !bind_assoc; rewrite !bind_rewrite.

      rewrite !bind_assoc; rewrite !bind_rewrite.
      rewrite !bind_assoc; rewrite !bind_rewrite.
      rewrite !bind_assoc.
      apply (@somewhat_substitution _ ((chOption t_OvnContractState)) (compute_group_element_for_vote _ _ _)) ; [admit | admit | rewrite bind_rewrite].
            rewrite !bind_rewrite.
      rewrite !bind_assoc; rewrite !bind_rewrite.
      rewrite !bind_assoc; rewrite !bind_rewrite.
      rewrite !bind_assoc; rewrite !bind_rewrite.

      rewrite !bind_assoc; rewrite !bind_rewrite.
      rewrite !bind_assoc; rewrite !bind_rewrite.
      rewrite !bind_assoc.
      apply (@somewhat_substitution _ ((chOption t_OvnContractState)) (compute_group_element_for_vote _ _ _)) ; [admit | admit | rewrite bind_rewrite].
      rewrite !bind_rewrite.
      rewrite !bind_assoc; rewrite !bind_rewrite.
      rewrite bind_assoc.

      eassert (is_state (zkp_one_out_of_two _ _ _ _ _ _) = match lookup_op or_proof_args.Sigma.RUN_interactive (or_proof_args.Sigma.RUN, ((chProd or_proof_args.MyAlg.choiceStatement or_proof_args.MyAlg.choiceWitness), or_proof_args.MyAlg.choiceTranscript)) with Some c => temp ← c (fto (g ^+ _,(
                 is_pure (compute_g_pow_yi
                 (cast_int (f_cvp_i (solve_lift ret_both (f_parameter_cursor (ret_both s0)))))
                 (f_g_pow_xis (ret_both s))) : gT),_), ( fto ((or_proof_args.FieldToWitness (is_pure (f_cvp_xi (solve_lift ret_both (f_parameter_cursor (ret_both s0)))))) : 'F_q, _, _))) ;; _ | None => _ end) by admit.
      rewrite H2.
      simpl (lookup_op _ _).
      destruct choice_type_eqP ; [ | subst ; contradiction ].
      destruct choice_type_eqP ; [ | subst ; contradiction ].
      subst.
      rewrite cast_fun_K.

      rewrite otf_fto.

      rewrite !bind_assoc.
      simpl.
      rewrite otf_fto.

      apply r_assertD ; [ reflexivity | ].
      unfold #assert.

      
      unfold f_parameter_cursor.
      setoid_rewrite bind_assoc.
      setoid_rewrite bind_assoc.
      destruct s0.
      simpl.
      destruct s1.
      -
        rewrite !bind_assoc.
        
        
      rewrite !bind_assoc; rewrite !bind_rewrite.
      rewrite !bind_assoc; rewrite !bind_rewrite.

      rewrite !bind_assoc; rewrite !bind_rewrite.
      rewrite !bind_assoc; rewrite !bind_rewrite.
      rewrite !bind_assoc.

      rewrite !bind_assoc; 
      
      
      rewrite !bind_assoc; rewrite !bind_rewrite.
      rewrite !bind_assoc; rewrite !bind_rewrite.
      rewrite !bind_assoc; rewrite !bind_rewrite.
      rewrite !bind_assoc; rewrite !bind_rewrite.
      rewrite !bind_assoc.
      rewrite bind_rewrite.
      Transparent prod_to_prod_n.
      rewrite !bind_assoc.
      
      
      apply r_nice_swap_rule ; [admit | admit | ].

      
      apply (@somewhat_substitution (v_G) ((chOption t_OvnContractState)) (f_g_pow (f_cvp_xi (ret_both s0)))) ; [admit | admit | rewrite bind_rewrite].
      apply (@somewhat_substitution (v_G) ((chOption t_OvnContractState)) _) ; [admit | admit | rewrite bind_rewrite].

      apply pkg_rhl.r_const_sample_L ; [admit | intros ].
      apply pkg_rhl.r_const_sample_L ; [admit | intros ].
      apply pkg_rhl.r_const_sample_L ; [admit | intros ].
      apply pkg_rhl.r_const_sample_L ; [admit | intros ].
      apply pkg_rhl.r_const_sample_L ; [admit | intros ].
      rewrite !otf_fto.
      simpl.
      rewrite !otf_fto.
      rewrite bind_rewrite.



      apply r_nice_swap_rule ; [admit | admit | ].
      
      apply (@somewhat_substitution ((t_Result (v_A × t_OvnContractState) t_ParseError)) (chOption t_OvnContractState) _ _ _) ; [admit | admit | rewrite bind_rewrite].
      setoid_rewrite bind_rewrite.

      set (ret _).
      set (zkp_one_out_of_two _ _ _  _ _ _) in r.
      Locate choiceWitness.
      Check lookup_op or_proof_args.Sigma.RUN_interactive (or_proof_args.Sigma.RUN, ((chProd or_proof_args.MyAlg.choiceStatement or_proof_args.MyAlg.choiceWitness), or_proof_args.MyAlg.choiceTranscript)).
      eassert (b = match lookup_op or_proof_args.Sigma.RUN_interactive (or_proof_args.Sigma.RUN, ((chProd or_proof_args.MyAlg.choiceStatement or_proof_args.MyAlg.choiceWitness), or_proof_args.MyAlg.choiceTranscript)) with Some c => c _ | None => _ end) by admit.
      subst r.
      rewrite H2.
      subst b.

      apply r_ret.
      split.
      2: easy.
      destruct s as [[[[[[]]]]]].
      destruct s0 as [[[[[]]]]].
      simpl.
      unfold Build_t_OvnContractState at 1.
      simpl.
      unfold Build_t_OvnContractState at 1.
      simpl.
      f_equal.

      rewrite hacspec_function_guarantees.
      Transparent f_zkp_xis.
      Transparent f_g_pow_xis.
      Transparent Build_t_OvnContractState.
      Transparent f_commit_vis.
      Transparent f_g_pow_xi_yi_vis.
      simpl.

      progress repeat (rewrite pair_equal_spec ; split).
      - reflexivity.
      - reflexivity.
      - reflexivity.
      - Transparent update_at_usize.
        Transparent lift3_both.
        Transparent lift2_both.
        Transparent lift1_both.
        Transparent cast_int.
        Transparent f_cvp_xi.
        Transparent f_cvp_i.
        simpl.
        Transparent compute_group_element_for_vote.
        simpl.
        Transparent compute_g_pow_yi.
        simpl.
        Transparent f_cvp_vote.
        simpl.
        unfold f_parameter_cursor.
        simpl.
        f_equal.
        simpl.
        Transparent f_field_one.
        Transparent f_field_zero.
        simpl.

        admit.
      - simpl.
        f_equal.
    
        
        unfold zkp_one_out_of_two at 1.
        simpl.
        rewrite hacspec_function_guarantees.
        simpl.
        (* One out of two ! *)

      - 
      -
      - 
  Qed.
  (* Admitted. *)

End OVN_proof.
