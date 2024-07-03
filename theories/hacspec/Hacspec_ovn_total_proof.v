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

Module OVN_proof (HGPA : HacspecGroupParamAxiom).
  Module Schnorr_ZKP := OVN_schnorr_proof HGPA.
  Module OR_ZKP := OVN_or_proof HGPA.

  Import Schnorr_ZKP.
  Import OR_ZKP.

  Include HGPA.

  (* begin details : helper defintions *)
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

  Definition somewhat_substitution : forall {A : choice_type} {B : choiceType} (b : both A) (f : A -> raw_code B) (c : raw_code B),
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
      apply Misc.rpre_hypothesis_rule'.
      intros ? ? [].
      eapply rpre_weaken_rule.
      1: subst ; apply rreflexivity_rule.
      intros ? ? [].
      now subst.
  Qed.

  Definition somewhat_let_substitution :
               forall {A C : choice_type} {B : choiceType} (f : C -> raw_code B) (c : raw_code B) (y : both A) (r : both A -> both C),
                 (forall x, deterministic (f x)) ->
          ⊢ ⦃ λ '(s₀, s₁), s₀ = s₁ ⦄ b_temp ← is_state y ;; temp ← is_state (r (ret_both b_temp)) ;; f temp ≈ c ⦃ λ '(b₀, s₀) '(b₁, s₁), b₀ = b₁ ∧ s₀ = s₁ ⦄ ->
          ⊢ ⦃ λ '(s₀, s₁), s₀ = s₁ ⦄ temp ← is_state (letb 'b := y in r b) ;; f temp ≈ c ⦃ λ '(b₀, s₀) '(b₁, s₁), b₀ = b₁ ∧ s₀ = s₁ ⦄.
  Proof.
    intros.
  Admitted.
  (* end details : helper defintions *)

  (* (* Redifinition *) *)
  (* #[export] Instance Bool_pos : Positive #|'bool|. *)
  (* Proof. *)
  (*   rewrite card_bool. done. *)
  (* Defined. *)

  Definition power_is_pos : Positive (2^32). Proof. easy. Qed.

  (* Definition choiceWitness : choice_type := 'fin #||. *)
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
    ((int32 × f_Z × f_Z × f_Z × f_Z × 'bool))
    (in custom pack_type at level 2).

  Notation " 'chAuxOut' " :=
    (chProd
        (chProd (chProd OR_ZKP.MyAlg.choiceStatement OR_ZKP.MyAlg.choiceMessage) OR_ZKP.MyAlg.choiceChallenge)
        OR_ZKP.MyAlg.choiceResponse)
    (in custom pack_type at level 2).

  (* × t_CastVoteParam = (int32 × v_Z × int32 × int32 × int32 × 'bool) *)

  Definition MAXIMUM_BALLOT_SECRECY : nat := 10.

  Program Definition maximum_ballot_secrecy_real :
    package (fset [])
      [interface]
      [interface
         #val #[ Sigma.RUN ] : chAuxInp → chAuxOut
      ] :=
    [package
      #def #[ MAXIMUM_BALLOT_SECRECY ] ('(state, (cvp_i, cvp_xi, cvp_vote)) : chInp) : chOut
      {
        #import {sig #[ Sigma.RUN ] : chInp → chAuxOut } as RUN ;;

        let state := ret_both (state : t_OvnContractState) in

        (* Setup and inputs for algorithm *)
        cvp_zkp_random_w ← sample (uniform (2^32) (* (H := Zq_pos) #|Finite.clone _ 'Z_q| *)) ;;
        cvp_zkp_random_d ← sample (uniform (2^32) (* (H := Zq_pos) #|Finite.clone _ 'Z_q| *)) ;;
        cvp_zkp_random_r ← sample (uniform (2^32) (* (H := Zq_pos) #|Finite.clone _ 'Z_q| *)) ;;

        let ctx := prod_b (
                       ret_both cvp_i,
                       ret_both cvp_xi,
                       ret_both (Hacspec_Lib_Pre.repr _ (Z.of_nat (nat_of_ord cvp_zkp_random_w))),
                       ret_both (Hacspec_Lib_Pre.repr _ (Z.of_nat (nat_of_ord cvp_zkp_random_r))),
                       ret_both (Hacspec_Lib_Pre.repr _ (Z.of_nat (nat_of_ord cvp_zkp_random_d))),
                       ret_both (cvp_vote : 'bool)
                      ) : both t_CastVoteParam in

        (* before zkp_vi *)
        g_pow_yi ← is_state (compute_g_pow_yi (cast_int (WS2 := _) (f_cvp_i ctx)) (f_g_pow_xis state)) ;;
        let g_pow_yi := ret_both g_pow_yi in

        (* zkp_vi *)
        zkp_vi ← RUN _
          (* is_state (zkp_one_out_of_two (f_cvp_zkp_random_w ctx) (f_cvp_zkp_random_r ctx) (f_cvp_zkp_random_d ctx) g_pow_yi (f_cvp_xi ctx) (f_cvp_vote ctx)) *) ;;
          (* is_state (cast_vote (ctx) (ret_both (state : t_OvnContractState))) ;; *)
        let zkp_vi := ret_both zkp_vi in

        (* after zkp_vi *)
        temp ← is_state (letb g_pow_xi_yi_vi := compute_group_element_for_vote (f_cvp_xi ctx) (f_cvp_vote ctx) g_pow_yi in
    letb cast_vote_state_ret := f_clone state in
    letb cast_vote_state_ret := Build_t_OvnContractState[cast_vote_state_ret] (f_g_pow_xi_yi_vis := update_at_usize (f_g_pow_xi_yi_vis cast_vote_state_ret) (cast_int (WS2 := _) (f_cvp_i ctx)) g_pow_xi_yi_vi) in
    letb cast_vote_state_ret := Build_t_OvnContractState[cast_vote_state_ret] (f_zkp_vis := update_at_usize (f_zkp_vis cast_vote_state_ret) (cast_int (WS2 := _) (f_cvp_i ctx)) zkp_vi) in
    Result_Ok (prod_b (f_accept,cast_vote_state_ret))) ;;

        (* handle output *)
        match temp : t_Result (HacspecGroup.v_A × t_OvnContractState) _ with
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
      apply valid_sampler ; intros.
      apply valid_sampler ; intros.
      apply valid_sampler ; intros.
      ssprove_valid'_2.
      all: try apply (ChoiceEquality.is_valid_code (both_prog_valid _)).
    - unfold "\notin".
      rewrite <- !fset0E.
      rewrite imfset0.
      rewrite in_fset0.
      easy.
  Qed.
  Fail Next Obligation.

  (* Definition maximum_ballot_secrecy_real_game : Game_Type [interface #val #[MAXIMUM_BALLOT_SECRECY] : chInp → chOut ] := *)
  (*   ({| locs := fset [::]; *)
  (*      locs_pack := maximum_ballot_secrecy_real |}). *)

  Program Definition maximum_ballot_secrecy_ideal:
    package (fset [])
      [interface]
      [interface #val #[ MAXIMUM_BALLOT_SECRECY ] : chInp → chOut] :=
    [package
      #def #[ MAXIMUM_BALLOT_SECRECY ] ('(state, (cvp_i, cvp_xi, cvp_vote)) : chInp) : chOut
      {
        let state := ret_both (state : t_OvnContractState) in
        let p_i := ret_both cvp_i : both int32 in
       
        yi ← sample (uniform (H := Zq_pos) #|Finite.clone _ 'Z_q|) ;;
        c ← sample (uniform (H := Zq_pos) #|Finite.clone _ 'Z_q|) ;;

         h ← is_state (compute_g_pow_yi (cast_int (WS2 := _) p_i) (f_g_pow_xis state)) ;;

        x ← is_state (f_g_pow (ret_both cvp_xi)) ;;
        let y := g ^+ (otf yi * FieldToWitness cvp_xi + (if cvp_vote then 1 else 0))%R in

        '(zkp_xhy, zkp_abab, zkp_c, zkp_rdrd) ← MyAlg.Simulate (fto (x : gT, h : gT, y)) c ;;

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

  Definition ɛ_maximum_ballot_secrecy A := AdvantageE maximum_ballot_secrecy_real maximum_ballot_secrecy_ideal A.


  Definition maximum_ballot_secrecy_real_to_or_run A := AdvantageE maximum_ballot_secrecy_real (hacspec_or_run) A.

  Lemma maximum_ballot_secrecy_to_or:
    ∀ LA A,
      ValidPackage LA [interface
                         #val #[ MAXIMUM_BALLOT_SECRECY ] : chInp → chOut
        ] A_export A →
      fdisjoint LA fset0 →
      maximum_ballot_secrecy_real_to_or_run A = 0%R.
  Proof.
    intros.
    unfold maximum_ballot_secrecy_real_to_or_run.
    unfold hacspec_or_run.
    unfold maximum_ballot_secrecy_real.
    apply: eq_rel_perf_ind_eq.
    all: ssprove_valid.
    (* 2,3: rewrite - fset0E ; apply fdisjoints0. *)
    (* 1:{ *)
    
    2:{
            unfold eq_up_to_inv.
      intros.
      unfold get_op_default.

      (* rewrite <- fset1E in H0. *)
      (* apply (ssrbool.elimT (fset1P _ _)) in H0. *)
      (* inversion H0. *)

      Opaque MyAlg.Simulate.

      simpl (lookup_op _ _) ; fold chElement.

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

      destruct x as [state [[cvp_i cvp_xi] cvp_vote]].

      set (lhs_f := fun _ => _) at 4.
      set (rhs_f := fun _ => _) at 5.


    }


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
    From Crypt Require Import SigmaProtocol.

    Set Printing Coercions.
    pose run_interactive_or_shvzk.

    epose (aux_pack := _ : raw_package).

    epose (aux_pack ∘ hacspec_or_run).
    replace (pack maximum_ballot_secrecy_real) with r.
    2: admit.
    subst r.

    epose (aux_pack ∘ Sigma.SHVZK_real_aux ∘ Sigma.SHVZK_ideal).
    replace (pack maximum_ballot_secrecy_ideal) with r.
    2: admit.
    subst r.

    rewrite <- Advantage_link.
    
    apply (AdvantageE_le_0 _ _ _ ).
    eapply Order.le_trans ; [ eapply (Advantage_triangle _ _ (pack Sigma.SHVZK_real_aux ∘ pack Sigma.SHVZK_real) _) | ].
    erewrite (run_interactive_or_shvzk _ (A ∘ aux_pack) _ _).
    rewrite GRing.add0r.

    rewrite <- Advantage_link.

    epose (shvzk_success _ ((A ∘ aux_pack) ∘ pack Sigma.SHVZK_real_aux) _ _).
    unfold Sigma.ɛ_SHVZK in e0.
    now rewrite e0.
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

      simpl (lookup_op _ _) ; fold chElement.

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

      destruct x as [state [[cvp_i cvp_xi] cvp_vote]].

      set (lhs_f := fun _ => _) at 4.
      set (rhs_f := fun _ => _) at 5.

      (* Remove wrapping *)
      Opaque zkp_one_out_of_two.

      unfold cast_vote at 1.

      setoid_rewrite (bind_assoc (is_state (f_get _))).
      setoid_rewrite (bind_assoc (is_state (f_get _))).
      simpl (is_state _) at 1 ; fold chElement.
      setoid_rewrite bind_rewrite.

      setoid_rewrite bind_assoc.

      setoid_rewrite (bind_assoc (is_state (impl__map_err _ _))).
      unfold prod_to_prod at 1.
      unfold f_parameter_cursor.
      repeat unfold prod_both at 1.
      simpl (is_state _) at 1 ; fold chElement.
      setoid_rewrite bind_rewrite.


      setoid_rewrite bind_assoc.
      simpl (is_state (solve_lift ret_both (Hacspec_Lib_Pre.Ok _))).
      setoid_rewrite (bind_rewrite _).
      simpl is_state.
      setoid_rewrite (bind_rewrite _).
      (* / Remove wrapping *)

      (* simplify ctx arg *)
      unfold f_cvp_i at 1.
      setoid_rewrite bind_ret_both.
      simpl (solve_lift _).

      unfold let_both at 1.

      unfold f_cvp_zkp_random_w at 1.
      unfold f_cvp_zkp_random_d at 1.
      unfold f_cvp_zkp_random_r at 1.
      unfold f_cvp_xi at 1.
      unfold f_cvp_vote at 1.
      setoid_rewrite bind_ret_both.
      simpl (solve_lift _).
      (* / simplify ctx args *)

      assert (forall {A B : choiceType} (f : _ -> raw_code A) (k : A -> raw_code B),
                  (cvp_zkp_random_w ← sample uniform (2 ^ 32) ;;
                  x ← (f cvp_zkp_random_w) ;;
                  k x)
                  =
                  (x ← (cvp_zkp_random_w ← sample uniform (2 ^ 32) ;;
                       f cvp_zkp_random_w) ;;
                  k x)
             ) by admit.
      setoid_rewrite (H2 _ _ (fun cvp_zkp_random_r => _)).
      setoid_rewrite (H2 _ _ (fun cvp_zkp_random_d => _)).
      setoid_rewrite (H2 _ _ (fun cvp_zkp_random_w => _)).

      eapply r_transR with (c₁ :=
                              x ← (cvp_zkp_random_w ← sample uniform (2 ^ 32) ;;
                                   cvp_zkp_random_d ← sample uniform (2 ^ 32) ;;
                                   cvp_zkp_random_r ← sample uniform (2 ^ 32) ;;
                                   is_state
                                     (zkp_one_out_of_two
                  _
                  _
                  _
                  _
                  _
                  _)) ;; c ← (is_state (_ : both (t_Result (v_A × t_OvnContractState) t_ParseError))) ;; lhs_f c).
      2:{
        eapply r_transR with (c₁ :=
                                x ← (cvp_zkp_random_w ← sample uniform (2 ^ 32) ;;
                                     cvp_zkp_random_d ← sample uniform (2 ^ 32) ;;
                                     cvp_zkp_random_r ← sample uniform (2 ^ 32) ;;
                                     b_temp ← is_state
                                       (zkp_one_out_of_two
                                          _
                                          _
                                          _
                                          _
                                          _
                                          _) ;; _) ;; lhs_f _).
        2:{
          eapply r_bind with (mid := pre_to_post (λ '(s₀, s₁), s₀ = s₁)).
          2:{
            intros.
            apply rpre_hypothesis_rule.
            intros ? ? []. subst.
            eapply rpre_weaken_rule ; [intros | admit ].
            eapply rpost_weaken_rule ; [intros | admit ].
            apply rreflexivity_rule.
          }

          eapply r_uniform_bij with (f := id) ; [ admit | intros ].
          eapply r_uniform_bij with (f := id) ; [ admit | intros ].
          eapply r_uniform_bij with (f := id) ; [ admit | intros ].

          rewrite <- (bind_ret _ (is_state _) ).
          eapply somewhat_let_substitution ; [admit | ].

          (* ssprove_sync_eq. *)
          
          eapply r_bind with (mid := pre_to_post (λ '(s₀, s₁), s₀ = s₁)).
          {
            intros.
            apply rpre_hypothesis_rule.
            intros ? ? []. subst.
            eapply rpre_weaken_rule ; [intros | admit ].
            eapply rpost_weaken_rule ; [intros | admit ].
            apply rreflexivity_rule.
          }
          intros.
          
          
          eapply r_bind with (mid := pre_to_post (λ '(s₀, s₁), s₀ = s₁)).
          {
            intros.
            apply rpre_hypothesis_rule.
            intros ? ? []. subst.
            eapply rpre_weaken_rule ; [intros | admit ].
            eapply rpost_weaken_rule ; [intros | admit ].
            apply rreflexivity_rule.
          }
          intros.

          apply r_ret.
          intros ? ? []. subst. split ; reflexivity.
        }
        {
          eapply r_uniform_bij with (f := id) ; [ admit | intros ].
          eapply r_uniform_bij with (f := id) ; [ admit | intros ].
          eapply r_uniform_bij with (f := id) ; [ admit | intros ].
          fold @bind.
          rewrite bind_assoc.

          eapply r_bind with (mid := pre_to_post (λ '(s₀, s₁), s₀ = s₁)).
          {
            intros.
            apply rpre_hypothesis_rule.
            intros ? ? []. subst.
            eapply rpre_weaken_rule ; [intros | admit ].
            eapply rpost_weaken_rule ; [intros | admit ].
            apply rreflexivity_rule.
          }
          intros.
          

          eapply r_bind with (mid := pre_to_post (λ '(s₀, s₁), s₀ = s₁)).
          {
            intros.
            apply rpre_hypothesis_rule.
            intros ? ? []. subst.
            eapply rpre_weaken_rule ; [intros | admit ].
            eapply rpost_weaken_rule ; [intros | admit ].

            rewrite bind_ret.
            admit.
          }
          intros.

          apply rpre_hypothesis_rule.
          intros ? ? []. subst.

          eapply rpre_weaken_rule ; [intros | admit ].
          eapply rpost_weaken_rule ; [intros | admit ].

          apply rreflexivity_rule.
        }
      }

      set (compute_g_pow_yi _ _).

      eapply r_transR.
      2:{
        eapply r_bind with (m₁ :=
                              match
                                lookup_op Sigma.RUN_interactive
                                  (Sigma.RUN, (MyAlg.choiceStatement × MyAlg.choiceWitness, MyAlg.choiceTranscript))
                              with
                              | Option_Some c => c
                              | None =>
                                  λ _ : src (Sigma.RUN, (MyAlg.choiceStatement × MyAlg.choiceWitness, MyAlg.choiceTranscript)),
                                    ret
                                      (chCanonical
                                         (chtgt
                                            (Sigma.RUN, (MyAlg.choiceStatement × MyAlg.choiceWitness, MyAlg.choiceTranscript))))
                              end
                                ((fto (is_pure b : gT, _, _) : MyAlg.choiceStatement,
                                     fto (FieldToWitness cvp_xi, _, _))
                                  : (MyAlg.choiceStatement * MyAlg.choiceWitness))).
        {
          apply rsymmetry.
          
          (* (x, h, y) , (xi, vi, h) *)

          
          epose (or :=
                   or_run_eq _
                     (
                       (_, is_pure b, _),
                       (FieldToWitness cvp_xi , _ , _)
                )).
          unfold ".1", ".2" in or.

          eapply r_transR.
          2:{
            unfold MyAlg.Sigma_locs in or.
            
            eapply rpost_weaken_rule ; [ | admit ].
            eapply rpre_weaken_rule ; [ | admit ].

            apply or.
          }

          assert (
              forall {A B : choice_type} P (a : raw_code A) (b : raw_code B) Q,
                ⊢ ⦃ P ⦄ a ≈ #assert true ;; b ⦃ Q ⦄ ->
                ⊢ ⦃ P ⦄ a ≈ b ⦃ Q ⦄).
          {
            clear ; intros. apply H.
          }
          apply H3 ; clear H3.
          apply r_assertD ; [ admit | intros ].

          ssprove_sync_eq. intros.
          ssprove_sync_eq. intros.
          ssprove_sync_eq. intros.
          eassert (cvp_vote = (_ == ((is_pure b : gT) ^+ FieldToWitness cvp_xi * HGPA.HacspecGroup.g)%g)) by admit.
          rewrite <- H3.

          rewrite WitnessToFieldCancel.
          assert (forall {A : choice_type} (x : A), (solve_lift ret_both x) = (ret_both x)) by admit.
          rewrite !H4.

          assert (forall {A : choice_type} (x : both A), (ret_both (is_pure x)) = x) by admit.
          rewrite H5.
          
          apply rreflexivity_rule.
        }

        intros.
        apply rpre_hypothesis_rule.
        intros ? ? ?.
        eapply rpre_weaken_rule ; [intros | admit ].
        eapply rpost_weaken_rule ; [intros | admit ].
        apply rreflexivity_rule.
      }

      pose run_interactive_or_shvzk.
      
          (compute_g_pow_yi
             (cast_int
                (solve_lift ret_both cvp_i))
             (f_g_pow_xis (ret_both state))).
          
          unfold assert in or.
          
          set (r := pkg_core_definition.sampler _ _).

          (* set (f_cvp_zkp_random_w _). *)
          (* set (f_cvp_zkp_random_r _). *)
          (* set (f_cvp_zkp_random_d _). *)
          (* set (ret_both _). *)
          (* set (f_cvp_xi _). *)
          (* set (f_cvp_vote _). *)

          assert (
              forall {A B : choice_type} P (a : raw_code A) (b : raw_code B) Q,
                ⊢ ⦃ P ⦄ #assert true ;; a ≈ b ⦃ Q ⦄ ->
                ⊢ ⦃ P ⦄ a ≈ b ⦃ Q ⦄).
          {
            clear ; intros. apply H.
          }
          apply H3 ; clear H3.

          epose (MyParam.R (_, _, _) (_, _, _)).

          subst r.
          simpl in or.
          set (true).
          replace b0 with b.

          unfold r.
          apply rsymmetry.

          eapply rpost_weaken_rule ; [ | admit ].
          eapply rpre_weaken_rule ; [ | admit ].
          
          apply or_run_eq.
          
          eapply rpost_weaken_rule ; [ | admit ].
          eapply rpre_weaken_rule ; [ | admit ].

          apply rreflexivity_rule.

          eassert (true = MyParam.R (_, _, _) (_, _, _)) by admit.
          
          
          eapply r_transR.
          2:{
            apply rsymmetry.

          
          apply rsymmetry.
          
      
      (* Transparent MyAlg.Simulate. *)
      (* unfold MyAlg.Simulate ; *)
      (* simpl ; fold chElement ; *)
      (* setoid_rewrite otf_fto. *)

      eapply r_transL ; [ apply r_uniform_triple ; intros ; apply rreflexivity_rule | ].
      apply rsymmetry.
      eapply r_transL ; [ apply r_uniform_prod ; intros ; apply rreflexivity_rule | ].
      apply rsymmetry.

      eapply r_uniform_bij ; [ admit | intros ].
      destruct (ch3prod x) as [[w r] d].

      unfold let_both at 1.

      eapply rpost_weaken_rule ; [ | admit ].
      eapply rpre_weaken_rule ; [ | admit ].
      
      eapply somewhat_let_substitution ; [admit | ].

      pose run_interactive_or_shvzk.

      destruct ch2prod.
      
      unfold AdvantageE in e.
      
      
      
        with
        (f := (fun t =>
                 let '(d, r, r_other) := ch3prod t in
                 let '(w, d2, r2) :=
                   if vi
                   then
                     let '(d2,r2) := (d, r) in
                     let 'w := fto ((otf r2) + (m * (otf d2))) in
                     let 'd := fto (otf c - otf d2) in
                     (w, d, r_other)
                   else
                     let '(d2,r1) := (d, r_other) in
                     (fto ((otf r1) + (m * (otf c - otf d2))), fto (otf d2), r)
                 in
                 prod3ch (w, d2, r2) (* w d r *)
        )%R).
      {
        eapply Bijective with
          (g :=  (fun (wdr : Arit (uniform (_ * _ * _))) =>
                   let '(w, d2, r2) := ch3prod wdr in
                   let '(d, r, r_other) :=
                     if vi
                     then
                       let d := fto (otf c - otf d2) in
                       let r := fto (otf w - (otf c - otf d2) * m) in
                       (d, r, r2)
                     else
                       let r := fto (otf w - m * (otf c - otf d2)) in
                       let r2 := r2 in
                       (d2, r2, r)
                   in
                   prod3ch (d, r, r_other))%R).
        {
          intros xyz.
          rewrite -[RHS](prod3ch_ch3prod xyz).
          simpl.
          set (ch3prod _) at 2.
          destruct s as [[d r] r_other] eqn:wrd_eq.
          subst s.
          rewrite wrd_eq.

          rewrite (if_bind (fun '(x,y,z) => _)).
          rewrite if_bind.
          rewrite !ch3prod_prod3ch.
          rewrite !(if_bind (fun '(x,y,z) => _)).

          rewrite if_if.

          rewrite !otf_fto !fto_otf.

          rewrite !subKr.
          rewrite mulrC.
          rewrite !addrK.
          rewrite !fto_otf.

          rewrite if_const.
          reflexivity.
        }
        {
          intros xyz.
          rewrite -[RHS](prod3ch_ch3prod xyz).
          simpl.
          set (ch3prod _) at 2.
          destruct s as [[w d] r] eqn:wrd_eq.
          subst s.
          rewrite wrd_eq.

          rewrite (if_bind (fun '(x,y,z) => _)).
          rewrite if_bind.
          rewrite !ch3prod_prod3ch.
          rewrite !(if_bind (fun '(x,y,z) => _)).

          rewrite if_if.

          rewrite !otf_fto !fto_otf.

          rewrite !subKr.
          rewrite mulrC.
          rewrite !subrK.
          rewrite !fto_otf.

          rewrite if_const.
          reflexivity.
        }
      }

      
      set (is_state _).
      replace (is_state _) with
        (' g_pow_yi ← is_state (compute_g_pow_yi
                 (cast_int
                    (f_cvp_i
                       (solve_lift ret_both
                                     (f_parameter_cursor
                                        prod_b (ret_both cvp_i, ret_both cvp_xi,
                                          ret_both (wrepr U32 (Z.of_nat cvp_zkp_random_w)),
                                          ret_both (wrepr U32 (Z.of_nat cvp_zkp_random_r)),
                                          ret_both (wrepr U32 (Z.of_nat cvp_zkp_random_d)),
                                          ret_both cvp_vote))))) (f_g_pow_xis (ret_both state))) ;;
         _).

      setoid_rewrite (bind_assoc (is_state (f_accept))).
      fold zkp_one_out_of_two.
      
      eapply r_transL.
      1:{
        eapply r_uniform_bij ; [ admit | intros ].
        eapply r_uniform_bij ; [ admit | intros ].
        eapply r_uniform_bij ; [ admit | intros ].

        apply r_nice_swap_rule ; [ admit | admit | ].
        eapply rpost_weaken_rule ; [ | admit ].
        apply somewhat_let_substitution ; [ admit | ].
        eapply r_bind.
        - apply rreflexivity_rule.
        - intros.

          eapply rpost_weaken_rule ; [ | admit ].
          eapply rpre_weaken_rule ; [ | admit ].

          apply somewhat_let_substitution ; [ admit | ].

          eapply rpost_weaken_rule ; [ | admit ].
          eapply rpre_weaken_rule ; [ | admit ].

          apply rreflexivity_rule.
      }
      hnf.

      setoid_rewrite bind_assoc.

      simpl (is_state (solve_lift ret_both (Hacspec_Lib_Pre.Ok _))).
      setoid_rewrite (bind_rewrite _).

      setoid_rewrite bind_assoc.
      replace (is_state f_accept) with (ret (is_pure f_accept)) by admit.
      setoid_rewrite bind_rewrite.
      (* *)

      setoid_rewrite bind_assoc.
      setoid_rewrite bind_rewrite.
      
      simpl (is_state f_accept).
      
      setoid_rewrite (bind_assoc (is_state (compute_g_pow_yi _ _))).
      
      apply (somewhat_let_substitution _ _ _ _ _ _ _) ; [ admit | ].
      eapply r_bind ; [ apply rreflexivity_rule | intros ].

      eapply rpre_weaken_rule ; [ | admit ].
      
      apply (somewhat_let_substitution _ _ _ _ _ _ _) ; [admit | ].

      set (f_cvp_zkp_random_w _).
      set (f_cvp_zkp_random_r _).
      set (f_cvp_zkp_random_d _).
      set (ret_both _).
      set (f_cvp_xi _).
      set (f_cvp_vote _).

      

      epose AdvantageE_equiv.
      pose hacspec_vs_RUN_interactive.
      
      change (zkp_one_out_of_two b b0 b1 b2 b3 b4) with
        (letb ' b := b in
         letb ' b0 := b0 in
         letb ' b1 := b1 in
           zkp_one_out_of_two b b0 b1 b2 b3 b4).

      set (letb ' _ := _ in _).
      
      rewrite <- (bind_rewrite (is_state b5)).
      
      set (fun _ => _).
      replace (bind _ _).
      
      rewrite bind_assoc.
      
      apply r_nice_swap_rule ; [ admit | admit | ] ;
      apply (somewhat_substitution (f_g_pow b3)) ; [ admit | admit | rewrite bind_rewrite ] ;
      apply r_nice_swap_rule ; [ admit | admit | ].

      eapply r_transR.
      2:{
        eapply r_bind.
        1:{
          rewrite <- (bind_ret (is_state _)).
          apply (somewhat_let_substitution _ _ _ _ _ _ _) ; [ admit | ].
        

          eapply rpre_weaken_rule ; [ | admit ].

          apply (somewhat_let_substitution _ _ _ _ _ _ _).

          
        2:{
          intros.
          eapply rpre_weaken_rule ; [ | admit ].
          eapply rpost_weaken_rule ; [ | admit ].
          eapply rreflexivity_rule.
        
      apply (somewhat_let_substitution _ _ _ _ _ _ _) ; [admit | ].

      set (fun _ => _) at 3.
      replace (bind _ _) with (x ← sample uniform #|'Z_q| ;; y0 (otf x)) by admit.

      ssprove_sync_eq.
      intros.
      subst y0.
      hnf.
      
      apply (somewhat_let_substitution _ _ _ _ _ _ _) ; [admit | ].

      set (fun _ => _) at 3.
      replace (bind _ _) with (x ← sample uniform #|'Z_q| ;; y0 (otf x)) by admit.

      ssprove_sync_eq.
      intros.
      subst y0.
      hnf.

      apply (somewhat_let_substitution _ _ _ _ _ _ _) ; [admit | ].

      set (fun _ => _) at 3.
      replace (bind _ _) with (x ← sample uniform #|'Z_q| ;; y0 (otf x)) by admit.

      ssprove_sync_eq.
      intros.
      subst y0.
      hnf.


      
      
      eapply r_transR.
      2:{
        apply (somewhat_let_substitution _ _ _ _ _ _ _) ; [admit | eapply r_bind ; [ admit | intros ] ].
        eapply rpre_weaken_rule ; [ | admit ].
        assert (a₀ = a₁) by admit.
        subst.
        apply (somewhat_let_substitution _ _ _ _ _ _ _) ; [admit | eapply r_bind ; [ admit | intros ] ].
        eapply rpre_weaken_rule ; [ | admit ].
        assert (a₀ = a₁0) by admit.
        subst.
        apply (somewhat_let_substitution _ _ _ _ _ _ _) ; [admit | eapply r_bind ; [ admit | intros ] ].
        eapply rpre_weaken_rule ; [ | admit ].
        assert (a₀ = a₁1) by admit.
        subst.
        eapply rpost_weaken_rule ; [ | admit ].
        apply rreflexivity_rule.
      }

      set (fun _ => _) at 3.
      replace (bind _ _) with
        (x ← (#assert (MyParam.R (g ^+ FieldToWitness (is_pure b3), is_pure b2, is_pure b2)
                    (FieldToWitness (is_pure b3), is_pure b4, is_pure b2)) ;;
              wr ← sample uniform (2^32) ;;
              dr ← sample uniform (2^32) ;;
              rr ← sample uniform (2^32) ;;
              is_state (zkp_one_out_of_two
                          (ret_both (Hacspec_Lib_Pre.repr _ (Z.of_nat (nat_of_ord wr))))
                          (ret_both (Hacspec_Lib_Pre.repr _ (Z.of_nat (nat_of_ord rr))))
                          (ret_both (Hacspec_Lib_Pre.repr _ (Z.of_nat (nat_of_ord dr))))
                          (ret_both (is_pure b2)) (* (snd (fst (fst b))) *)
                          (ret_both (WitnessToField (FieldToWitness (is_pure b3)))) (* (WitnessToField (fst (fst (snd b)))) *)
                          (ret_both
                             ((is_pure b2 : gT) == ((is_pure b2 : gT) ^+ FieldToWitness (is_pure b3) * g)%g : 'bool)) (* ((snd (fst b) == (snd (fst (fst b)) ^+  (fst (fst (snd b))) * g)) : 'bool) *))) ;; y0 x) by admit.

      pose lookup_op_valid.
      pose (lookup_op RUN_interactive (RUN, ((chProd choiceStatement choiceWitness), choiceTranscript))).
      replace (assertD _ _) with (ret 3).
      
      
      eapply r_transR.
      2:{
        eapply r_bind.
        1:{
          apply r_nice_swap_rule ; [ admit | admit | ].
          eapply rpre_weaken_rule ; [ | admit ].
          eapply rpost_weaken_rule ; [ | admit ].

          epose (or_run_eq (λ '(h₁, h₀), heap_ignore _ (h₀, h₁)) (((g ^+ FieldToWitness (is_pure b3)) , (is_pure b2), (is_pure b2)), (FieldToWitness (is_pure b3) , is_pure b4, (is_pure b2)))).
          unfold ".1", ".2" in r1.

          change HGPA.HacspecGroup.g with g in r1.
          change HGPA.HacspecGroup.OVN_instance.OVN.zkp_one_out_of_two with zkp_one_out_of_two in r1.
          change HGPA.field_equality.WitnessToField with WitnessToField in r1.

          set (assertD _ _) in *.
          eapply r2.
          
          eapply r2.
          
          rewrite WitnessToFieldCancel in r2.
      
      apply (somewhat_let_substitution _ _ _ _ r _ _) ; [admit | ].
      apply (somewhat_let_substitution _ _ _ _ r _ _) ; [admit | ].

      
      2:{ reflexivity.

      replace ()
ite      
      rewrite <- (bind_ret_both (f_cvp_zkp_random_w
                      (solve_lift bind_both (ret_both (f_parameter_cursor (ret_both ctx))) ret_both))).
      set (fun _ => _) at 3.
      replace (bind _ _) with (x ← sample uniform #|gT| ;; y0 (otf x)) by admit.
      subst y0.
      hnf.

      
      apply (@somewhat_substitution _ ((chOption t_OvnContractState)) (compute_g_pow_yi _ _)) ; [ admit | admit | rewrite bind_rewrite ].

      
      set (ret_both _).

      unfold y0.
      apply (somewhat_let_substitution _ _ _ _ r _ _) ; [admit | ].

      
      simpl.

      apply (@somewhat_substitution _ ((chOption t_OvnContractState)) (compute_g_pow_yi _ _)) ; [ admit | admit | rewrite bind_rewrite ].
        
        admit.
        
        
      
      apply r1.
      apply 
      apply somewhat_let_substitution.
      
      assert (forall y r, is_state (letb ' p := y in r p) = (' p ← is_state y ;; r (ret_both p))).
      
      
      replace (is_state (letb ' g_pow_yi
            := compute_g_pow_yi
                 (cast_int (f_cvp_i (solve_lift ret_both (f_parameter_cursor (ret_both ctx)))))
                 (f_g_pow_xis (ret_both state))
            in letb ' g_pow_xi_yi_vi
               := compute_group_element_for_vote
                    (f_cvp_xi (solve_lift ret_both (f_parameter_cursor (ret_both ctx))))
                    (f_cvp_vote (solve_lift ret_both (f_parameter_cursor (ret_both ctx)))) g_pow_yi
               in letb ' zkp_vi
                  := zkp_one_out_of_two
                       (f_cvp_zkp_random_w (solve_lift ret_both (f_parameter_cursor (ret_both ctx))))
                       (f_cvp_zkp_random_r (solve_lift ret_both (f_parameter_cursor (ret_both ctx))))
                       (f_cvp_zkp_random_d (solve_lift ret_both (f_parameter_cursor (ret_both ctx))))
                       g_pow_yi (f_cvp_xi (solve_lift ret_both (f_parameter_cursor (ret_both ctx))))
                       (f_cvp_vote (solve_lift ret_both (f_parameter_cursor (ret_both ctx))))
                  in letb ' cast_vote_state_ret := f_branch (ret_both state)
                     in letb ' cast_vote_state_ret0
                        := Build_t_OvnContractState [cast_vote_state_ret]
                           ( f_g_pow_xi_yi_vis := update_at_usize
                                                    (f_g_pow_xi_yi_vis cast_vote_state_ret)
                                                    (cast_int
                                                       (f_cvp_i
                                                          (solve_lift ret_both
                                                                        (f_parameter_cursor
                                                                         (ret_both ctx)))))
                                                    g_pow_xi_yi_vi)
                        in letb ' cast_vote_state_ret1
                           := Build_t_OvnContractState [cast_vote_state_ret0]
                              ( f_zkp_vis := update_at_usize (f_zkp_vis cast_vote_state_ret0)
                                               (cast_int
                                                  (f_cvp_i
                                                     (solve_lift ret_both
                                                                   (f_parameter_cursor (ret_both ctx)))))
                                               zkp_vi)
                             in ControlFlow_Continue prod_b (f_accept, cast_vote_state_ret1))) with
        (g_pow_yi ← is_state (compute_g_pow_yi
                 (cast_int (f_cvp_i (solve_lift ret_both (f_parameter_cursor (ret_both ctx)))))
                 (f_g_pow_xis (ret_both state))) ;;
         g_pow_xi_yi_vi ←
               compute_group_element_for_vote
                    (f_cvp_xi (solve_lift ret_both (f_parameter_cursor (ret_both ctx))))
                    (f_cvp_vote (solve_lift ret_both (f_parameter_cursor (ret_both ctx)))) g_pow_yi
               ;; letb ' zkp_vi
                  := zkp_one_out_of_two
                       (f_cvp_zkp_random_w (solve_lift ret_both (f_parameter_cursor (ret_both ctx))))
                       (f_cvp_zkp_random_r (solve_lift ret_both (f_parameter_cursor (ret_both ctx))))
                       (f_cvp_zkp_random_d (solve_lift ret_both (f_parameter_cursor (ret_both ctx))))
                       g_pow_yi (f_cvp_xi (solve_lift ret_both (f_parameter_cursor (ret_both ctx))))
                       (f_cvp_vote (solve_lift ret_both (f_parameter_cursor (ret_both ctx))))
                  in letb ' cast_vote_state_ret := f_branch (ret_both state)
                     in letb ' cast_vote_state_ret0
                        := Build_t_OvnContractState [cast_vote_state_ret]
                           ( f_g_pow_xi_yi_vis := update_at_usize
                                                    (f_g_pow_xi_yi_vis cast_vote_state_ret)
                                                    (cast_int
                                                       (f_cvp_i
                                                          (solve_lift ret_both
                                                                        (f_parameter_cursor
                                                                         (ret_both ctx)))))
                                                    g_pow_xi_yi_vi)
                        in letb ' cast_vote_state_ret1
                           := Build_t_OvnContractState [cast_vote_state_ret0]
                              ( f_zkp_vis := update_at_usize (f_zkp_vis cast_vote_state_ret0)
                                               (cast_int
                                                  (f_cvp_i
                                                     (solve_lift ret_both
                                                                   (f_parameter_cursor (ret_both ctx)))))
                                               zkp_vi)
                           in ControlFlow_Continue prod_b (f_accept, cast_vote_state_ret1)).
      
      rewrite bind_assoc ;
        set (is_state _) ;
      simpl (is_state _) ; 
      unfold bind at 2 ; 
      subst y ; 
      hnf ; 
      unfold Hacspec_Lib_Pre.Ok ;
        set (fun _ => _) at 3 ;
        subst r0.

      
      
      rewrite bind_assoc ; 
      apply (@somewhat_substitution _ ((chOption t_OvnContractState)) f_accept) ; [admit | admit | rewrite bind_rewrite] ; 
      rewrite bind_assoc ;
      set (is_state _) ;
      simpl (is_state _) ;
      unfold bind at 2 ;
      subst r0.

      rewrite bind_assoc.
      rewrite bind_rewrite.

      apply (@somewhat_substitution _ ((chOption t_OvnContractState)) (compute_group_element_for_vote _ _ _)) ; [admit | admit | rewrite bind_rewrite].

      
      
      set ((zkp_one_out_of_two
                            (f_cvp_zkp_random_w
                               (solve_lift ret_both (f_parameter_cursor (ret_both ctx))))
                            (f_cvp_zkp_random_r
                               (solve_lift ret_both (f_parameter_cursor (ret_both ctx))))
                            (f_cvp_zkp_random_d
                               (solve_lift ret_both (f_parameter_cursor (ret_both ctx))))
                            (compute_g_pow_yi
                               (cast_int
                                  (f_cvp_i (solve_lift ret_both (f_parameter_cursor (ret_both ctx)))))
                               (f_g_pow_xis (ret_both state)))
                            (f_cvp_xi (solve_lift ret_both (f_parameter_cursor (ret_both ctx))))
                            (f_cvp_vote (solve_lift ret_both (f_parameter_cursor (ret_both ctx)))))).
      set (Build_t_OvnContractState[ _ ] ( f_g_pow_xi_yi_vis := _)).
      set (Build_t_OvnContractState[ _ ] ( f_zkp_vis := _)).
      pattern (f_cvp_zkp_random_w) in b.
      
      replace
        Build_t_OvnContractState [
            Build_t_OvnContractState [f_branch (ret_both state)]
              ( f_g_pow_xi_yi_vis := update_at_usize
                                       (f_g_pow_xi_yi_vis
                                          (f_branch (ret_both state)))
                                       (cast_int
                                          (f_cvp_i
                                             (solve_lift 
                                                ret_both
                                                (f_parameter_cursor
                                                   (ret_both ctx)))))
                                       (compute_group_element_for_vote
                                          (f_cvp_xi
                                             (solve_lift 
                                                ret_both
                                                (f_parameter_cursor
                                                   (ret_both ctx))))
                                          (f_cvp_vote
                                             (solve_lift 
                                                ret_both
                                                (f_parameter_cursor
                                                   (ret_both ctx))))
                                          (compute_g_pow_yi
                                             (cast_int
                                                (f_cvp_i
                                                   (solve_lift 
                                                      ret_both
                                                      (f_parameter_cursor
                                                         (ret_both ctx)))))
                                             (f_g_pow_xis (ret_both state)))))]
          ( f_zkp_vis := update_at_usize
                           (f_zkp_vis
                              Build_t_OvnContractState [f_branch (ret_both state)]
                              ( f_g_pow_xi_yi_vis := update_at_usize
                                                       (f_g_pow_xi_yi_vis (f_branch (ret_both state)))
                                                       (cast_int
                                                          (f_cvp_i
                                                             (solve_lift 
                                                                ret_both
                                                                (f_parameter_cursor (ret_both ctx)))))
                                                       (compute_group_element_for_vote
                                                          (f_cvp_xi
                                                             (solve_lift 
                                                                ret_both
                                                                (f_parameter_cursor (ret_both ctx))))
                                                          (f_cvp_vote
                                                             (solve_lift 
                                                                ret_both
                                                                (f_parameter_cursor (ret_both ctx))))
                                                          (compute_g_pow_yi
                                                             (cast_int
                                                                (f_cvp_i
                                                                   (solve_lift 
                                                                      ret_both
                                                                      (f_parameter_cursor
                                                                         (ret_both ctx)))))
                                                             (f_g_pow_xis (ret_both state))))))
                           (cast_int
                              (f_cvp_i (solve_lift ret_both (f_parameter_cursor (ret_both ctx)))))
                           (zkp_one_out_of_two
                              (f_cvp_zkp_random_w
                                 (solve_lift ret_both (f_parameter_cursor (ret_both ctx))))
                              (f_cvp_zkp_random_r
                                 (solve_lift ret_both (f_parameter_cursor (ret_both ctx))))
                              (f_cvp_zkp_random_d
                                 (solve_lift ret_both (f_parameter_cursor (ret_both ctx))))
                              (compute_g_pow_yi
                                 (cast_int
                                    (f_cvp_i
                                       (solve_lift ret_both (f_parameter_cursor (ret_both ctx)))))
                                 (f_g_pow_xis (ret_both state)))
                              (f_cvp_xi (solve_lift ret_both (f_parameter_cursor (ret_both ctx))))
                              (f_cvp_vote (solve_lift ret_both (f_parameter_cursor (ret_both ctx))))))
      
      rewrite bind_assoc ; 
      apply (@somewhat_substitution _ ((chOption t_OvnContractState)) f_accept) ; [admit | admit | rewrite bind_rewrite] ; 
      rewrite bind_assoc ;
      set (is_state _) ;
      simpl (is_state _) ;
      unfold bind at 2 ;
      subst r0.
      
      
      simpl (bind _ _) at 2.

      
      
      destruct s.
      unfold y.
      hnf.
      
      rewrite bind_assoc.
      apply (@somewhat_substitution _ ((chOption t_OvnContractState)) f_accept) ; [admit | admit | rewrite bind_rewrite].



      
      replace (bind _ _) with (
          bind (letm[choice_typeMonad.result_bind_code _ (* t_ParseError *)] (params : t_CastVoteParam f_Z) := impl__map_err out f_from in
    Result_Ok (letb g_pow_yi := compute_g_pow_yi (cast_int (WS2 := _) (f_cvp_i params)) (f_g_pow_xis (ret_both state)) in
    letb g_pow_xi_yi_vi := compute_group_element_for_vote (f_cvp_xi params) (f_cvp_vote params) g_pow_yi in
    letb zkp_vi := zkp_one_out_of_two (f_cvp_zkp_random_w params) (f_cvp_zkp_random_r params) (f_cvp_zkp_random_d params) g_pow_yi (f_cvp_xi params) (f_cvp_vote params) in
    letb cast_vote_state_ret := f_clone (ret_both state) in
    letb cast_vote_state_ret := Build_t_OvnContractState[cast_vote_state_ret] (f_g_pow_xi_yi_vis := update_at_usize (f_g_pow_xi_yi_vis cast_vote_state_ret) (cast_int (WS2 := _) (f_cvp_i params)) g_pow_xi_yi_vi) in
    letb cast_vote_state_ret := Build_t_OvnContractState[cast_vote_state_ret] (f_zkp_vis := update_at_usize (f_zkp_vis cast_vote_state_ret) (cast_int (WS2 := _) (f_cvp_i params)) zkp_vi) in
    Result_Ok (prod_b (f_accept,cast_vote_state_ret))))


      unfold cast_vote at 1.
      rewrite !bind_assoc; rewrite !bind_rewrite.
      rewrite !bind_assoc; rewrite !bind_rewrite ; fold chElement.
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

      set (y := fun _ => _) at 3.
      replace (bind _ _) with (x ← sample uniform #|gT| ;; y (otf x)) by admit.
      subst y.
      hnf.
      
      apply pkg_rhl.r_const_sample_L ; [admit | intros ].
      rewrite !bind_rewrite.
      rewrite !bind_assoc; rewrite !bind_rewrite.

      set (bind_both _ _).
      pattern (f_cvp_zkp_random_w (solve_lift ret_both (f_parameter_cursor (ret_both s0)))) in b.
      set (fun _ => _) in b.
      subst b.
      epose (both_eq_let_both y (f_cvp_zkp_random_w (solve_lift ret_both (f_parameter_cursor (ret_both s0))))).
      destruct b.

      setoid_rewrite <- H3.
      
      setoid_rewrite <- b.

      pose both_eq_bind.
      rewrite <- (bind_ret_both _ (f_cvp_zkp_random_w (solve_lift ret_both (f_parameter_cursor (ret_both s0))))).
      bind_both
        (f_cvp_zkp_random_w (solve_lift ret_both (f_parameter_cursor (ret_both s0))))
      rewrite let_bind.
      rewrite <- (bind_rewrite (f_cvp_zkp_random_w (solve_lift ret_both (f_parameter_cursor (ret_both s0))))).

      Transparent f_cvp_zkp_random_w.
      unfold f_cvp_zkp_random_w.
      
      rewrite !bind_assoc.


      set (y := fun _ => _) at 4.


      
      apply (@somewhat_substitution _ ((chOption t_OvnContractState)) (compute_group_element_for_vote _ _ _)) ; [admit | admit | rewrite bind_rewrite].
      rewrite !bind_rewrite.

      simpl.
      
      rewrite !bind_assoc; rewrite !bind_rewrite.
      rewrite bind_assoc.

      (* eassert (is_state (zkp_one_out_of_two _ _ _ _ _ _) = match lookup_op OR_ZKP.Sigma.RUN_interactive (OR_ZKP.Sigma.RUN, ((chProd OR_ZKP.MyAlg.choiceStatement OR_ZKP.MyAlg.choiceWitness), OR_ZKP.MyAlg.choiceTranscript)) with Some c => temp ← c (fto (g ^+ FieldToWitness *)
      (*                   (is_pure (f_cvp_xi (solve_lift ret_both (f_parameter_cursor (ret_both s0))))),( *)
      (*            is_pure (compute_g_pow_yi *)
      (*            (cast_int (f_cvp_i (solve_lift ret_both (f_parameter_cursor (ret_both s0))))) *)
      (*            (f_g_pow_xis (ret_both s))) : gT),(_ ^+ _ * _ ^+ _)%g), ( fto ((FieldToWitness (is_pure (f_cvp_xi (solve_lift ret_both (f_parameter_cursor (ret_both s0)))))) : 'Z_q, _, is_pure (compute_g_pow_yi *)
      (*            (cast_int (f_cvp_i (solve_lift ret_both (f_parameter_cursor (ret_both s0))))) *)
      (*            (f_g_pow_xis (ret_both s))) : gT))) ;; _ | None => _ end) by admit. *)
      (* rewrite H2. *)
      
      Check zkp_one_out_of_two.
      epose OR_ZKP.hacspec_vs_RUN_interactive.
      unfold AdvantageE in e.
      apply (@somewhat_substitution _ _ OR_ZKP.hacspec_vs_RUN_interactive).
      
      simpl (lookup_op _ _).
      destruct choice_type_eqP ; [ | subst ; contradiction ].
      destruct choice_type_eqP ; [ | subst ; contradiction ].
      subst.
      rewrite cast_fun_K.

      rewrite !otf_fto.

      rewrite !bind_assoc.
      simpl.
      (* rewrite otf_fto. *)

      rewrite eqxx.
      rewrite eqxx.
      rewrite eqxx.
      
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
