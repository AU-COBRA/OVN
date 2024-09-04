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

  Ltac ssprove_same_head_generic :=
      apply (rsame_head_alt (L := fset0)) ; [ ssprove_valid_code | done | done | intros ? ].

  Ltac ssprove_refl :=
      apply (r_reflexivity_alt (L := fset0)) ; [ ssprove_valid_code | done | done ].

  Ltac ssprove_sym :=
    apply r_nice_swap_rule ; [ easy | | apply p_eq ] ; now intros [] [] ; cbn.

  Ltac trim_is_interface :=
    setoid_rewrite filterm_set ; simpl ; fold chElement ;
    rewrite <- fset1E ;
    rewrite in_fset1 ;
    simpl ;
    rewrite eqxx ;
    rewrite filterm0 ;
    reflexivity.

  Ltac trimmed_package p :=
    match type of p with
    | package ?L ?I ?E =>
        assert (trimmed E p) by now unfold trimmed ; trim_is_interface
    end.

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
    forall I1 I2 a b, Parable a b -> trimmed I1 a -> trimmed I2 b -> trimmed (I1 :|: I2) (par a b).
  Proof.
    intros.
    unfold trimmed.
    unfold trim.
    simpl.
    unfold par.

    rewrite filterm_union.
    1:{
      rewrite <- H0.
      rewrite <- H1.

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

      rewrite H2.
      rewrite H2.
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
    {
      apply parable.
    }
  Qed.

  Lemma trimmed_link :
    forall E a b, trimmed E a -> trimmed E (a ∘ b).
  Proof.
    intros.
    unfold trimmed.
    rewrite <- link_trim_commut.
    rewrite H.
    done.
  Qed.

  Lemma parable_par_l :
    forall a b c, Parable a c -> Parable b c -> Parable (par a b) c.
  Proof.
    clear ; intros.
    unfold Parable.
    rewrite domm_union.
    rewrite fdisjointUl.
    rewrite H H0.
    reflexivity.
  Qed.

  Lemma parable_par_r :
    forall a b c, Parable c a -> Parable c b -> Parable c (par a b).
  Proof.
    clear ; intros.
    unfold Parable.
    rewrite domm_union.
    rewrite fdisjointUr.
    rewrite H H0.
    reflexivity.
  Qed.


  Ltac solve_Parable :=
    match goal with
    | [ |- context [ Parable (trim _ ?a) (trim _ ?b) ] ] =>
        apply parable_trim
        ; try (unfold idents
               ; rewrite <- !fset1E
               ; rewrite !imfset1
               ; now rewrite fdisjoint1s)
    | Ha : trimmed ?Ea ?a ,
        Hb : trimmed ?Eb ?b
      |- context [ Parable ?a ?b ] =>
        rewrite <- Ha ; rewrite <- Hb ; solve_Parable
    | Ha : trimmed ?Ea ?a ,
      Hb : trimmed ?Eb ?b
      |- context [ Parable ?a (?b ∘ ?c) ] =>
        rewrite <- Ha ;
        rewrite <- Hb ;
        erewrite !link_trim_commut ;
        solve_Parable
    | Ha : trimmed ?Ea ?a ,
        Hb : trimmed ?Eb ?b
      |- context [ Parable (?b ∘ ?c) ?a ] =>
        rewrite <- Ha ;
        rewrite <- Hb ;
        erewrite !link_trim_commut ;
        solve_Parable
    | |- context [ Parable ?a (par ?b ?c) ] =>
        apply parable_par_r ; solve_Parable
    | |- context [ Parable (par ?a ?b) ?c ] =>
        apply parable_par_l ; solve_Parable
    end.

  Ltac solve_trimmed :=
    match goal with
    | |- context [ trimmed ?E (par ?a ?b) ] =>
        apply trimmed_par ; [ solve_Parable | solve_trimmed.. ]
    | |- context [ trimmed ?E (?b ∘ ?c) ] =>
        apply trimmed_link ; solve_trimmed
    (* | |- context [ trimmed _ (?b ∘ ?c) ] => *)
    (*     assert (Hb : trimmed _ b) by solve_trimmed ; *)
    (*     rewrite <- Hb ; *)
    (*     rewrite link_trim_commut ; *)
    (*     solve_trimmed *)
    (* | [ |- context [ trimmed _ (par (trim _ ?a) (trim _ ?b ∘ ?c)) ] ] => *)
    (*     rewrite link_trim_commut ; *)
    (*     solve_trimmed *)
    (* | [ |- context [ trimmed _ (par ?a ?b) ] ] => *)
              (*     apply trimmed_par ; solve_Parable *)
    | _ => eassumption || shelve
    end.

  Ltac solve_valid_package :=
    match goal with
    | [ |- context [ ValidPackage ?L ?I ?E (pack ?a) ] ] =>
        apply a
    | [ |- context [ ValidPackage ?L ?I ?E (trim ?T ?a) ] ] =>
        apply valid_trim ; solve_valid_package
    (* | [ |- context [ ValidPackage ?L ?I ?E (?a ∘ ?b) ] ] => *)
    (*     apply valid_link ; solve_valid_package *)
    | [ |- context [ ValidPackage ?L ?I ?E (?a ∘ ?b) ] ] =>
        eapply valid_link_upto ; [ solve_valid_package | solve_valid_package | shelve | shelve ]
    (* | [ |- context [ ValidPackage ?L ?I ?E (par (trim _ ?a) (trim _ ?b)) ] ] => *)
    (*     apply valid_par ; [ *)
    (*       solve_Parable *)
    (*     | solve_valid_package | solve_valid_package ] *)
    | [ |- context [ ValidPackage ?L ?I ?E (par ?a ?b) ] ] =>
        eapply valid_par_upto ; [
          solve_Parable
        | solve_valid_package | solve_valid_package | shelve.. ]
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


  Lemma bobble_sampleC :
    ∀
      {A : ord_choiceType}
      {C : _}
      (o : Op)
      (c : raw_code C)
      (v : raw_code A)
      (f : A -> Arit o -> raw_code C),
      ⊢ ⦃ λ '(h₀, h₁), h₀ = h₁ ⦄
        r ← sample o ;;
        a ← v ;;
        f a r ≈
        c ⦃ Logic.eq ⦄ <->
      ⊢ ⦃ λ '(h₀, h₁), h₀ = h₁ ⦄
        a ← v ;;
        r ← sample o ;;
        f a r ≈
        c ⦃ Logic.eq ⦄.
  Proof.
    intros.
    replace
      (a ← v ;; r ← sample o ;; f a r) with
      ('(a,r) ← (a ← v ;; r ← sample o ;; ret (a, r)) ;; f a r) by now rewrite bind_assoc.

    assert (H_eq : ⊢ ⦃ λ '(h₀, h₁), h₀ = h₁ ⦄
              x ← (a ← v ;;
                   r ← sample o ;;
                   ret (a, r)) ;;
            (let '(a, r) := x in f a r)
              ≈
              r ← sample o ;;
            a ← v ;;
            f a r
              ⦃ Logic.eq ⦄).
    {
      1:{
        eapply r_transR with (c₁ := '(a,r) ← _ ;; f a r).
        2: apply r_bind_feq ; [ apply rsamplerC | intros [] ].
        2: apply rreflexivity_rule.
        rewrite !bind_assoc.
        simpl.
        setoid_rewrite bind_assoc.
        simpl.
        apply rreflexivity_rule.
      }
    }

    split ; intros H ; (eapply r_transR ; [ apply H | clear H ])
                         ; [ | apply r_nice_swap_rule ; [ easy | easy | ] ] ; simpl ; apply H_eq.
  Qed.

  Lemma bobble_sample_uniform_putr :
    ∀
      {C : choiceType}
      {ℓ : Location}
      (o : nat) {Ho : Positive o}
      (c : raw_code C)
      (v : ℓ.π1)
      (f : Arit (uniform o) -> raw_code C),
      (forall (v : Arit (uniform o)), valid_code fset0 fset0 (f v)) ->
      ⊢ ⦃ λ '(h₀, h₁), h₀ = h₁ ⦄
        r ← sample uniform o ;;
        #put ℓ := v ;;
        f r ≈
        c ⦃ Logic.eq ⦄ ->
      ⊢ ⦃ λ '(h₀, h₁), h₀ = h₁ ⦄
        #put ℓ := v ;;
        r ← sample uniform o ;;
        f r ≈
        c ⦃ Logic.eq ⦄.
  Proof.
    intros ? ? ? ? ? ? ? ? H.
    eapply r_transR.
    1: apply H.
    apply better_r_put_lhs.
    apply r_uniform_bij with (f := id) ; [ now apply inv_bij | intros ].
    apply better_r_put_rhs.
    eapply rpost_weaken_rule.
    1:{
      set (pre := set_rhs _ _ _).
      refine (r_reflexivity_alt (L := fset0) pre _ _ _ _).
      1: rewrite <- fset0E ; apply (H0 _).
      all: easy.
    }
    now simpl ; intros [] [] [? [? [[? []] ?]]].
  Qed.

  Definition r_bind_feq_alt :
    forall {A B} (a b : raw_code A) (f g : A -> raw_code B) pre post,
      ⊢ ⦃ pre ⦄ a ≈ b ⦃ pre_to_post pre ⦄
      → (∀ (a₀ : A), ⊢ ⦃ pre ⦄ f a₀ ≈ g a₀ ⦃ post ⦄) →
      ⊢ ⦃ pre ⦄ x ← a ;; f x ≈ x ← b ;; g x ⦃ post ⦄.
  Proof.
    intros.
    eapply r_bind with (mid := pre_to_post pre)
    ; [eapply rpost_weaken_rule ; [ apply H | now intros [] [] ? ]
      | intros ].
    apply rpre_hypothesis_rule ; intros ? ? [] ; eapply rpre_weaken_rule with (pre := pre)
    ; [ subst ; apply H0 | now simpl ; intros ? ? [] ].
  Qed.

  (* Import Schnorr_ZKP. *)
  (* Import OR_ZKP. *)

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

  Definition DL_game :
    loc_GamePair [interface
         #val #[ DL ] : chDLInput → chDLOutput
      ] :=
    λ b,
      if b then {locpackage dl_real } else {locpackage dl_ideal }.

  (* (∀ D, DDH.ϵ_DDH D <= ϵ_DDH) *)
  Definition ϵ_DL := Advantage DL_game.

  (** Schnorr *) (* TODO: move to schnorr file *)
  Notation " 'schnorrInput' " :=
    (f_Z × v_G)
      (in custom pack_type at level 2).

  Notation " 'schnorrOutput' " :=
    (t_SchnorrZKPCommit)
      (in custom pack_type at level 2).

  Definition SCHNORR : nat := 232.

  Program Definition schnorr_real :
    package fset0
      [interface]
      [interface #val #[ SCHNORR ] : schnorrInput → schnorrOutput]
    :=
    [package
       #def #[ SCHNORR ] ('(xi, h) : schnorrInput) : schnorrOutput
       {
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

  Program Definition schnorr_ideal :
    package fset0
      [interface]
      [interface #val #[ SCHNORR ] : schnorrInput → schnorrOutput]
    :=
    [package
       #def #[ SCHNORR ] ('(_, h) : schnorrInput) : schnorrOutput
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
      (* ValidPackage LA [interface #val #[ DL ] : chDLInput → chDLOutput ] A_export A → *)
      (AdvantageE
        (schnorr_real)
        (schnorr_ideal) A = 0)%R.
  Proof.
    intros.
    admit.
  Admitted.

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
         (* #assert OR_ZKP.proof_args.MyParam.R (x,h,y) (FieldToWitness xi, vi, h) ;; *)
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
    (* replace (OR_ZKP.proof_args.MyParam.R _ _) with true by admit. *)
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
         (* #assert OR_ZKP.proof_args.MyParam.R (x,h,y) (FieldToWitness xi, vi, h) ;; *)
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
                WitnessToField d1,WitnessToField r1,WitnessToField d2,WitnessToField r2)
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

  Lemma cds_advantage :
    ∀ (LA : {fset Location}) (A : raw_package),
      (AdvantageE
        (cds_real)
        (cds_ideal) A = 0)%R.
  Proof. admit. Admitted.


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
       ; #val #[ CDS ] : CDSinput → CDSoutput
      ]
      [interface
         #val #[ FULL_PROTOCOL_INTERFACE ] : 'unit → chSingleProtocolTranscript
      ]
    :=
    [package
        #def #[ FULL_PROTOCOL_INTERFACE ] (_ : 'unit) : chSingleProtocolTranscript
        {
          #import {sig #[ DL ] : chDLInput → chDLOutput }
          as dl ;;
          #import {sig #[ SCHNORR ] : schnorrInput → schnorrOutput }
          as schnorr ;;
          #import {sig #[ CDS ] : CDSinput → CDSoutput }
          as CDS ;;
          xi ← sample (uniform #|'Z_q|) ;; let xi := WitnessToField (otf xi) in
          g_pow_xi ← dl xi ;;
          zkp_i ← schnorr (xi, g_pow_xi) ;;
          g_pow_yi ← is_state (compute_g_pow_yi (ret_both (i : int32)) (f_g_pow_xis (ret_both state))) ;;
          g_pow_xy ← dl (WitnessToField (FieldToWitness xi * (inv g_pow_yi)))%R ;;
          vote_i ← ret ((g_pow_xy : gT) * g^+(if vi then 1 else 0)%R)%g ;;
          commit ← is_state (f_hash (t_Group := HOGaFE.GroupAndField.OVN.v_G_t_Group)
             (impl__into_vec
                (unsize
                   (box_new
                      (array_from_list [(ret_both vote_i)]))))) ;;
          cds_i ← CDS ((g_pow_xi, g_pow_yi, g_pow_yi), (xi, vi)) ;;
          ret (((zkp_i, g_pow_xi, commit, (cds_i : t_OrZKPCommit, vote_i))) : (((t_SchnorrZKPCommit × v_G) × v_Z) × (t_OrZKPCommit × v_G))%pack)
        }
    ].
  Solve All Obligations with now intros ; destruct from_uint_size.
  Next Obligation.
    intros.
    fold chElement.
    ssprove_valid.
    1,2: apply valid_scheme ; rewrite <- fset0E ; apply (ChoiceEquality.is_valid_code (both_prog_valid _)).
  Qed.
  Fail Next Obligation.

  (** All steps *)

  Ltac split_advantage O :=
    try apply (AdvantageE_le_0 _ _ _ ) ;
    eapply Order.le_trans ; [ apply Advantage_triangle with (R := O) | ] ;
    replace (AdvantageE _ _ _) with (@GRing.zero R) ; [
        replace (AdvantageE _ _ _) with (@GRing.zero R) ; [ rewrite add0r ; easy | symmetry ] |
        symmetry ] ; revgoals.

  (* Ltac split_advantage_R O := *)
  (*   match goal with *)
  (*   | |- context [ _ = 0%R ] => *)
  (*       apply (AdvantageE_le_0 _ _ _ ) *)
  (*   | _ => idtac *)
  (*   end ; *)
  (*   match goal with *)
  (*   | |- context [ (_ <= ?advantage)%R ] => *)
  (*       eapply Order.le_trans ; [ apply Advantage_triangle with (R := O) | ] ; *)
  (*       replace (AdvantageE _ _ _) with advantage ; [ *)
  (*         replace (AdvantageE _ _ _) with (@GRing.zero R) ; [ rewrite addr0 ; easy | symmetry ] | *)
  (*         symmetry ] ; revgoals *)
  (*   end. *)

  Lemma protocol_dl_real_to_ideal :
    forall state (i : nat) vi,
    ∀ (LA : {fset Location}) (A : raw_package),
      ValidPackage LA [interface #val #[ FULL_PROTOCOL_INTERFACE ] : 'unit → chSingleProtocolTranscript ] A_export A →
      forall (ϵ : _),
        (forall P, ϵ_DL P <= ϵ)%R →
        (AdvantageE
           (full_protocol_interface state i vi ∘ par dl_real (par schnorr_real cds_real))
           (full_protocol_interface state i vi ∘ par dl_ideal (par schnorr_ideal cds_ideal))
           A <= ϵ%R)%R.
  Proof.
    intros.

    eapply Order.le_trans ; [ apply Advantage_triangle with (R := (full_protocol_interface state i vi ∘ (par dl_ideal (par schnorr_real cds_real)))) | ].
    rewrite <- (addr0 ϵ).
    apply Num.Theory.lerD.
    1:{
      unfold_advantageE.
      rewrite (par_commut dl_real).
      rewrite (par_commut dl_ideal).

      trimmed_package (schnorr_real).
      trimmed_package (cds_real).
      trimmed_package (dl_real).
      trimmed_package (dl_ideal).

      unfold_advantageE.
      2: apply (flat_valid_package _ _ _ dl_real _).
      Unshelve.
      all: revgoals.
      all: try (apply fsubsetxx || solve_in_fset) .
      match goal with | |- context [ AdvantageE _ _ ?A ] => specialize (H0 A) end.
      unfold ϵ_DL in H0.
      rewrite Advantage_sym.
      rewrite Advantage_E in H0.
      apply H0.
    }

    split_advantage (full_protocol_interface state i vi ∘ (par dl_ideal (par (schnorr_ideal) cds_real))).
    1:{
      trimmed_package (schnorr_real).
      trimmed_package (schnorr_ideal).
      trimmed_package (cds_real).
      trimmed_package (dl_real).
      trimmed_package (dl_ideal).

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
      Unshelve.
      all: revgoals.
      3: apply fsubsetxx.
      all: try (apply fsubsetxx || solve_in_fset) .

      rewrite !(par_commut _ cds_real).
      unfold_advantageE.
      2: apply (flat_valid_package _ _ _ schnorr_real _).
      apply (schnorr_advantage LA).
    }
    {
      trimmed_package (schnorr_ideal).
      trimmed_package (cds_real).
      trimmed_package (cds_ideal).
      trimmed_package (dl_real).
      trimmed_package (dl_ideal).

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
      Unshelve.
      all: revgoals.
      3: apply fsubsetxx.
      all: try (apply fsubsetxx || solve_in_fset).

      unfold_advantageE.
      2: apply (flat_valid_package _ _ _ cds_real _).
      apply (cds_advantage LA).
    }
  Qed.

  Lemma all_step_advantage :
    forall state (i : nat),
    ∀ (LA : {fset Location}) (A : raw_package),
      ValidPackage LA [interface #val #[ FULL_PROTOCOL_INTERFACE ] : 'unit → chSingleProtocolTranscript ] A_export A →
    forall (ϵ : _),
      (forall P, ϵ_DL P <= ϵ)%R →
      (AdvantageE
        (full_protocol_interface state i true ∘ (par dl_real (par schnorr_real cds_real)))
        (full_protocol_interface state i false ∘ (par dl_real (par schnorr_real cds_real) )) A <= ϵ + ϵ)%R.
  Proof.
    intros.

    (* Close in from the left *)
    eapply Order.le_trans ; [ apply Advantage_triangle with (R := (full_protocol_interface state i true ∘ (par dl_ideal (par schnorr_ideal cds_ideal)))) | ].
    (* rewrite <- (addr0 ϵ). *)
    apply Num.Theory.lerD.
    1: eapply (protocol_dl_real_to_ideal) ; eassumption.

    (* Close in from the right *)
    eapply Order.le_trans ; [ apply Advantage_triangle with (R := (full_protocol_interface state i false ∘ (par dl_ideal (par schnorr_ideal cds_ideal)))) | ].
    rewrite <- (add0r ϵ).
    apply Num.Theory.lerD.
    2: rewrite Advantage_sym ; eapply (protocol_dl_real_to_ideal) ; eassumption.

    replace (AdvantageE _ _ _) with (@GRing.zero R) ; [ easy | symmetry ].
    {
      trimmed_package (dl_ideal).
      rename H0 into trimmed_dl.
      trimmed_package (schnorr_ideal).
      rename H0 into trimmed_schnorr.
      trimmed_package (cds_ideal).
      rename H0 into trimmed_cds.

      
      apply: eq_rel_perf_ind_ignore.
      1:{
        solve_valid_package.
        Unshelve.
        all: revgoals.
        all: (apply fsubsetxx || solve_in_fset || shelve).
      }
      1:{
        solve_valid_package.
        Unshelve.
        all: revgoals.
        all: (apply fsubsetxx || solve_in_fset || shelve).
        Unshelve.
        1:{ rewrite !fset_cons. solve_in_fset. }.
        all: shelve.
      }
      3:{
        apply H.
      }
      1: (apply fsubsetxx || solve_in_fset || shelve).
      2,3: apply fdisjoints0.

      unfold eq_up_to_inv.
      simplify_eq_rel inp_unit.

      repeat choice_type_eqP_handle.
      erewrite !cast_fun_K.
      fold chElement.

      ssprove_code_simpl.
      ssprove_sync=> ?.
      ssprove_sync=> ?.
      ssprove_sync=> ?.
      ssprove_sync=> ?.
      ssprove_same_head_generic.
      erewrite !(code_link_scheme).
      2: ssprove_valid_code.
      ssprove_same_head_generic.

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

      erewrite !(code_link_scheme).
      2,3: ssprove_valid_code.
      ssprove_same_head_generic.
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
         (full_protocol_interface state i vi ∘ (par dl_real (par schnorr_real cds_real)))
         A = 0)%R.
  Proof.
    intros.

    trimmed_package (dl_real).
    rename H0 into trimmed_dl.
    trimmed_package (schnorr_real).
    rename H0 into trimmed_schnorr.
    trimmed_package (cds_real).
    rename H0 into trimmed_cds.

    apply: eq_rel_perf_ind_ignore.
    1: apply real_protocol.
    1:{
      solve_valid_package.
      Unshelve.
      all: revgoals.
      3: instantiate (1 := [interface #val #[SCHNORR] : schnorrInput → schnorrOutput ; #val #[CDS] : CDSinput → CDSoutput]).
      all: (apply fsubsetxx || solve_in_fset || shelve).
    }
    3:{
      apply H.
    }
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

    rewrite H0.
    rewrite H1.
    clear H0 H1.

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

      rewrite H3.
      rewrite H2.
      rewrite H1.
      clear H1 H2 H3.

      
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
    subst r H0.
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
    
    rewrite code_link_bind.
    erewrite !(code_link_scheme).
    2: ssprove_valid_code.

    unfold bind at 1.
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

    rewrite H2.
    rewrite H1.
    rewrite H0.
    clear H0 H1 H2.
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
    apply somewhat_substitutionR.
    set (a0 := (is_pure (compute_g_pow_yi (ret_both i) (f_g_pow_xis (ret_both _))))).
    rewrite bind_rewrite.
    rewrite bind_rewrite.
    (* / ssprove_same_head a0. *)
    
    apply somewhat_let_substitution.
    
    simpl code_link.
    rewrite code_link_bind.
    
    repeat choice_type_eqP_handle.
    erewrite !cast_fun_K.
    fold chElement.

    rewrite !FieldToWitnessCancel.

    replace (g ^+ (otf _ * inv a0)%R) with ((a0 : gT) ^+ otf xi).
    2:{
      rewrite mulrC.
      rewrite trunc_pow.
      rewrite expgM.
      rewrite inv_is_inv.
      reflexivity.
    }
    rewrite bind_rewrite.

    rewrite code_link_bind.

    erewrite !(code_link_scheme).
    2: ssprove_valid_code.

    unfold commit_to at 1.
    set (s := is_pure _).
    set (s0 := (_ * _)%g).
    assert (s = s0) ; subst s s0.
    {
      unfold compute_group_element_for_vote at 1.
      simpl.
      Misc.push_down_sides.
      rewrite <- pow_witness_to_field.
      rewrite <- conversion_is_true.
      destruct vi ; [ rewrite rmorph1 | rewrite rmorph0 ] ; reflexivity.
    }

    rewrite H0 ; clear H0.
    ssprove_same_head_generic.
    unfold let_both at 1.
    unfold let_both at 1.
    rewrite bind_assoc.
    rewrite bind_assoc.
    apply somewhat_substitution.
    rewrite bind_rewrite.
    rewrite bind_assoc.
    apply somewhat_substitution.
    rewrite bind_rewrite.
    simpl.
    apply somewhat_substitution.
    rewrite bind_rewrite.

    repeat choice_type_eqP_handle.
    erewrite !cast_fun_K.
    fold chElement.

    simpl.

    (* Round 3 / cast_vote *)

    unfold cast_vote at 1.

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

        rewrite H3.
        rewrite H2.
        rewrite H1.
        rewrite H0.
        clear H0 H1 H2 H3.

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

    replace (ret _) with (ret (is_pure (ret_both a₀))).
    2:{
      clear.
      repeat set (update_at_usize _ _ _).
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
    unfold b5.
    
    replace (cast_int (ret_both i)) with (ret_both (i : int32)).
    2:{ apply both_eq.
        simpl.
        unfold cast_int at 1, lift1_both at 1, bind_both, bind_raw_both.
        simpl.
        rewrite wrepr_unsigned.
        reflexivity.
    }
    rewrite <- (hacspec_function_guarantees (fun x => array_index (n_seq_array_or_seq x _) _)).

    setoid_rewrite (array_update_eq _ (ret_both _) i real_protocol_obligation_5).
    reflexivity.
    }
    rewrite bind_rewrite.
    rewrite bind_rewrite.

    apply r_ret.
    split ; [ | easy ].


    rewrite pair_equal_spec ; repeat split ; [ rewrite pair_equal_spec ; repeat split ; [ try rewrite pair_equal_spec ; repeat split.. ].. ].
    1:{
      clear.
      repeat set (update_at_usize _ _ _).
      rewrite (hacspec_function_guarantees (fun x => array_index (n_seq_array_or_seq x _) _)).
      rewrite <- (hacspec_function_guarantees f_commit_vis).

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
      rewrite H ; clear H.
      unfold b2.

      rewrite <- (hacspec_function_guarantees (fun x => array_index (n_seq_array_or_seq x _) _)).

      setoid_rewrite (array_update_eq _ (ret_both _) i real_protocol_obligation_3).

      reflexivity.
    }
    {
      unfold compute_group_element_for_vote at 1.
      unfold "*"%g at 1.
      simpl.
      unfold setoid_lower2, F, sg_prod, U.
      simpl.
      subst b.
      subst a0.

      replace (cast_int (ret_both i)) with (ret_both (i : int32)).
      2:{ apply both_eq.
          simpl.
          unfold cast_int at 1, lift1_both at 1, bind_both, bind_raw_both.
          simpl.
          rewrite wrepr_unsigned.
          reflexivity.
      }

      set (f_g_pow_xis _).
      rewrite pow_witness_to_field.
      Misc.push_down_sides.
      replace (is_pure (compute_g_pow_yi _ _)) with (is_pure (compute_g_pow_yi (ret_both i) (ret_both (is_pure (f_g_pow_xis (ret_both state)))))).
      2:{
        subst b.

        clear.
        repeat set (update_at_usize _ _ _).

        eassert (forall state (v : both (nseq_ _ (from_uint_size (is_pure n)))),
                    is_pure (f_g_pow_xis (Build_t_OvnContractState [ state ] ( f_commit_vis := v)))
                    = is_pure (f_g_pow_xis state)).
        {
          clear ; intros.
          unfold f_g_pow_xis at 1.
          unfold Build_t_OvnContractState at 1.
          simpl.
          reflexivity.
        }
        rewrite H ; clear H.

        eassert (forall state (v : both (nseq_ _ (from_uint_size (is_pure n)))),
                    is_pure (f_g_pow_xis (Build_t_OvnContractState [ state ] ( f_round1 := v)))
                    = is_pure (f_g_pow_xis state)).
        {
          clear ; intros.
          unfold f_g_pow_xis at 1.
          unfold Build_t_OvnContractState at 1.
          simpl.
          reflexivity.
        }
        rewrite H ; clear H.

        eassert (forall state (v : both (nseq_ _ (from_uint_size (is_pure n)))),
                    is_pure (f_g_pow_xis (Build_t_OvnContractState [ state ] ( f_zkp_xis := v)))
                    = is_pure (f_g_pow_xis state)).
        {
          clear ; intros.
          unfold f_g_pow_xis at 1.
          unfold Build_t_OvnContractState at 1.
          simpl.
          reflexivity.
        }
        rewrite H ; clear H.

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
        rewrite H ; clear H.

        subst b.
        rewrite <- hacspec_function_guarantees.
        rewrite <- hacspec_function_guarantees.
        rewrite (compute_g_pow_yi_update_eq (f_g_pow_xis (ret_both state)) (ret_both (GaFP.HacspecGroup.g ^+ otf xi)) i).
        reflexivity.
      }
      repeat f_equal.
      rewrite <- conversion_is_true.
      f_equal.
      destruct vi ; [ rewrite rmorph1 | rewrite rmorph0 ] ; done.
    }
  Time Qed. (* 319.394 secs *)

  Lemma real_protocol_is_maximum_balloc_secrecy_hiding :
    forall state (i : nat),
    ∀ (LA : {fset Location}) (A : raw_package),
      ValidPackage LA [interface #val #[ FULL_PROTOCOL_INTERFACE ] : 'unit → chSingleProtocolTranscript ] A_export A →
      forall (ϵ : _),
        (forall P, ϵ_DL P <= ϵ)%R →
        (AdvantageE
           (real_protocol i state true)
           (real_protocol i state false) A <= ϵ + ϵ%R)%R.
  Proof.
    intros.

    (* Close in from the left *)
    eapply Order.le_trans ; [ apply Advantage_triangle with (R := (full_protocol_interface state i true ∘ par dl_real (par schnorr_real cds_real))) | ].

    replace (AdvantageE _ _ _) with (@GRing.zero R) ; [ rewrite add0r | symmetry ] ; revgoals.
    1: eapply (real_to_full_protocol_advantage state i true) ; eassumption.

    rewrite Advantage_sym.

    eapply Order.le_trans ; [ apply Advantage_triangle with (R := (full_protocol_interface state i false ∘ par dl_real (par schnorr_real cds_real))) | ].

    replace (AdvantageE _ _ _) with (@GRing.zero R) ; [ rewrite add0r | symmetry ] ; revgoals.
    1: eapply (real_to_full_protocol_advantage state i false) ; eassumption.

    rewrite Advantage_sym.

    eapply all_step_advantage ; eassumption.
  Qed.

  (*** /Solution *)

End OVN_proof.
