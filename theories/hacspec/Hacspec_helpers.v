Set Warnings "-ambiguous-paths,-notation-overridden,-notation-incompatible-format".
From mathcomp Require Import all_ssreflect fingroup.fingroup ssreflect.
Set Warnings "ambiguous-paths,notation-overridden,notation-incompatible-format".
From SSProve.Relational Require Import OrderEnrichedCategory .
From SSProve.Crypt Require Import choice_type Package Prelude.
From SSProve.Crypt Require Import Axioms ChoiceAsOrd RulesStateProb UniformStateProb.
Import PackageNotation.
From extructures Require Import ord fset.
Set Warnings "-ambiguous-paths".
From mathcomp Require Import word_ssrZ word.
Set Warnings "ambiguous-paths".
(* From Jasmin Require Import word. *)

Set Warnings "-notation-overridden".
From Coq Require Import ZArith.
Set Warnings "notation-overridden".
From Coq Require Import Strings.String.
Import List.ListNotations.
Open Scope list_scope.
Open Scope Z_scope.
Open Scope bool_scope.

From Hacspec Require Import ChoiceEquality.
From Hacspec Require Import LocationUtility.
From Hacspec Require Import Hacspec_Lib_Comparable.
Set Warnings "-notation-incompatible-prefix".
From Hacspec Require Import Hacspec_Lib_Pre.
From Hacspec Require Import Hacspec_Lib.
Set Warnings "notation-incompatible-prefix".

Open Scope hacspec_scope.
Import choice.Choice.Exports.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".
Set Primitive Projections.

Global Obligation Tactic := (* try timeout 8 *) solve_ssprove_obligations.

Lemma valid_both_is_deterministic : forall {A: choice_type} (is_pure : A) (is_state : raw_code A), (valid_both {| is_pure := is_pure ; is_state := is_state |}) -> deterministic is_state.
Proof.
  intros A a_pure a_state a_valid_both ; simpl in *.
  induction a_state.
  + apply deterministic_ret.
  + exfalso. inversion a_valid_both.
  + apply deterministic_get.
    intros.
    apply X.
    * now inversion a_valid_both.
  + apply deterministic_put.
    apply IHa_state.
    * now inversion a_valid_both.
  + exfalso. inversion a_valid_both.
Defined.

Corollary both_deterministic : forall {A: choice_type} (a : both A), deterministic (is_state a).
Proof.
  intros.
  destruct a as [[] [] ?].
  apply (valid_both_is_deterministic is_pure is_state is_valid_both).
Defined.

Definition both_equivalence {A} (a : both A) (b : both A) :=
  is_pure a = is_pure b /\ ⊢ ⦃ true_precond ⦄ is_state a ≈ is_state b ⦃ fun '(a, h₀) '(b, h₁) => (a = b) ⦄.
Arguments both_equivalence {A} a b.
Infix "≈both" := (both_equivalence) (at level 77).

From Coq Require Import FunctionalExtensionality.

Lemma r_swap_post : forall {A B : choiceType} {P} {a b} (Q Q' : postcond A B),
    Q = Q' ->
    ⊢ ⦃ P ⦄ a ≈ b ⦃ Q' ⦄ ->
    ⊢ ⦃ P ⦄ a ≈ b ⦃ Q ⦄.
Proof. now intros ; subst. Qed.

Lemma r_swap_precond : forall {A B : choiceType} {Q : postcond A B} {a b} P P',
    P = P' ->
    ⊢ ⦃ P' ⦄ a ≈ b ⦃ Q ⦄ ->
    ⊢ ⦃ P ⦄ a ≈ b ⦃ Q ⦄.
Proof. now intros ; subst. Qed.

Corollary r_transL_val' :
  forall {A} (c₀ c₀' c₁ : raw_code A),
    deterministic c₀' ->
    deterministic c₀ ->
    deterministic c₁ ->
    ⊢ ⦃ true_precond ⦄ c₀ ≈ c₀' ⦃ fun '(v₀, _) '(v₁, _) => v₀ = v₁ ⦄ ->
    ⊢ ⦃ true_precond ⦄ c₀ ≈ c₁ ⦃ fun '(v₀, _) '(v₁, _) => v₀ = v₁ ⦄ ->
    ⊢ ⦃ true_precond ⦄ c₀' ≈ c₁ ⦃ fun '(v₀, _) '(v₁, _) => v₀ = v₁ ⦄.
Proof.
  intros A.
  pose (r := @r_transL_val A A (True) (@Logic.eq A)).
  now replace (fun '(_, _) => True) with true_precond in r by now apply functional_extensionality ; intros [].
Qed.

Ltac prop_fun_eq :=
  repeat (apply functional_extensionality ; intros []) ; simpl ; rewrite (boolp.propeqP).

Lemma r_nice_swap_rule : forall {A} {P Q} (c₀ c₁ : raw_code A),
    (forall (x y : heap), P (x, y) <-> P (y, x)) ->
    (forall (x y : A * heap), Q x y <-> Q y x) ->
    ⊢ ⦃ P ⦄ c₁ ≈ c₀ ⦃ Q ⦄ ->
    ⊢ ⦃ P ⦄ c₀ ≈ c₁ ⦃ Q ⦄.
Proof.
  intros.
  apply rsymmetry.
  eapply r_swap_precond ; [ prop_fun_eq ; apply H | ].
  eapply r_swap_post ; [ prop_fun_eq ; apply H0 | ].
  apply H1.
Qed.

Lemma r_nice_swap : forall {A} (c₀ c₁ : raw_code A),
    ⊢ ⦃ true_precond ⦄ c₁ ≈ c₀ ⦃ fun '(v₀, _) '(v₁, _) => v₀ = v₁ ⦄ ->
    ⊢ ⦃ true_precond ⦄ c₀ ≈ c₁ ⦃ fun '(a₀, _) '(a₁, _) => a₀ = a₁ ⦄.
Proof. intros ; now apply r_nice_swap_rule. Qed.

Corollary r_transR_val' :
  forall {A} (c₀ c₀' c₁ : raw_code A),
    deterministic c₀' ->
    deterministic c₀ ->
    deterministic c₁ ->
    ⊢ ⦃ true_precond ⦄ c₀' ≈ c₀ ⦃ fun '(v₀, _) '(v₁, _) => v₀ = v₁ ⦄ ->
    ⊢ ⦃ true_precond ⦄ c₁ ≈ c₀ ⦃ fun '(v₀, _) '(v₁, _) => v₀ = v₁ ⦄ ->
    ⊢ ⦃ true_precond ⦄ c₀' ≈ c₁ ⦃ fun '(v₀, _) '(v₁, _) => v₀ = v₁ ⦄.
Proof.
  intros.
  apply r_transL_val' with c₀ ; try assumption ; now apply r_nice_swap.
Qed.

Ltac solve_deterministic :=
  (apply both_deterministic || apply deterministic_ret).

Lemma r_symmetry_both : forall {A : choice_type} (pure : A) (a_state b_state : raw_code A),
    ⊢ ⦃ true_precond ⦄ a_state ≈ b_state ⦃ pre_to_post_ret true_precond pure ⦄ ->
    ⊢ ⦃ true_precond ⦄ b_state ≈ a_state ⦃ pre_to_post_ret true_precond pure ⦄.
Proof.
  intros.
  now apply r_nice_swap_rule ; intros ; unfold pre_to_post_ret.
Qed.

Lemma pre_to_post_implies_eq : forall {A} (a : both A) (b : raw_code A),
    deterministic b ->
    ⊢ ⦃ true_precond ⦄ is_state a ≈ b ⦃ pre_to_post_ret true_precond (is_pure a) ⦄ ->
    ⊢ ⦃ true_precond ⦄ is_state a ≈ b ⦃ fun '(v₀, _) '(v₁, _) => v₀ = v₁ ⦄.
Proof.
  intros.
  assert (deterministic (is_state a)) by solve_deterministic.
  apply det_to_sem with (hd₀ := X0) (hd₁ := X).
  apply sem_to_det with (hd₀ := X0) (hd₁ := X) in H.
  unfold det_jdg in H |- *.
  intros.
  specialize (H s₀ s₁ H0) ; clear -H.
  unfold pre_to_post_ret in H.
  destruct (det_run b s₁).
  destruct (det_run (is_state a) s₀).
  now destruct H as [[] ?].
Qed.

Corollary r_transL_both_eq :
  forall {A : choice_type} (c₀ c₀' c₁ : both A),
    ⊢ ⦃ true_precond ⦄ is_state c₀ ≈ is_state c₀' ⦃ pre_to_post_ret true_precond (is_pure c₀) ⦄ ->
    ⊢ ⦃ true_precond ⦄ is_state c₀ ≈ is_state c₁ ⦃ pre_to_post_ret true_precond (is_pure c₁) ⦄ ->
    ⊢ ⦃ true_precond ⦄ is_state c₀' ≈ is_state c₁ ⦃ pre_to_post_ret true_precond (is_pure c₁) ⦄.
Proof.
  intros A c₀ c₀' c₁.
  assert (deterministic (is_state c₀')) by solve_deterministic.
  assert (deterministic (is_state c₀)) by solve_deterministic.
  assert (deterministic (is_state c₁)) by solve_deterministic.

  pose (r := @r_transL_val A A (True) (fun a b => (a = b /\ b = is_pure c₁))).
  replace (fun '(_, _) => True) with true_precond in r by now prop_fun_eq.
  replace (fun '(_, _) '(_, _) => _ /\ _) with (pre_to_post_ret true_precond (is_pure c₁)) in r by now prop_fun_eq.

  intros.
  eapply r with (c₀ := is_state c₀) ; try assumption.
  apply pre_to_post_implies_eq ; try assumption.
Qed.

Corollary r_transR_both_eq :
  forall {A : choice_type} (c₀ c₀' c₁ : both A),
    ⊢ ⦃ true_precond ⦄ is_state c₀' ≈ is_state c₀ ⦃ pre_to_post_ret true_precond (is_pure c₀) ⦄ ->
    ⊢ ⦃ true_precond ⦄ is_state c₁ ≈ is_state c₀ ⦃ pre_to_post_ret true_precond (is_pure c₁) ⦄ ->
    ⊢ ⦃ true_precond ⦄ is_state c₀' ≈ is_state c₁ ⦃ pre_to_post_ret true_precond (is_pure c₁) ⦄.
Proof.
  intros.
  apply r_transL_both_eq with c₀ ; now apply r_symmetry_both.
Qed.

Corollary r_transL_val_pure :
  forall {A : choice_type} (a : both A) (b : raw_code A),
    deterministic b ->
    ⊢ ⦃ true_precond ⦄ is_state a ≈ b ⦃ fun '(v₀, _) '(v₁, _) => v₀ = v₁ ⦄ <->
      ⊢ ⦃ true_precond ⦄ ret (is_pure a) ≈ b ⦃ fun '(v₀, _) '(v₁, _) => v₀ = v₁ ⦄.
Proof.
  intros.
  pose (r := @r_transL_val A A (True) (fun x y => (x = y))).
  replace (fun '(_, _) => True) with true_precond in r by now prop_fun_eq.
  replace (fun '(_, _) '(_, _) => _ /\ _) with (pre_to_post_ret true_precond (is_pure a)) in r by now prop_fun_eq.

  split.
  - eapply r ; [ | | | apply pre_to_post_implies_eq ; [ | apply p_eq ] |  .. ] ; now (solve_deterministic || assumption) .
  - eapply r with (c₀ := ret (is_pure a)) ; [ | | | apply (pre_to_post_implies_eq (ret_both (is_pure a)) (is_state a)) ; [ | apply r_symmetry_both, (p_eq a) ] | .. ] ; try (solve_deterministic || assumption) .
Qed.

Corollary r_transL_both_pure :
  forall {A : choice_type} (a : both A) (b : raw_code A),
    deterministic b ->
    ⊢ ⦃ true_precond ⦄ is_state a ≈ b ⦃ pre_to_post_ret true_precond (is_pure a) ⦄ <->
      ⊢ ⦃ true_precond ⦄ ret (is_pure a) ≈ b ⦃ pre_to_post_ret true_precond (is_pure a) ⦄.
Proof.
  intros.
  pose (r := @r_transL_val A A (True) (fun x y => (x = y /\ y = is_pure a))).
  replace (fun '(_, _) => True) with true_precond in r by now prop_fun_eq.
  replace (fun '(_, _) '(_, _) => _ /\ _) with (pre_to_post_ret true_precond (is_pure a)) in r by now prop_fun_eq.

  split.
  - eapply r ; [ | | | apply pre_to_post_implies_eq ; [ | apply p_eq ] |  .. ] ; now (solve_deterministic || assumption) .
  - eapply r with (c₀ := ret (is_pure a)) ; [ | | | apply (pre_to_post_implies_eq (ret_both (is_pure a)) (is_state a)) ; [ | apply r_symmetry_both, (p_eq a) ] | .. ] ; try (solve_deterministic || assumption) .
Qed.

Lemma code_reflexivity {A : choice_type} (a : both A) :
  ⊢ ⦃ true_precond ⦄ is_state a ≈ is_state a ⦃ pre_to_post_ret true_precond (is_pure a) ⦄.
Proof.
  assert (deterministic (is_state a)) by solve_deterministic.
  apply r_transL_both_pure ; [ assumption | ].
  apply r_symmetry_both.
  apply (p_eq a).
Qed.

Theorem both_pure {A} (a : both A) (b : both A) :
  is_pure a = is_pure b <-> ⊢ ⦃ true_precond ⦄ is_state a ≈ is_state b ⦃ fun '(a, h₀) '(b, h₁) => (a = b) ⦄.
Proof.
  replace (⊢ ⦃ true_precond ⦄ is_state a ≈ is_state b ⦃ fun '(a, h₀) '(b, h₁) => (a = b) ⦄) with
    (⊢ ⦃ true_precond ⦄ ret (is_pure a) ≈ ret (is_pure b) ⦃ fun '(a, h₀) '(b, h₁) => (a = b) ⦄).
  2:{
    rewrite (boolp.propeqP).
    split ; intros.
    - apply (r_transR_val' (ret (is_pure a)) (is_state a) (is_state b) ) ; try solve_deterministic.
      + apply pre_to_post_implies_eq ; try solve_deterministic. apply (p_eq a).
      + apply r_nice_swap.
        apply (r_transR_val' (ret (is_pure b)) (ret (is_pure a)) (is_state b) ) ; try solve_deterministic.
        * apply H.
        * apply pre_to_post_implies_eq ; try solve_deterministic. apply (p_eq b).
    - apply (r_transL_val' (is_state a) (ret (is_pure a)) (ret (is_pure b)) ) ; try solve_deterministic.
      + apply pre_to_post_implies_eq ; try solve_deterministic. apply (p_eq a).
      + apply (r_transR_val' (is_state b) (is_state a) (ret (is_pure b)) ) ; try solve_deterministic.
        * apply H.
        * apply r_nice_swap.
          apply pre_to_post_implies_eq ; try solve_deterministic.
          apply p_eq.
  }
  split.
  - intros.
    now apply r_ret.
  - intros.
    apply (@sem_to_det _ _ _ _ (ret (is_pure a)) (ret (is_pure b)) (deterministic_ret _) (deterministic_ret _)) in H.
    specialize (H empty_heap empty_heap I).
    unfold pre_to_post_ret in H.
    now simpl in H.
Qed.

Theorem both_pure_eq {A} (a : both A) (b : both A) :
  is_pure a = is_pure b <-> ⊢ ⦃ fun '(a, b) => a = b ⦄ is_state a ≈ is_state b ⦃ Logic.eq ⦄.
Proof.

  replace (⊢ ⦃ fun '(a, b) => a = b ⦄ is_state a ≈ is_state b ⦃ Logic.eq ⦄) with
    (⊢ ⦃ fun '(a, b) => a = b ⦄ ret (is_pure a) ≈ ret (is_pure b) ⦃ Logic.eq ⦄).
  2:{
    rewrite (boolp.propeqP).
    split ; intros.
    -
      intros.
      eapply r_transR.
      2:{
        eapply rpost_weaken_rule.
        1: apply (p_eq _ (fun '(a, b) => a = b)).
        now intros [] [] [[] ?].
      }
      apply r_nice_swap_rule ; [ easy | easy | ].

      eapply r_transR.
      2:{
        eapply rpost_weaken_rule.
        1: apply (p_eq _ (fun '(a, b) => a = b)).
        now intros [] [] [[] ?].
      }
      apply r_nice_swap_rule ; [ easy | easy | ].

      apply H.
    -
      intros.
      eapply r_transL.
      2:{
        eapply rpost_weaken_rule.
        1: apply (p_eq _ (fun '(a, b) => a = b)).
        now intros [] [] [[] ?].
      }

      eapply r_transR.
      1:{
        eapply rpost_weaken_rule.
        1: apply (p_eq _ (fun '(a, b) => a = b)).
        now intros [] [] [[] ?].
      }
      apply r_nice_swap_rule ; [ easy | easy | ].

      apply H.
  }
  split.
  - intros.
    now apply r_ret.
  - intros.
    destruct (is_pure a == is_pure b) eqn:a_eq_b ; [ now apply /eqP | ].
    apply (@sem_to_det _ _ _ _ (ret (is_pure a)) (ret (is_pure b)) (deterministic_ret _) (deterministic_ret _)) in H.
    specialize (H empty_heap empty_heap erefl).
    unfold pre_to_post_ret in H.
    now simpl in H.
Qed.

Corollary both_equivalence_is_pure_eq : forall {A} {a : both A} {b : both A},
    a ≈both b <-> is_pure a = is_pure b.
Proof.
  intros.
  unfold both_equivalence.
  split ; [ easy | split ; [ easy | ] ].
  epose (proj1 (both_pure_eq _ _) H).
  eapply r_transR.
  1:{
    apply r.
  }
  eapply rpost_weaken_rule.
  1:{
    apply better_r.
    refine (r_reflexivity_alt true_precond (is_state a) _ _ _).
    1: rewrite <- !fset0E ; apply (ChoiceEquality.is_valid_code) ; apply a.
    1: easy.
    1: easy.
  }
  now intros [] [] [? _].
Qed.

Lemma both_eq_reflexivity : forall {A : choice_type} (a : both A),
    a ≈both a.
Proof.
  intros.
  split.
  - reflexivity.
  - epose (@r_reflexivity_alt A fset0 true_precond (is_state a)) ; rewrite <- fset0E in r ; specialize (r (is_valid_code (both_prog_valid a)) (ltac:(intros ; inversion H)) (ltac:(intros ; inversion H))) ; simpl in r.
    replace (fun '(_, _) => true_precond _) with true_precond in r by now apply functional_extensionality ; intros [].
    apply (r_swap_post (fun '(a, _) '(b, _) => a = b) ) in r ; [ | now do 2 (apply functional_extensionality ; intros []); rewrite (boolp.propeqP) ] .
    assumption.
Qed.

Lemma both_eq_symmetry : forall {A : choice_type} (a v : both A),
    v ≈both a <-> a ≈both v.
Proof.
  split ; intros.
  1,2: destruct H ; split ; [ now rewrite <- H | apply r_nice_swap ; apply H0 ].
Qed.

Lemma both_eq_trans : forall {A : choice_type} {a} (b : both A) {c},
    a ≈both b -> b ≈both c -> a ≈both c.
Proof.
  intros A a b c [] [].
  split.
  - now transitivity (is_pure b).
  - eapply r_transR_val' ; try solve_deterministic.
    + apply H0.
    + apply r_nice_swap.
      apply H2.
Qed.


Require Import Setoid.
Definition setoid_structure {A : choice_type} : Setoid.Setoid_Theory (both A) both_equivalence :=
  {|
    RelationClasses.Equivalence_Reflexive := both_eq_reflexivity;
    RelationClasses.Equivalence_Symmetric := fun x y Hxy => proj2 (both_eq_symmetry x y) Hxy ;
    RelationClasses.Equivalence_Transitive := fun x y z Hxy Hyz => both_eq_trans y Hxy Hyz ;
  |}.

Add Parametric Relation (A : choice_type) :
  (both A) both_equivalence
    reflexivity proved by both_eq_reflexivity
    symmetry proved by (fun x y => proj2 (both_eq_symmetry x y))
    transitivity  proved by (@both_eq_trans _)
    as both_setoid.

(* Add Parametric Setoid (A : choice_type) : (both A) both_equivalence setoid_structure as both_setoid. *)

Lemma both_eq_bind : forall {A B : choice_type} (f : A -> both B) (a : both A) v,
    a ≈both ret_both v ->
    bind_both a f ≈both (f v).
Proof.
  intros.
  destruct H as [? _].
  unfold both_equivalence;  simpl in *.
  split.
  - easy.
  - match_bind_trans_both.
    subst.
    apply both_eq_reflexivity.
Qed.

Lemma both_eq_let_both : forall {A B : choice_type} (f : both A -> both B) (a : both A),
    (letb x := a in f x) ≈both (f a).
Proof.
  intros. setoid_reflexivity.
Qed.


Lemma ret_both_is_pure_cancel : forall {A} (a : both A),
    ret_both (is_pure a) ≈both a.
Proof.
  intros.
  symmetry.
  unfold bind_both.
  unfold both_equivalence ; simpl.
  split.
  - reflexivity.
  - apply pre_to_post_implies_eq ; [ solve_deterministic | apply p_eq ].
Qed.

Lemma both_eq_solve_lift : forall {A : choice_type} (a : both A),
    (solve_lift a) ≈both a.
Proof.
  intros.
  unfold both_equivalence;  simpl in *.
  split ; now apply both_eq_reflexivity.
Qed.

Ltac pattern_lhs pat :=
  match goal with | |- context [ ?lhs = ?rhs ] => let H_lhs := fresh in set (H_lhs := lhs) ; pattern pat in H_lhs ; subst H_lhs end.

Ltac pattern_lhs_f f pat :=
  match goal with | |- context [ f ?lhs = f ?rhs ] => let H_lhs := fresh in set (H_lhs := lhs) ; pattern pat in H_lhs ; subst H_lhs end.

Ltac pattern_rhs pat :=
  match goal with | |- context [ ?lhs = ?rhs ] => let H_rhs := fresh in set (H_rhs := rhs) ; pattern pat in H_rhs ; subst H_rhs end.

Ltac pattern_rhs_f f pat :=
  match goal with | |- context [ f ?lhs = f ?rhs ] => let H_rhs := fresh in set (H_rhs := rhs) ; pattern pat in H_rhs ; subst H_rhs end.

Lemma hacspec_function_guarantees : forall {A B} (f : both A -> both B) (x : both A),
    is_pure (f x) = is_pure (f (ret_both (is_pure x))).
Proof.
  intros.

  f_equal.
  f_equal.
  f_equal.

  apply both_eq.

  destruct x as [[] [] ?].
  now inversion is_valid_both ; subst.
Qed.

(* Axiom hacspec_function_guarantees : forall {A B} (f : both A -> both B) (x : both A), *)
(*     is_pure (f x) = is_pure (f (ret_both (is_pure x))). *)

Corollary hacspec_function_guarantees2 : forall {A B C} (f : both A -> both B -> both C) (x : both A) (y : both B),
    is_pure (f x y) = is_pure (f (ret_both (is_pure x)) (ret_both (is_pure y))).
Proof.
  intros.
  rewrite hacspec_function_guarantees.
  pattern_lhs_f (is_pure (A := C)) x.
  rewrite (hacspec_function_guarantees (fun _ => _) x).
  reflexivity.
Qed.

Corollary hacspec_function_guarantees3 : forall {A B C D} (f : both A -> both B -> both C -> both D) (x : both A) (y : both B) (z : both C),
    is_pure (f x y z) = is_pure (f (ret_both (is_pure x)) (ret_both (is_pure y)) (ret_both (is_pure z))).
Proof.
  intros.
  rewrite hacspec_function_guarantees2.
  pattern_lhs_f (is_pure (A := D)) x.
  rewrite (hacspec_function_guarantees (fun _ => _) x).
  reflexivity.
Qed.

Corollary both_eq_guarantees : forall {A} (x y : both A),
    x ≈both y <-> ret_both (is_pure x) ≈both ret_both (is_pure y).
Proof.
  intros.
  now do 2 rewrite both_equivalence_is_pure_eq.
Qed.

Theorem both_eq_fun_ext : forall {A B} (f : both A -> both B) (x y : both A),
    x ≈both y -> f x ≈both f y.
Proof.
  intros.
  unfold bind_both.
  unfold both_equivalence ; simpl.
  split ; [ | apply both_pure ].
  1,2: rewrite (hacspec_function_guarantees f x) ; rewrite (hacspec_function_guarantees f y) ; now destruct H.
Qed.

Ltac pattern_in a b :=
  let H_in := fresh in
  set (H_in := b) ; pattern a in H_in ; subst H_in.

Lemma both_eq_fun_ext2 : forall {A B C : choice_type} {a x : both A} {b y : both B} {f : both A -> both B -> both C},
    a ≈both x ->
    b ≈both y ->
    f a b ≈both f x y.
Proof.
  intros.
  eapply (both_eq_trans) ; [ apply both_eq_fun_ext, H0 | ].
  eapply (both_eq_trans) ; [ apply (both_eq_fun_ext (fun x => f x y)), H | ].
  apply both_eq_solve_lift.
Qed.

Corollary both_eq_lift2_both : forall {A B C : choice_type} {a : both A} {va : A} {b : both B} {vb : B} {f : A -> B -> C},
    a ≈both (ret_both va) ->
    b ≈both (ret_both vb) ->
    (lift2_both f a b) ≈both ret_both (f va vb).
Proof.
  intros.
  eapply both_eq_trans ; [ eapply (both_eq_fun_ext2 H H0) | ].
  setoid_rewrite lift2_both_equation_1  ; rewrite !bind_ret_both.
  apply both_eq_solve_lift.
Qed.

Lemma bind_both_eta : forall {A B} (f : both A -> both B) (x : both A),
    bind_both x (fun x => f (ret_both x)) ≈both f x.
Proof.
  intros.
  symmetry.
  unfold bind_both.
  unfold both_equivalence ; simpl.
  split.
  - now rewrite hacspec_function_guarantees.
  - apply r_nice_swap.
    match_bind_trans_both.
    apply both_pure.
    now rewrite <- hacspec_function_guarantees.
Qed.

Lemma both_eq_andb_true : forall (a b : both 'bool),
    a ≈both ret_both (true : 'bool) ->
    b ≈both ret_both (true : 'bool) ->
    (andb a b) ≈both ret_both (true : 'bool).
Proof.
  intros.
  setoid_rewrite both_eq_lift2_both ; [ | easy ..].
  reflexivity.
Qed.

Lemma both_eq_andb_false : forall (a b : both 'bool),
    a ≈both ret_both (false : 'bool) \/ b ≈both ret_both (false : 'bool) ->
    (andb a b) ≈both ret_both (false : 'bool).
Proof.
  now intros ? ? [] ;
    eapply (both_eq_trans) ; [
      refine (both_eq_lift2_both (vb := (is_pure b)) H _) ; rewrite (ret_both_is_pure_cancel _)
    | simpl
    | refine (both_eq_lift2_both (va := (is_pure a)) _ H) ; rewrite (ret_both_is_pure_cancel _)
    | simpl ; rewrite Bool.andb_false_r ].
Qed.

Lemma both_eq_eqb_true : forall {A : choice_type} `{t_Eq A} (a b : both A), a ≈both b <-> a =.? b ≈both ret_both (true : 'bool).
Proof.
  split ; intros [].
  - unfold eqb.
    rewrite (both_eq_lift2_both (va := is_pure a) (vb := is_pure b)).
    2, 3: now rewrite ret_both_is_pure_cancel.
    now rewrite H0 eqb_refl.
  - apply both_equivalence_is_pure_eq.
    now apply eqb_leibniz.
Qed.

Fixpoint both_list {A} (l : list (both A)) : both (chList A) :=
  match l with
  | [] => ret_both (nil : chList A)
  | (x :: xs) =>
      bind_both x (fun x =>
                     bind_both (both_list xs) (fun xs =>
                                                 ret_both (x :: xs : chList A)))
  end.

Lemma array_from_list_helper_base :
  forall {A} (x y : both A) k,
    x ≈both y ->
    array_from_list_helper x [] k ≈both array_from_list_helper y [] k.
Proof.
  intros.
  now apply (both_eq_fun_ext (fun x => array_from_list_helper x [] k)).
Qed.

Lemma array_from_list_helper_eq_succ :
  forall {A} k (a b x y : both A) (xs ys : list (both A)),
    Datatypes.length xs = Datatypes.length ys ->
    a ≈both b ->
    array_from_list_helper x xs k ≈both array_from_list_helper y ys k ->
    array_from_list_helper a (x :: xs) k ≈both array_from_list_helper b (y :: ys) k.
Proof.
  intros.

  rewrite !array_from_list_helper_equation_2.

  rewrite (both_eq_fun_ext (fun x => bind_both x _) _ _ H0).
  rewrite !(both_eq_bind _ _ (is_pure b)) ; [ | now rewrite ret_both_is_pure_cancel..].
  rewrite (both_eq_fun_ext (fun x => bind_both x _) _ _ H1).
  rewrite !(both_eq_bind _ _ (is_pure (array_from_list_helper y ys k))) ; [ | now rewrite ret_both_is_pure_cancel..].
  simpl.
  rewrite H.
  reflexivity.
Qed.

Lemma array_from_list_helper_eq :
  forall {A} k (x y : both A) (xs ys : list (both A)),
    Datatypes.length xs = Datatypes.length ys ->
    x ≈both y ->
    List.Forall (fun '(x, y) => x ≈both y) (zip xs ys) ->
    array_from_list_helper x xs k ≈both array_from_list_helper y ys k.
Proof.
  intros.
  generalize dependent ys.
  generalize dependent x.
  generalize dependent y.
  induction xs, ys ; intros ; try discriminate.
  - now apply (both_eq_fun_ext (fun x => array_from_list_helper x [] k)).
  - inversion H.
    apply array_from_list_helper_eq_succ ; try assumption.
    inversion H1 ; subst.
    apply IHxs ; try assumption.
Qed.

Lemma both_eq_array_from_list : forall {A} (l : list (both A)),
    array_from_list l ≈both
      match l as k return both (nseq_ A (Datatypes.length k)) with
        [] => solve_lift (ret_both (tt : nseq_ A 0))
      | (x :: xs) => array_from_list_helper (ret_both (is_pure x)) (List.map (fun x => ret_both (is_pure (both_prog x))) xs) (Datatypes.length xs)
      end.
Proof.
  intros.
  destruct l.
  - apply both_eq_reflexivity.
  - rewrite array_from_list_equation_1.
    apply array_from_list_helper_eq.
    + now rewrite List.map_length.
    + now rewrite ret_both_is_pure_cancel.
    + induction l.
      * apply List.Forall_nil.
      * apply List.Forall_cons.
        -- now rewrite ret_both_is_pure_cancel.
        -- apply IHl.
Qed.

Module Misc.

  Lemma hasChoice_surjective : forall {A B : Type},
    forall {f : A -> B} {f_inv : B -> A} `(η : cancel f_inv f),
      hasChoice.axioms_ A ->
      hasChoice.axioms_ B.
  Proof.
    intros A B f f_inv η [].
    refine ({| hasChoice.find_subdef := (fun P n => match find_subdef (fun x => P (f x)) n with
                                                    | Some x => Some (f x)
                                                    | None => None
                                                    end) |}).
    - intros.
      destruct (find_subdef (fun x => P (f x)) n) eqn:Heq.
      + inversion H.
        subst.
        apply (choice_correct_subdef (fun x => P (f x)) n a Heq).
      + discriminate H.
    - intros.
      destruct (choice_complete_subdef (fun x => P (f x)) (match H with ex_intro _ x H_P => ex_intro _ (f_inv x) (eq_ind_r P H_P (η x)) end )).
      exists x.
      now destruct (find_subdef _ _).
    - intros P Q H_eq n.
      now rewrite (choice_extensional_subdef (fun x => P (f x)) (fun x => Q (f x)) (fun x => H_eq (f x)) n).
  Qed.

  Lemma Choice_isCountable_surjective : forall {A B},
    forall {f : A -> B} {f_inv : B -> A} `(η : cancel f_inv f),
      Choice_isCountable.axioms_ A ->
      Choice_isCountable.axioms_ B.
  Proof.
    intros A B f f_inv η [].
    refine {|
        Choice_isCountable.pickle := fun x => pickle (f_inv x);
        Choice_isCountable.unpickle := fun x => Option.map f (unpickle x);
        Choice_isCountable.pickleK := _
      |}.
    intros x.
    rewrite (pickleK (f_inv x)).
    simpl.
    now rewrite η.
  Qed.

  Lemma equality_surjective : forall {A B},
    forall {f : A -> B} {f_inv : B -> A} `(η : cancel f_inv f),
      hasDecEq.axioms_ A ->
      hasDecEq.axioms_ B.
  Proof.
    intros A B f f_inv η H_eq.
    assert (@injective (Equality.sort (@Equality.Pack A (@Equality.Class A H_eq))) _ f_inv) by easy.
    apply (eqtype_inj_type__canonical__eqtype_Equality H).
  Qed.

  Lemma bijection_is_adjoint : forall {A B : eqType},
    forall (f : A -> B) (f_inv : B -> A),
      (forall (x : B), f (f_inv x) == x) /\ (forall x, f_inv (f x) == x) <-> forall x y, (f y == x) = (y == f_inv x).
  Proof.
    intros.
    split.
    - intros [] x y.
      specialize (H x).
      specialize (H0 y).
      apply (ssrbool.elimT eqP) in H.
      apply (ssrbool.elimT eqP) in H0.
      apply Bool.eq_iff_eq_true.
      now split ; intros ; apply (ssrbool.elimT eqP) in H1 ; apply (ssrbool.introT eqP).
    - intros.
      split ; [ intros x ; set (y := f_inv x) |
                intros y ; set (x := f y) ; rewrite eq_sym ; symmetry in H ] ;
        specialize (H x y) ;
        now rewrite H.
  Qed.

  Lemma isFinite_bijective : forall {A B},
    forall {f : A -> B} {f_inv : B -> A} `(η : cancel f_inv f) `(β : cancel f f_inv),
    forall (H_eq : Equality.mixin_of A),
      isFinite.axioms_ A H_eq ->
      isFinite.axioms_ B (equality_surjective η H_eq).
  Proof.
    intros A B f f_inv η β H_eq [].

    pose (eqA := @Equality.Pack A (@Equality.Class A H_eq)).
    pose (eqB := @Equality.Pack B (@Equality.Class B (@equality_surjective A B f f_inv η H_eq))).

    refine {|
        isFinite.enum_subdef := [ seq f i | i <- enum_subdef ];
        isFinite.enumP_subdef := _;
      |}.

    assert (H : injective (aT := Equality.sort eqA) (rT := Equality.sort eqB) f) by easy ; epose proof (H_inj := eqtype.inj_eq H) ; simpl in H_inj ; clear H.

    assert (H : injective (aT := Equality.sort eqB) (rT := Equality.sort eqA) f_inv) by easy ; epose proof (H_inv_inj := eqtype.inj_eq H) ; simpl in H_inv_inj ; clear H.

    intros x ; simpl in x.
    rewrite count_map.
    rewrite <- (enumP_subdef (f_inv x)).
    clear -H_inj β.
    induction enum_subdef as [ | y ] ; [ reflexivity | ] ; simpl in *.
    rewrite (IHenum_subdef).
    f_equal.
    f_equal.
    apply (proj1 (bijection_is_adjoint (A := eqA) (B := eqB) f f_inv)).
    now split ; intros ; [ rewrite η | rewrite β ].
  Qed.

  Definition finite_bijective : forall {A B},
    forall (f : A -> B) (f_inv : B -> A) `(η : cancel f_inv f) `(β : cancel f f_inv),
      Finite.axioms_ A ->
      Finite.axioms_ B.
  Proof.
    intros A B f f_inv η β H.
    refine {|
        Finite.choice_hasChoice_mixin := hasChoice_surjective η H ;
        Finite.choice_Choice_isCountable_mixin := Choice_isCountable_surjective η H;
        Finite.fintype_isFinite_mixin := isFinite_bijective η β H H
      |}.
  Qed.

  Lemma is_pure_cancel_ret_both : forall {A : choice_type}, cancel (@ret_both A) (@is_pure A).
  Proof. easy. Qed.

  Definition finite_to_word {n} (x : 'I_(Z.to_nat (modulus n)).-1.+1) : n.-word :=
    mkword _ (Z.of_nat (nat_of_ord x)).

  Definition word_to_finite {n} (x : n.-word) : 'I_((Z.to_nat (modulus n)).-1.+1) := inord (Z.to_nat (toword x)).

  Lemma finite_word_cancel : forall {n}, cancel word_to_finite (finite_to_word (n := n)).
  Proof.
    intros.
    unfold word_to_finite, finite_to_word.
    intros x ; clear.
    rewrite inordK.
    - rewrite Z2Nat.id.
      + now rewrite ureprK.
      + now destruct x as [[] ?].
    - destruct x.
      simpl.
      apply (ssrbool.elimT andP) in i as [].
      apply Z.leb_le in H.
      apply Z.ltb_lt in H0.
      apply (ssrbool.introT (jasmin_util.ZNltP _ _)).
      rewrite Nat.succ_pred.
      + now rewrite !Z2Nat.id.
      + unfold modulus.
        unfold two_power_nat.
        easy.
  Qed.

  Lemma word_finite_cancel : forall {n}, cancel (finite_to_word (n := n)) word_to_finite.
  Proof.
    intros.
    unfold finite_to_word, word_to_finite.
    intros x.

    destruct n.
    {
      simpl in x |- *.
      rewrite Z.mod_1_r.
      unfold Z.to_nat.
      destruct x as [[]].
      + unfold inord, insubd, odflt, oapp, insub.
        destruct idP ; now apply ord_ext.
      + discriminate i.
    }

    rewrite mkword_val_small.
    2:{
      destruct x ; simpl.
      rewrite <- modulusE.
      rewrite Nat.succ_pred in i. 2: now unfold modulus, two_power_nat .
      apply (ssrbool.introT andP) ; split ; [ apply Z.leb_le | apply Z.ltb_lt ].
      - eapply (ssrbool.elimT (isword_ofnatZP _ _)).
        apply (ltn_expl m).
        easy.
      - eapply Z.lt_le_trans ; [ apply (ssrbool.elimT (jasmin_util.ZNltP _ _) i) | ].
        clear.
        rewrite !Z2Nat.id. 2: easy.
        unfold modulus.
        now rewrite two_power_nat_equiv.
    }
    rewrite Nat2Z.id.
    now rewrite inord_val.
  Qed.

  (* A slightly more general version where we don't fix the precondition *)
  Theorem rsame_head_cmd_alt :
    forall {A B C : ord_choiceType} {f₀ : A -> raw_code B} {f₁ : A -> raw_code C}
           (m : command A) pre (post : postcond B C),
      ⊢ ⦃ pre ⦄
        x ← cmd m ;; ret x ≈ x ← cmd m ;; ret x
                                            ⦃ fun '(a₀, s₀) '(a₁, s₁) => pre (s₀, s₁) /\ a₀ = a₁ ⦄ ->
      (forall a, ⊢ ⦃ pre ⦄ f₀ a ≈ f₁ a ⦃ post ⦄) ->
      ⊢ ⦃ pre ⦄ x ← cmd m ;; f₀ x ≈ x ← cmd m ;; f₁ x ⦃ post ⦄.
  Proof.
    intros A B C f₀ f₁ m pre post hm hf.
    eapply from_sem_jdg. rewrite !repr_cmd_bind.
    eapply (bind_rule_pp (repr_cmd m) (repr_cmd m)).
    - eapply to_sem_jdg in hm. rewrite !repr_cmd_bind in hm.
      rewrite bindrFree_ret in hm. eauto.
    - intros a₀ a₁. eapply to_sem_jdg.
      eapply rpre_hypothesis_rule.
      intros s₀ s₁ [h e]. subst.
      eapply rpre_weaken_rule. 1: eapply hf.
      simpl. intros ? ? [? ?]. subst. auto.
  Qed.

  (* One-sided sampling rule. *)
  (* Removes the need for intermediate games in some cases. *)
  Lemma r_const_sample_L :
    forall {A B : choiceType} (op : Op) c₀ c₁ (pre : precond) (post : postcond A B),
      LosslessOp op ->
      (forall x, ⊢ ⦃ pre ⦄ c₀ x ≈ c₁ ⦃ post ⦄) ->
      ⊢ ⦃ pre ⦄ x ← sample op ;; c₀ x ≈ c₁ ⦃ post ⦄.
  Proof.
    intros A B op c₀ c₁ pre post hop h.
    eapply r_transR with (x ← sample op ;; (fun _ => c₁) x).
    - apply r_dead_sample_L. 1: auto.
      apply rreflexivity_rule.
    - apply (rsame_head_cmd_alt (cmd_sample op)).
      + eapply rpre_weaken_rule. 1: eapply cmd_sample_preserve_pre.
        auto.
      + apply h.
  Qed.

  Lemma r_const_sample_R :
    forall {A B : choiceType} (op : Op) c₀ c₁ (pre : precond) (post : postcond A B),
      LosslessOp op ->
      (forall x, ⊢ ⦃ pre ⦄ c₀ ≈ c₁ x ⦃ post ⦄) ->
      ⊢ ⦃ pre ⦄ c₀ ≈ x ← sample op ;; c₁ x ⦃ post ⦄.
  Proof.
    intros A B op c₀ c₁ pre post hop h.
    eapply r_transL with (x ← sample op ;; (fun _ => c₀) x).
    - apply r_dead_sample_L. 1: auto.
      apply rreflexivity_rule.
    - apply (rsame_head_cmd_alt (cmd_sample op)).
      + eapply rpre_weaken_rule. 1: eapply cmd_sample_preserve_pre.
        auto.
      + apply h.
  Qed.

  Theorem forget_precond {A B} (x : raw_code A) (y : raw_code B) P Q :
    ⊢ ⦃ true_precond ⦄ x ≈ y ⦃ Q ⦄ ->
    ⊢ ⦃ P ⦄ x ≈ y ⦃ Q ⦄.
  Proof.
    intros.
    now apply (rpre_weaken_rule _ _ _ H).
  Qed.

  Theorem rpre_hypothesis_rule' :
    forall {A₀ A₁ : _} {p₀ : raw_code A₀} {p₁ : raw_code A₁}
           (pre : precond) (post : postcond A₀ A₁),
      (forall s₀ s₁,
          pre (s₀, s₁) -> ⊢ ⦃ fun '(s₀', s₁') => s₀' = s₀ /\ s₁' = s₁ ⦄ p₀ ≈ p₁ ⦃ post ⦄
      ) ->
      ⊢ ⦃ pre ⦄ p₀ ≈ p₁ ⦃ post ⦄.
  Proof.
    intros A₀ A₁ p₀ p₁ pre post h.
    eapply rpre_hypothesis_rule.
    intros s0 s1 H. now eapply rpre_weaken_rule.
  Qed.

  Lemma r_eq_symmetry : forall {A B} {P Q} (c₀ : raw_code A) (c₁ : raw_code B) (f : A -> B),
      (forall (x y : heap), P (x, y) <-> P (y, x)) ->
      (forall (x : A) (y : B), Q (f x) y <-> Q y (f x)) ->
      ⊢ ⦃ P ⦄ c₁ ≈ c₀ ⦃ fun '(a, _) '(b, _) => Q a (f b) ⦄ ->
      ⊢ ⦃ P ⦄ c₀ ≈ c₁ ⦃ fun '(a, _) '(b, _) => Q (f a) b ⦄.
  Proof.
    intros.
    apply rsymmetry.
    eapply r_swap_precond ; [ prop_fun_eq ; apply H | ].
    eapply r_swap_post with (Q' := fun '(a, _) '(b, _) => Q a (f b)); [ prop_fun_eq ; apply H0 | ].
    apply H1.
  Qed.

  Theorem r_transR_both :
    forall {A B : _} {x : raw_code A} {y z : both B}
           (pre : precond) (post : postcond A B),
      y ≈both z ->
      ⊢ ⦃ pre ⦄ x ≈ is_state z ⦃ post ⦄ ->
      ⊢ ⦃ pre ⦄ x ≈ is_state y ⦃ post ⦄.
  Proof.
    intros A B x y z pre post [] H_xz.
    eapply r_transR.
    2:{
      apply H_xz.
    }
    destruct y as [[] []] , z as [[] []] ;  simpl in *.
    inversion is_valid_both.
    inversion is_valid_both0.
    now apply r_ret.
  Qed.

  Corollary make_pure :
    forall {A B : _} {x : raw_code A} {y : both B}
           (pre : precond) (post : postcond A B),
      ⊢ ⦃ pre ⦄ x ≈ ret (is_pure y) ⦃ post ⦄ ->
      ⊢ ⦃ pre ⦄ x ≈ is_state y ⦃ post ⦄.
  Proof.
    intros.
    eapply r_transR_both.
    + now rewrite <- ret_both_is_pure_cancel.
    + simpl.
      apply H.
  Qed.

  Lemma prod_both_pure_eta_3 : forall {A B C} (a : both A) (b : both B) (c : both C),
      ((is_pure (both_prog a) : A,
           is_pure (both_prog b) : B,
             is_pure (both_prog c) : C)) =
        is_pure (both_prog (prod_b( a , b, c ))).
  Proof. reflexivity. Qed.


  Ltac pattern_lhs_approx :=
    match goal with | |- context [ ⊢ ⦃ _ ⦄ ?lhs ≈ ?rhs ⦃ _ ⦄ ] => let H_lhs := fresh in set (H_lhs := lhs) end.

  Ltac pattern_lhs_approx_pat pat :=
    match goal with | |- context [ ⊢ ⦃ _ ⦄ ?lhs ≈ ?rhs ⦃ _ ⦄ ] => let H_lhs := fresh in set (H_lhs := lhs) ; pattern pat in H_lhs ; subst H_lhs end.

  Ltac pattern_lhs_both_pat pat :=
    match goal with | |- context [ ?lhs ≈both ?rhs ] => let H_lhs := fresh in set (H_lhs := lhs) ; pattern pat in H_lhs ; subst H_lhs end.

  Ltac pattern_rhs_approx :=
    match goal with | |- context [ ⊢ ⦃ _ ⦄ ?lhs ≈ ?rhs ⦃ _ ⦄ ] => let H_rhs := fresh in set (H_rhs := rhs) end.

  Ltac pattern_rhs_approx_pat pat :=
    match goal with | |- context [ ⊢ ⦃ _ ⦄ ?lhs ≈ ?rhs ⦃ _ ⦄ ] => let H_rhs := fresh in set (H_rhs := rhs) ; pattern pat in H_rhs ; subst H_rhs end.

  Ltac pattern_rhs_both_pat pat :=
    match goal with | |- context [ ?lhs ≈both ?rhs ] => let H_rhs := fresh in set (H_rhs := rhs) ; pattern pat in H_rhs ; subst H_rhs end.

  Lemma both_eta : forall {A : choice_type} (a : both A), a =
                                                            {|
                                                              both_prog := {| is_pure := is_pure a ; is_state := is_state a |};
                                                              both_prog_valid := ValidBoth_eta (both_prog_valid a)
                                                            ;
                                                              p_eq := p_eq a;
                                                            |}.
  Proof. now intros ? [[] [] ?]. Qed.

  Lemma valid_both_ext : forall {A : choice_type} {a b : both A},
      a ≈both b ->
      ValidBoth a = ValidBoth b.
  Proof.
    intros ? [[a_pure a_state] [a_code a_both] a_eq] [[b_pure b_state] [b_code b_both] b_eq] ?.
    inversion H ; simpl in *.
    subst.
    rewrite boolp.propeqE.
    split ; intros ; now refine {|
                           ChoiceEquality.is_valid_code := _;
                           is_valid_both := _
                         |}.
  Qed.

  Lemma unfold_both : (forall {A B : choice_type} (f : both A -> both B) (a : both A),
                          f a ≈both
                            {|
                              both_prog :=
                                {|
                                  is_pure := is_pure (f (ret_both (is_pure a)));
                                  is_state := x ← ret (is_pure a) ;;
                                              is_state (f (ret_both x))
                                |};
                              both_prog_valid := ValidBoth_eta (both_prog_valid (f (ret_both (is_pure a))));
                              p_eq := p_eq (f (ret_both (is_pure a)))
                            |}).
  Proof.
    intros.
    setoid_rewrite <- both_eta.
    apply both_eq_fun_ext.
    now rewrite ret_both_is_pure_cancel.
  Qed.

  Lemma prod_both_pure_eta_11 : forall {A B C D E F G H I J K} (a : both A) (b : both B) (c : both C) (d : both D) (e : both E) (f : both F) (g : both G) (h : both H) (i : both I) (j : both J) (k : both K),
      ((is_pure (both_prog a) : A,
           is_pure (both_prog b) : B,
             is_pure (both_prog c) : C,
               is_pure (both_prog d) : D,
                 is_pure (both_prog e) : E,
                   is_pure (both_prog f) : F,
                     is_pure (both_prog g) : G,
                       is_pure (both_prog h) : H,
                         is_pure (both_prog i) : I,
                           is_pure (both_prog j) : J,
                             is_pure (both_prog k) : K)) =
        is_pure (both_prog (prod_b( a , b, c, d, e, f, g, h, i, j, k ))).
  Proof. reflexivity. Qed.

  Ltac get_both_sides H_lhs H_rhs :=
    match goal with
    | [ |- context [?lhs ≈both ?rhs ] ] =>
        set (H_lhs := lhs) at 1 ;
        set (H_rhs := rhs) at 1
    | [ |- context [?lhs = ?rhs ] ] =>
        set (H_lhs := lhs) at 1 ;
        set (H_rhs := rhs) at 1
    end.

  Ltac apply_to_pure_sides H H_lhs H_rhs :=
    match goal with
    | [ |- context [ _ ≈both _ ] ] =>
        rewrite both_equivalence_is_pure_eq ;
        get_both_sides H_lhs H_rhs ;
        H ;
        rewrite <- both_equivalence_is_pure_eq
    | [ |- context [ _ = _ ] ] =>
        get_both_sides H_lhs H_rhs ;
        H
    end.

  Ltac push_down :=
    match goal with
    | H : _ |- _ => simpl in H
    end ;
    match goal with
    | H := is_pure (both_prog (?f (ret_both (is_pure (both_prog ?a))) (ret_both (is_pure (both_prog ?b))))) : _ |- _  =>
             subst H ;
             set (is_pure a) ;
             push_down ;
             set (is_pure b) ;
             push_down
        | H := is_pure (both_prog (?f ?a ?b)) |- _  =>
                 subst H ;
                 rewrite (hacspec_function_guarantees2 f a b) ;
                 set (is_pure a) ;
                 push_down ;
                 set (is_pure b) ;
                 push_down
            | H := is_pure (both_prog (?f (ret_both (is_pure (both_prog ?a))))) : _ |- _  =>
                     subst H ;
                     set (is_pure a) ;
                     push_down
                | H := is_pure (both_prog (?f ?a)) : _ |- _  =>
                         subst H ;
                         rewrite (hacspec_function_guarantees f a) ;
                         set (is_pure a) ;
                         push_down
                    | H : _ |- _ => subst H
    end ; simpl.

  Ltac push_down_sides :=
    let H_lhs := fresh in
    let H_rhs := fresh in
    get_both_sides H_lhs H_rhs ; subst H_rhs ;
    push_down ; simpl ;

    let H_lhs := fresh in
    let H_rhs := fresh in
    get_both_sides H_lhs H_rhs ; subst H_lhs ;
    push_down ; simpl.

  Ltac pull_up_assert :=
    match goal with
    | |- is_pure (both_prog (?f
                               (ret_both (is_pure (both_prog ?a)))
                               (ret_both (is_pure (both_prog ?b))))) = _ =>
        let H_a := fresh in
        let H_b := fresh in
        eassert (H_a : (is_pure a) = _) ;
        [ |
          eassert (H_b : (is_pure b) = _) ;
          [ | rewrite H_a ; rewrite H_b ; rewrite <- (hacspec_function_guarantees2 f) ; reflexivity ]
        ]
    | |- is_pure (both_prog (?f (ret_both (is_pure (both_prog ?a))))) = _ =>
        let H_a := fresh in
        eassert (H_a : (is_pure a) = _) ;
        [ | rewrite H_a ; rewrite <- (hacspec_function_guarantees f) ; reflexivity ]
    end.

  Ltac pull_up H :=
    let H_rewrite := fresh in
    eassert (H_rewrite : H = _) by repeat (pull_up_assert ; reflexivity) ; rewrite H_rewrite ; clear H_rewrite.

  Ltac pull_up_side H :=
    let H_rewrite := fresh in
    eassert (H_rewrite : H = _) ; subst H ; [ repeat pull_up_assert ; reflexivity | ] ; rewrite H_rewrite ; clear H_rewrite.

  Ltac remove_solve_lift :=
    repeat progress (rewrite (hacspec_function_guarantees2 _ (solve_lift _)) ; simpl) ;
    repeat progress (rewrite (hacspec_function_guarantees2 _ _ (solve_lift _)) ; simpl) ;
    repeat progress (rewrite (hacspec_function_guarantees _ (solve_lift _)) ; simpl).

  Ltac normalize_lhs :=
    let H_lhs := fresh in
    let H_rhs := fresh in
    get_both_sides H_lhs H_rhs ; subst H_rhs ;
    push_down ; simpl ;
    remove_solve_lift ; simpl ;
    get_both_sides H_lhs H_rhs ; subst H_rhs ;
    pull_up_side H_lhs.

  Ltac normalize_rhs :=
    let H_lhs := fresh in
    let H_rhs := fresh in
    get_both_sides H_lhs H_rhs ; subst H_lhs ;
    push_down ; simpl ;
    remove_solve_lift ; simpl ;
    get_both_sides H_lhs H_rhs ; subst H_lhs ;
    pull_up_side H_rhs.

  Ltac normalize_equation :=
    normalize_lhs ; normalize_rhs.

End Misc.

Definition lower1 {A B : choice_type} (f : both A -> both B) : A -> B :=
  fun x => is_pure (f (ret_both x)).

Definition lower2 {A B C : choice_type} (f : both A -> both B -> both C) : A -> B -> C :=
  fun x y => is_pure (f (ret_both x) (ret_both y)).

Lemma decidable_iff : forall P Q, (P <-> Q) -> decidable P -> decidable Q.
Proof.
  intros.
  destruct H0.
  - left.
    now apply H.
  - right.
    red ; intros.
    apply n.
    apply H.
    apply H0.
Qed.

Lemma running_state_is_pure : forall {A} (x : both A) h, fst (det_run (is_state x) (h := both_deterministic _) h) = is_pure x.
Proof.
  intros.
  epose (p_eq x true_precond).
  apply (sem_to_det _ _ _ _ (both_deterministic _) (deterministic_ret _)) in r.
  unfold det_jdg in r.
  specialize (r h h Logic.I).
  destruct (det_run (is_state x) h) eqn:d_eq in r |- *.
  unfold det_run in r.
  unfold pre_to_post_ret in r.
  simpl.
  apply r.
Qed.

Lemma state_equality_is_decidable :
  forall {A} (x y : both A),
    decidable (⊢ ⦃ fun '(h0, h1) => h0 = h1 ⦄ is_state x ≈ is_state y ⦃ fun a b => fst a = fst b ⦄).
Proof.
  intros.
  eapply (decidable_iff (det_jdg (fun '(h0, h1) => h0 = h1) (fun a b => fst a = fst b) (is_state x) (is_state y) (both_deterministic _) (both_deterministic _))).
  {
    split.
    - apply det_to_sem.
    - apply sem_to_det.
  }

  unfold det_jdg.

  intros.

  destruct (is_pure x == is_pure y) eqn:is_eq ;
    [ apply (ssrbool.elimT eqP) in is_eq ; left
    | apply (ssrbool.elimF eqP) in is_eq ; right ].
  - intros ? h ? ; subst.
    now rewrite !running_state_is_pure.
  - red ; intros.
    specialize (H empty_heap empty_heap erefl).
    now rewrite !running_state_is_pure in H.
Qed.


Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp Require Import all_ssreflect all_algebra.
From Coq Require Import Utf8.

(* Helper functions *)
Lemma card_prod_iprod3 :
  ∀ i j k,
    #|Datatypes_prod__canonical__fintype_Finite (Datatypes_prod__canonical__fintype_Finite (fintype_ordinal__canonical__fintype_Finite i) (fintype_ordinal__canonical__fintype_Finite j)) (fintype_ordinal__canonical__fintype_Finite k)| = (i * j * k)%N.
Proof.
  intros i j k.
  rewrite !card_prod. simpl. rewrite !card_ord. reflexivity.
Qed.

Definition ch3prod {i j k} `{Positive i} `{Positive j} `{Positive k}
  (xyz : Arit (uniform (i * j * k))) :
  Datatypes_prod__canonical__fintype_Finite (Datatypes_prod__canonical__fintype_Finite (Arit (uniform i)) (Arit (uniform j))) (Arit (uniform k)) :=
  let '(xy,z) := ch2prod xyz in
  let '(x,y) := ch2prod xy in
  (x,y,z).

Definition prod3ch {i j k} `{Positive i} `{Positive j} `{Positive k}
  (xyz : Datatypes_prod__canonical__fintype_Finite (Datatypes_prod__canonical__fintype_Finite (Arit (uniform i)) (Arit (uniform j))) (Arit (uniform k))) :
  Arit (uniform (i * j * k)) :=
  prod2ch (prod2ch (fst xyz),snd xyz).

Definition ch3prod_prod3ch :
  ∀ {i j k} `{Positive i} `{Positive j} `{Positive k}
    (x : Datatypes_prod__canonical__fintype_Finite (Datatypes_prod__canonical__fintype_Finite (Arit (uniform i)) (Arit (uniform j))) (Arit (uniform k))),
    ch3prod (prod3ch x) = x.
Proof.
  intros i j k hi hj hk xyz.
  unfold ch3prod, prod3ch.
  destruct xyz as [[]].
  now rewrite !ch2prod_prod2ch.
Qed.

Definition prod3ch_ch3prod :
  ∀ {i j k} `{Positive i} `{Positive j} `{Positive k} (x : Arit (uniform (i * j * k))),
    prod3ch (ch3prod x) = x.
Proof.
  intros i j k hi hj hk xyz.
  unfold ch3prod, prod3ch in *.
  rewrite -[RHS](prod2ch_ch2prod xyz).
  destruct (ch2prod xyz) as [xy z].
  set (s := xy) at 1 ; rewrite -(prod2ch_ch2prod xy) ; subst s.
  destruct (ch2prod xy) as [x y].
  rewrite ch2prod_prod2ch.
  reflexivity.
Qed.

Lemma r_uniform_triple :
  ∀ {A : ord_choiceType} i j k `{H : Positive i} `{H0 : Positive j} `{H1 : Positive k}
    (r : fin_family (mkpos (cond_pos := H) i) → fin_family (mkpos (cond_pos := H0) j) → fin_family (mkpos (cond_pos := H1) k) → raw_code A),
    (∀ x y z, ⊢ ⦃ λ '(s₀, s₁), s₀ = s₁ ⦄ r x y z ≈ r x y z ⦃ Logic.eq ⦄) →
    ⊢ ⦃ λ '(s₀, s₁), s₀ = s₁ ⦄
      xyz ← sample uniform (i * j * k) ;;
    let '(x,y,z) := ch3prod xyz in r x y z
                                     ≈
                                     x ← sample uniform i ;;
                                   y ← sample uniform j ;;
                                   z ← sample uniform k ;;
                                   r x y z
                                     ⦃ Logic.eq ⦄.
Proof.
  intros A i j k pi pj pk r h.
  eapply r_transR.
  1:{
    eapply r_uniform_bij with (f := id) ; [ now apply inv_bij | intros ].
    apply r_uniform_prod.
    intros ; apply rreflexivity_rule.
  }
  simpl.
  eapply r_transR.
  1:{
    apply r_uniform_prod.
    intros ; apply rreflexivity_rule.
  }
  simpl.
  eapply r_uniform_bij with (f := fun (xyz : Arit (uniform (i * j * k))) =>
                                    let '(x,y,z) := ch3prod xyz in
                                    (prod2ch (x,prod2ch(y,z))) : Arit (uniform (i * (j * k)))).
  {
    apply Bijective with (g :=  fun (xyz : Arit (uniform (i * (j * k)))) =>
                                  let '(x,yz) := ch2prod xyz in
                                  let '(y,z) := ch2prod yz in
                                  prod3ch (x,y,z) : Arit (uniform (i * j * k))).
    {
      intros xyz.
      rewrite -[RHS](prod3ch_ch3prod xyz).
      destruct (ch3prod xyz) as [[x y] z].
      now rewrite !ch2prod_prod2ch.
    }
    {
      intros xyz.
      rewrite -[RHS](prod2ch_ch2prod xyz).
      destruct (ch2prod xyz) as [x yz].
      set (s := yz) at 1 ; rewrite <- (prod2ch_ch2prod yz) ; subst s.
      destruct (ch2prod yz) as [y z].
      now rewrite !ch3prod_prod3ch.
    }
  }
  {
    intros xyz.
    unfold ch3prod.
    destruct ch2prod.
    destruct ch2prod.
    rewrite ch2prod_prod2ch.
    rewrite ch2prod_prod2ch.
    apply rreflexivity_rule.
  }
Qed.

Lemma if_bind : forall {A B} (k : A -> B) (a c : A) b,
    (let 'x :=
       if b
       then a
       else c
     in
     k x)
    =
      (if b then k a else k c).
Proof. now intros ? ? ? ? ? []. Qed.

Lemma if_then_if : forall {A} (a c e : A) b,
    (if b
     then
       if b
       then a
       else c
     else
       e)
    =
      (if b
       then a
       else e).
Proof. now intros ? ? ? ? []. Qed.

Lemma if_else_if : forall {A} (a c d : A) b,
    (if b
     then
       a
     else
       if b
       then c
       else d)
    =
      (if b
       then a
       else d).
Proof. now intros ? ? ? ? []. Qed.

Lemma if_if : forall {A} (a c d e : A) b,
    (if b
     then
       if b
       then a
       else c
     else
       if b
       then d
       else e)
    =
      (if b
       then a
       else e).
Proof. now intros ? ? ? ? ? []. Qed.

Lemma if_const : forall {A} (a: A) b, (if b then a else a) = a.
Proof. now intros ? ? []. Qed.

(* Helper function *)
Lemma compute_in_post_cond_R :
  forall {A B C : choice_type} (a : raw_code A) (b : raw_code B) (f : B -> C) pre post,
    ⊢ ⦃ pre ⦄ a ≈ b ⦃ fun '(x,h0) '(y,h1) => post (x, h0) (f y, h1) ⦄ ->
    ⊢ ⦃ pre ⦄ a ≈ v ← b ;; ret (f v) ⦃ post ⦄.
Proof.
  intros.
  eapply r_transL.
  2:{
    eapply r_bind.
    + apply H.
    + intros.
      apply r_ret.
      intros.
      apply H0.
  }
  rewrite bind_ret.
  apply rreflexivity_rule.
Qed.

(** Helper tactics *)
Ltac remove_ret_both_is_pure_from_args :=
  match goal with
  | [ |- context [ ?f (ret_both (is_pure ?x)) ?y ] ] =>
      setoid_rewrite (both_eq_fun_ext (fun k => f k y) (ret_both (is_pure x)) x) ; [ | now rewrite ret_both_is_pure_cancel]
  | [ |- context [ ?f ?x (ret_both (is_pure ?y)) ] ] =>
      setoid_rewrite (both_eq_fun_ext (fun k => f x k) (ret_both (is_pure y)) y) ; [ | now rewrite ret_both_is_pure_cancel]
  | [ |- context [ ?f (ret_both (is_pure ?y)) ] ] =>
      setoid_rewrite (both_eq_fun_ext f (ret_both (is_pure y)) y) ; [ | now rewrite ret_both_is_pure_cancel]
  end.

Ltac lower_proof proof :=
  intros ;
  unfold lower1 ;
  unfold lower2 ;
  apply (proj1 both_equivalence_is_pure_eq) ;
  repeat remove_ret_both_is_pure_from_args ;
  rewrite proof.

Lemma swap_samples :
  forall {n m : nat} {C} `{Positive n} `{Positive m} (c : 'I_n -> 'I_m -> raw_code C),
    ⊢ ⦃ λ '(s₀, s₁), s₀ = s₁ ⦄
      a0 ← sample uniform n ;;
    a1 ← sample uniform m ;;
    c a0 a1 ≈
      a1 ← sample uniform m ;;
    a0 ← sample uniform n ;;
    c a0 a1
      ⦃ Logic.eq ⦄.
Proof.
  intros.

  eapply r_transR.
  {
    apply r_uniform_prod.
    intros.
    apply rreflexivity_rule.
  }
  apply r_nice_swap_rule ; [ easy | easy | ].
  eapply r_transR.
  {
    apply r_uniform_prod.
    intros.
    apply rreflexivity_rule.
  }
  eapply r_uniform_bij with (f := fun x => let '(a,b) := ch2prod x in prod2ch (b,a)).
  {
    clear.
    econstructor.
    Unshelve.
    3: refine (fun x => let '(a,b) := ch2prod x in prod2ch (b,a)).
    all: intros x ; rewrite <- (prod2ch_ch2prod x) ; destruct (ch2prod x) ; now rewrite !ch2prod_prod2ch.
  }
  intros.
  destruct (ch2prod x).
  rewrite (ch2prod_prod2ch).

  apply rreflexivity_rule.
Qed.

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

From extructures Require Import ord fset fmap.

Ltac trim_is_interface :=
  setoid_rewrite filterm_set ; simpl ; fold chElement ;
  rewrite <- fset1E ;
  rewrite in_fset1 ;
  simpl ;
  rewrite eqxx ;
  rewrite filterm0 ;
  reflexivity.

Set Warnings "-notation-incompatible-prefix".
From SSProve.Crypt Require Import pkg_composition.
Set Warnings "notation-incompatible-prefix".

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

Import PackageNotation.

From SSProve.Crypt Require Import Package.

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
