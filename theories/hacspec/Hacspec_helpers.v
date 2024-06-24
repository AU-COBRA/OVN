From mathcomp Require Import all_ssreflect fingroup.fingroup ssreflect.
Set Warnings "-notation-overridden,-ambiguous-paths".
From Relational Require Import OrderEnrichedCategory .
From Crypt Require Import choice_type Package Prelude.
From Crypt Require Import Axioms ChoiceAsOrd RulesStateProb.
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

Require Import FunctionalExtensionality.

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

Corollary both_equivalence_is_pure_eq : forall {A} {a : both A} {b : both A},
    a ≈both b <-> is_pure a = is_pure b.
Proof.
  intros.
  unfold both_equivalence.
  now rewrite <- both_pure.
Qed.

Corollary both_equivalence_is_state_equivalence : forall {A} (a : both A) (b : both A),
    a ≈both b <-> ⊢ ⦃ true_precond ⦄ is_state a ≈ is_state b ⦃ fun '(a, h₀) '(b, h₁) => (a = b) ⦄.
Proof.
  intros.
  unfold both_equivalence.
  now rewrite both_pure.
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

Axiom hacspec_function_guarantees : forall {A B} (f : both A -> both B) (x : both A),
    is_pure (f x) = is_pure (f (ret_both (is_pure x))).

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

Corollary state_eq_pure :
  forall {A B} (f : both A -> both B) (x : both A),
  (⊢ ⦃ true_precond ⦄ is_state (f x) ≈ is_state (f (ret_both (is_pure x))) ⦃ fun '(a, _) '(b, _) => a = b ⦄)
<-> (is_pure (f x) = is_pure (f (ret_both (is_pure x)))).
Proof.
  split ; intros.
  - apply both_pure.
    apply H.
  - apply both_pure.
    apply H.
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
  epose (p_eq x).
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
