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
    a ≈both ret_both (is_pure a).
Proof.
  intros.
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
    f x ≈both bind_both x (fun x => f (ret_both x)).
Proof.
  intros.
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
  eapply (both_eq_trans) ; [ apply (both_eq_lift2_both H H0) | ] ; simpl.
  apply both_eq_reflexivity.
Qed.

Lemma both_eq_andb_false : forall (a b : both 'bool),
    a ≈both ret_both (false : 'bool) \/ b ≈both ret_both (false : 'bool) ->
    (andb a b) ≈both ret_both (false : 'bool).
Proof.
  intros.
  destruct H ; eapply (both_eq_trans) ; [
      eapply (both_eq_lift2_both H (ret_both_is_pure_cancel _)) | simpl |
      eapply (both_eq_lift2_both (ret_both_is_pure_cancel _) H) |
      simpl ; rewrite Bool.andb_false_r ] ; apply both_eq_reflexivity.
Qed.

Lemma both_eq_eqb_true : forall {A : choice_type} `{t_Eq A} (a b : both A), a ≈both b <-> a =.? b ≈both ret_both (true : 'bool).
Proof.
  split ; intros [].
  - unfold eqb.
    eapply both_eq_trans ; [ eapply (both_eq_lift2_both (ret_both_is_pure_cancel _) (ret_both_is_pure_cancel _)) | ].
    rewrite H0.
    rewrite eqb_refl.
    apply both_eq_reflexivity.
  - apply both_equivalence_is_pure_eq.
    now apply eqb_leibniz.
Qed.

Check chList.

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
  apply both_equivalence_is_pure_eq.
  destruct H.
  rewrite hacspec_function_guarantees.
  now rewrite H.
Qed.

Lemma array_from_list_helper_eq_succ :
  forall {A} k (a b x y : both A) (xs ys : list (both A)),
    Datatypes.length xs = Datatypes.length ys ->
    a ≈both b ->
    array_from_list_helper x xs k ≈both array_from_list_helper y ys k ->
    array_from_list_helper a (x :: xs) k ≈both array_from_list_helper b (y :: ys) k.
Proof.
  Print array_from_list_helper.

  intros.
  rewrite !array_from_list_helper_equation_2.

  eapply both_eq_trans ; [ apply both_eq_bind ; apply ret_both_is_pure_cancel | ].
  eapply both_eq_trans ; [ apply both_eq_bind ; apply ret_both_is_pure_cancel | ].
  eapply both_eq_trans ; [ apply both_eq_solve_lift | ].

  apply both_eq_symmetry.

  eapply both_eq_trans ; [ apply both_eq_bind ; apply ret_both_is_pure_cancel | ].
  eapply both_eq_trans ; [ apply both_eq_bind ; apply ret_both_is_pure_cancel | ].
  eapply both_eq_trans ; [ apply both_eq_solve_lift | ].

  apply both_equivalence_is_pure_eq.
  simpl.

  rewrite (proj1 both_equivalence_is_pure_eq H0).
  rewrite (proj1 both_equivalence_is_pure_eq H1).

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
  - apply array_from_list_helper_base.
    apply H0.
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
    + apply ret_both_is_pure_cancel.
    + induction l.
      * apply List.Forall_nil.
      * apply List.Forall_cons.
        -- apply ret_both_is_pure_cancel.
        -- apply IHl.
Qed.
