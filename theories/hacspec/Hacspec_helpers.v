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
Qed.

Corollary both_deterministic : forall {A: choice_type} (a : both A), deterministic (is_state a).
Proof.
  intros.
  destruct a as [[] [] ?].
  apply (valid_both_is_deterministic is_pure is_state is_valid_both).
Qed.

Definition both_equivalence {A} (a : both A) (b : both A) :=
  is_pure a = is_pure b /\ ⊢ ⦃ true_precond ⦄ is_state a ≈ is_state b ⦃ fun '(a, h₀) '(b, h₁) => (a = b) ⦄.
Arguments both_equivalence {A} a b.
Infix "≈both" := (both_equivalence) (at level 77).

Require Import FunctionalExtensionality.

Lemma r_swap_post : forall {A B : choice_type} {P} {a b} (Q Q' : postcond A B),
    Q = Q' ->
    ⊢ ⦃ P ⦄ a ≈ b ⦃ Q' ⦄ ->
    ⊢ ⦃ P ⦄ a ≈ b ⦃ Q ⦄.
Proof. now intros ; subst. Qed.

Corollary r_transL_val' :
  forall {A : choice_type} (c₀ c₀' c₁ : raw_code A),
    deterministic c₀' ->
    deterministic c₀ ->
    deterministic c₁ ->
    ⊢ ⦃ true_precond ⦄ c₀ ≈ c₀' ⦃ fun '(v₀, _) '(v₁, _) => v₀ = v₁ ⦄ ->
    ⊢ ⦃ true_precond ⦄ c₀ ≈ c₁ ⦃ fun '(v₀, _) '(v₁, _) => v₀ = v₁ ⦄ ->
    ⊢ ⦃ true_precond ⦄ c₀' ≈ c₁ ⦃ fun '(v₀, _) '(v₁, _) => v₀ = v₁ ⦄.
Proof.
  intros A.
  pose (r := @r_transL_val A A (True) (@Logic.eq (Choice.sort (chElement A)))).
  now replace (fun '(_, _) => True) with true_precond in r by now apply functional_extensionality ; intros [].
Qed.

Lemma true_precond_ignores : (fun '(x, y) => true_precond (y, x)) = (fun '(x, y) => true_precond (x, y)).
Proof. now apply functional_extensionality; intros [] ; rewrite (boolp.propeqP). Qed.

Ltac prop_fun_eq :=
  repeat (apply functional_extensionality ; intros []) ; simpl ; rewrite (boolp.propeqP).

Corollary r_transR_val' :
  forall {A : choice_type} (c₀ c₀' c₁ : raw_code A),
    deterministic c₀' ->
    deterministic c₀ ->
    deterministic c₁ ->
    ⊢ ⦃ true_precond ⦄ c₀' ≈ c₀ ⦃ fun '(v₀, _) '(v₁, _) => v₀ = v₁ ⦄ ->
    ⊢ ⦃ true_precond ⦄ c₁ ≈ c₀ ⦃ fun '(v₀, _) '(v₁, _) => v₀ = v₁ ⦄ ->
    ⊢ ⦃ true_precond ⦄ c₀' ≈ c₁ ⦃ fun '(v₀, _) '(v₁, _) => v₀ = v₁ ⦄.
Proof.
  intros.
  apply r_transL_val' with c₀ ; try assumption.
  - apply rsymmetry.
    rewrite true_precond_ignores; apply better_r.
    eapply r_swap_post ; [ | apply H ].
    now prop_fun_eq.
  - apply rsymmetry.
    rewrite true_precond_ignores; apply better_r.
    eapply r_swap_post ; [ | apply H0 ].
    now prop_fun_eq.
Qed.

Ltac solve_deterministic :=
  (apply both_deterministic || apply deterministic_ret).

Lemma r_symmetry_both : forall {A : choice_type} (pure : A) (a_state b_state : raw_code A),
    ⊢ ⦃ true_precond ⦄ a_state ≈ b_state ⦃ pre_to_post_ret true_precond pure ⦄ ->
    ⊢ ⦃ true_precond ⦄ b_state ≈ a_state ⦃ pre_to_post_ret true_precond pure ⦄.
Proof.
  intros.
  apply rsymmetry.
  rewrite true_precond_ignores.
  apply better_r.
  apply (r_swap_post _ (pre_to_post_ret true_precond pure)), H.
  now prop_fun_eq.
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
      + apply rsymmetry.
        rewrite true_precond_ignores; apply better_r.
        eapply r_swap_post ; [ | apply (r_transR_val' (ret (is_pure b)) (ret (is_pure a)) (is_state b) ) ; try solve_deterministic ] ; [ now prop_fun_eq | .. ].
        * apply H.
        * apply pre_to_post_implies_eq ; try solve_deterministic. apply (p_eq b).
    - apply (r_transL_val' (is_state a) (ret (is_pure a)) (ret (is_pure b)) ) ; try solve_deterministic.
      + apply pre_to_post_implies_eq ; try solve_deterministic. apply (p_eq a).
      + apply (r_transR_val' (is_state b) (is_state a) (ret (is_pure b)) ) ; try solve_deterministic.
        * apply H.
        * apply rsymmetry.
          rewrite true_precond_ignores; apply better_r.
          eapply r_swap_post.
          2:{
            apply pre_to_post_implies_eq ; try solve_deterministic.
            apply p_eq.
          }
          now prop_fun_eq.
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
  1,2: destruct H ; split ; [ now rewrite <- H | apply rsymmetry ;
      rewrite true_precond_ignores; apply better_r ;
      eapply r_swap_post ; [ | apply H0 ] ; now prop_fun_eq ].
Qed.

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

Axiom hacspec_function_guarantees : forall {A B} (f : both A -> both B) (x : both A),
    is_pure (f x) = is_pure (f (ret_both (is_pure x))).

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

Theorem both_eq_fun_ext : forall {A B} (f : both A -> both B) (x y : both A),
    x ≈both y -> f x ≈both f y.
Proof.
  intros.
  unfold bind_both.
  unfold both_equivalence ; simpl.
  split ; [ | apply both_pure ].
  1,2: rewrite (hacspec_function_guarantees f x) ; rewrite (hacspec_function_guarantees f y) ; now destruct H.
Qed.

Lemma bind_both_eta : forall {A B} (f : both A -> both B) (x : both A),
    f x ≈both bind_both x (fun x => f (ret_both x)).
Proof.
  intros.
  unfold bind_both.
  unfold both_equivalence ; simpl.
  split.
  - now rewrite hacspec_function_guarantees.
  - apply rsymmetry.
    rewrite true_precond_ignores; apply better_r.
    match_bind_trans_both.
    eapply r_swap_post ; [ | apply both_pure ] ; [ now prop_fun_eq | .. ].
    now rewrite <- hacspec_function_guarantees.
Qed.
