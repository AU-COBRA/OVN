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
    ∀ {A B : choiceType} (op : Op) c₀ c₁ (pre : precond) (post : postcond A B),
      LosslessOp op →
      (∀ x, ⊢ ⦃ pre ⦄ c₀ x ≈ c₁ ⦃ post ⦄) →
      ⊢ ⦃ pre ⦄ x ← sample op ;; c₀ x ≈ c₁ ⦃ post ⦄.
  Proof.
    intros A B op c₀ c₁ pre post hop h.
    eapply r_transR with (x ← sample op ;; (λ _, c₁) x).
    - apply r_dead_sample_L. 1: auto.
      apply rreflexivity_rule.
    - apply (rsame_head_cmd_alt (cmd_sample op)).
      + eapply rpre_weaken_rule. 1: eapply cmd_sample_preserve_pre.
        auto.
      + apply h.
  Qed.

  Lemma r_const_sample_R :
    ∀ {A B : choiceType} (op : Op) c₀ c₁ (pre : precond) (post : postcond A B),
      LosslessOp op →
      (∀ x, ⊢ ⦃ pre ⦄ c₀ ≈ c₁ x ⦃ post ⦄) →
      ⊢ ⦃ pre ⦄ c₀ ≈ x ← sample op ;; c₁ x ⦃ post ⦄.
  Proof.
    intros A B op c₀ c₁ pre post hop h.
    eapply r_transL with (x ← sample op ;; (λ _, c₀) x).
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
    ∀ {A₀ A₁ : _} {p₀ : raw_code A₀} {p₁ : raw_code A₁}
      (pre : precond) post,
      (∀ s₀ s₁,
          pre (s₀, s₁) → ⊢ ⦃ λ '(s₀', s₁'), s₀' = s₀ ∧ s₁' = s₁ ⦄ p₀ ≈ p₁ ⦃ post ⦄
      ) →
      ⊢ ⦃ pre ⦄ p₀ ≈ p₁ ⦃ post ⦄.
  Proof.
    intros A₀ A₁ p₀ p₁ pre post h.
    eapply rpre_hypothesis_rule.
    intros s0 s1 H. now eapply rpre_weaken_rule.
  Qed.


  Lemma r_eq_symmetry : forall {A B} {P Q} (c₀ : raw_code A) (c₁ : raw_code B) (f : A -> B),
      (forall (x y : heap), P (x, y) <-> P (y, x)) ->
      (forall (x : A) (y : B), Q (f x) y <-> Q y (f x)) ->
      ⊢ ⦃ P ⦄ c₁ ≈ c₀ ⦃ λ '(a, _) '(b, _), Q a (f b) ⦄ ->
      ⊢ ⦃ P ⦄ c₀ ≈ c₁ ⦃ λ '(a, _) '(b, _), Q (f a) b ⦄.
  Proof.
    intros.
    apply rsymmetry.
    eapply r_swap_precond ; [ prop_fun_eq ; apply H | ].
    eapply r_swap_post with (Q' := λ '(a, _) '(b, _), Q a (f b)); [ prop_fun_eq ; apply H0 | ].
    apply H1.
  Qed.

  Theorem r_transR_both :
    ∀ {A B : _} {x : raw_code A} {y z : both B}
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
    ∀ {A B : _} {x : raw_code A} {y : both B}
      (pre : precond) (post : postcond A B),
      ⊢ ⦃ pre ⦄ x ≈ ret (is_pure y) ⦃ post ⦄ ->
      ⊢ ⦃ pre ⦄ x ≈ is_state y ⦃ post ⦄.
  Proof.
    intros.
    eapply r_transR_both.
    + apply ret_both_is_pure_cancel.
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
    apply ret_both_is_pure_cancel.
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
  eapply (decidable_iff (det_jdg (λ '(h0, h1), h0 = h1) (fun a b => fst a = fst b) (is_state x) (is_state y) (both_deterministic _) (both_deterministic _))).
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

Module Type GroupOperationProperties (OVN_impl : Hacspec_ovn.HacspecOVNParams).
  Include OVN_impl.
  Export OVN_impl.

  Axiom f_sub_by_opp : forall x y, f_sub x y ≈both f_add x (f_opp y).

  Axiom f_addA : forall x y z, f_add x (f_add y z) ≈both f_add (f_add x y) z.
  Axiom f_addC: forall x y, f_add x y ≈both f_add y x.

  Axiom f_add0z: forall x, f_add f_field_zero x ≈both x.
  Axiom f_addNz: forall x, f_add (f_opp x) x ≈both f_field_zero.

  Axiom prod_pow_add_mul : forall x y z, f_prod (f_g_pow x) (f_pow (f_g_pow z) y) ≈both f_g_pow (f_add x (f_mul z y)).
  Axiom prod_pow_pow : forall h x a b, f_prod (f_pow h x) (f_pow (f_pow h a) b) ≈both f_pow h (f_add x (f_mul a b)).
  Axiom div_prod_cancel : forall x y, f_div (f_prod x y) y ≈both x.

  Axiom f_mulC : forall x y, f_mul x y ≈both f_mul y x.

  Axiom v_G_countable : Choice_isCountable (Choice.sort (chElement v_G)).
  Axiom v_G_isFinite : isFinite (Choice.sort (chElement v_G)).

  Axiom v_Z_countable : Choice_isCountable (Choice.sort (chElement v_G_t_Group.(f_Z))).
  Axiom v_Z_isFinite : isFinite (Choice.sort (chElement v_G_t_Group.(f_Z))).

  Axiom f_prodA : associative (lower2 f_prod).
  Axiom f_prod1 : associative (lower2 f_prod).
  Axiom f_prod_left_id : left_id (is_pure f_group_one) (lower2 f_prod).
  Axiom f_invK : involutive (lower1 f_group_inv).
  Axiom f_invM : {morph (lower1 f_group_inv)  : x y / (lower2 f_prod) x y >-> (lower2 f_prod)  y x}.

  (* Axiom v_Z_Field : GRing.Field (v_G_t_Group.(f_Z)). *)

  Axiom prod_inv_cancel : forall x, f_prod (f_group_inv x) x ≈both f_group_one.

  Axiom f_mul0 : forall x, f_mul f_field_zero x ≈both f_field_zero.
  Axiom f_mul1 : forall x, f_mul f_field_one x ≈both x.
  Axiom f_mulA : forall x y z, f_mul x (f_mul y z) ≈both f_mul (f_mul x y) z.
  Axiom f_mul_addr : forall x y z, f_mul (f_add x y) z ≈both f_add (f_mul x z) (f_mul y z).
  Axiom f_one_not_zero : ¬ (f_field_one ≈both f_field_zero).
  Axiom mul_inv_cancel : forall x, ¬ (x ≈both f_field_zero) -> f_mul (f_inv x) x ≈both f_field_one.
  Axiom f_inv0 : f_inv (f_field_zero) ≈both f_field_zero.

  Axiom generator_is_not_one : f_group_one ≈both f_g -> False.

  Axiom f_mulDr : forall x y z, f_mul x (f_add y z) ≈both f_add (f_mul x y) (f_mul x z).
  Axiom f_mulDl : forall x y z, f_mul (f_add x y) z ≈both f_add (f_mul x z) (f_mul y z).

End GroupOperationProperties.

Module HacspecGroup (OVN_impl : Hacspec_ovn.HacspecOVNParams) (GOP : GroupOperationProperties OVN_impl).
  Include GOP.
  Export GOP.

  Module OVN := HacspecOVN OVN_impl.
  Include OVN.
  Export OVN.

  #[local] Open Scope hacspec_scope.

  Definition add_sub_cancel : forall a b, f_add a (f_sub b a) ≈both b.
  Proof.
    intros.
    eapply both_eq_trans ; [ apply both_eq_fun_ext; apply (f_sub_by_opp _ _) | ].
    eapply both_eq_trans ; [ apply f_addC | ].
    eapply both_eq_trans ; [ apply both_eq_symmetry ; apply f_addA | ].
    eapply both_eq_trans ; [ apply both_eq_fun_ext ; apply f_addNz | ].
    eapply both_eq_trans ; [ apply f_addC | ].
    apply f_add0z.
  Qed.

  Definition add_sub_cancel2 : forall a b, f_add (f_sub b a) a ≈both b.
  Proof.
    intros.
    eapply both_eq_trans ; [ apply f_addC | ].
    apply add_sub_cancel.
  Qed.

  Definition v_G_Finite : Finite (Choice.sort (chElement v_G)) :=
    {|
      Finite.choice_hasChoice_mixin := Choice.choice_hasChoice_mixin (Choice.class v_G);
      Finite.choice_Choice_isCountable_mixin := v_G_countable;
      Finite.eqtype_hasDecEq_mixin := Choice.eqtype_hasDecEq_mixin (Choice.class v_G);
      Finite.fintype_isFinite_mixin := v_G_isFinite
    |}.

  Definition v_Z_Finite : Finite (Choice.sort (chElement v_Z)) :=
    {|
      Finite.choice_hasChoice_mixin := Choice.choice_hasChoice_mixin (Choice.class v_Z);
      Finite.choice_Choice_isCountable_mixin := v_Z_countable;
      Finite.eqtype_hasDecEq_mixin := Choice.eqtype_hasDecEq_mixin (Choice.class v_Z);
      Finite.fintype_isFinite_mixin := v_Z_isFinite
    |}.


  Definition f_field_finType : finType := Finite.Pack v_Z_Finite.
  Definition f_group_finType : finType := Finite.Pack v_G_Finite.

  Definition mul_group : isMulBaseGroup (v_G) :=
    {|
      isMulBaseGroup.mulg_subdef := lower2 f_prod;
      isMulBaseGroup.oneg_subdef := is_pure f_group_one;
      isMulBaseGroup.invg_subdef := lower1 f_group_inv;
      isMulBaseGroup.mulgA_subproof := f_prodA;
      isMulBaseGroup.mul1g_subproof := f_prod_left_id;
      isMulBaseGroup.invgK_subproof := f_invK;
      isMulBaseGroup.invMg_subproof := f_invM
    |}.

  Definition v_G_BaseFinGroup : baseFinGroupType :=
    BaseFinGroup.Pack
      {|
        BaseFinGroup.fingroup_isMulBaseGroup_mixin := mul_group;
        BaseFinGroup.choice_hasChoice_mixin := v_G_Finite;
        BaseFinGroup.choice_Choice_isCountable_mixin := v_G_Finite;
        BaseFinGroup.eqtype_hasDecEq_mixin := v_G_Finite;
        BaseFinGroup.fintype_isFinite_mixin := v_G_Finite
      |}.

  Lemma inv_mul_inverse : left_inverse (T := v_G_BaseFinGroup) (R := v_G) (oneg v_G_BaseFinGroup) invg mulg.
  Proof.
    unfold invg, mulg ; change 1%g with (is_pure f_group_one) ; simpl.
    intros x.
    unfold lower1, lower2.
    rewrite hacspec_function_guarantees ; rewrite <- hacspec_function_guarantees2.
    rewrite <- (both_equivalence_is_pure_eq).
    apply prod_inv_cancel.
  Qed.

  Definition v_G_is_group : finGroupType :=
    FinGroup.Pack
      {| FinGroup.fingroup_BaseFinGroup_isGroup_mixin :=
          {| BaseFinGroup_isGroup.mulVg_subproof := inv_mul_inverse |} |}.

  Ltac cancel_operations :=
    try apply both_eq_fun_ext ;
      try apply both_eq_fun_ext2 ;
      try (eapply both_eq_trans ; [ | apply both_eq_symmetry ; apply prod_pow_add_mul ]) ;
      try (eapply both_eq_trans ; [ | apply both_eq_symmetry ; apply add_sub_cancel ]) ;
      try (eapply both_eq_trans ; [ | apply both_eq_symmetry ; apply add_sub_cancel2 ]) ;
      try (eapply both_eq_trans ; [ | apply both_eq_symmetry ; apply prod_pow_pow ]) ;
      try (eapply both_eq_trans ; [ | apply both_eq_symmetry ; apply div_prod_cancel ]).

  Lemma f_lower_addA : forall x y z,
      lower2 f_add x (lower2 f_add y z) = lower2 f_add (lower2 f_add x y) z.
  Proof.
    intros.
    unfold lower2.
    rewrite hacspec_function_guarantees2.
    simpl (ret_both (is_pure _)) at 2.
    rewrite <- hacspec_function_guarantees2.

    symmetry.
    rewrite hacspec_function_guarantees2.
    simpl (ret_both (is_pure _)) at 1.
    rewrite <- hacspec_function_guarantees2.

    symmetry.

    apply (proj1 both_equivalence_is_pure_eq (f_addA (ret_both x) (ret_both y) (ret_both z))).
  Qed.

  Lemma f_lower_addC : forall x y,
      lower2 f_add x y = lower2 f_add y x.
  Proof.
    intros.
    unfold lower2.
    apply (proj1 both_equivalence_is_pure_eq (f_addC (ret_both x) (ret_both y))).
  Qed.

  Lemma f_lower_add0r : forall x,
      lower2 f_add (is_pure f_field_zero) x = x.
  Proof.
    intros.
    unfold lower2.

    rewrite hacspec_function_guarantees2.
    simpl (ret_both (is_pure _)) at 1.
    rewrite <- hacspec_function_guarantees2.

    apply (proj1 both_equivalence_is_pure_eq (f_add0z (ret_both x))).
  Qed.

  Definition v_Z_isNmodule : GRing.isNmodule.axioms_ f_Z :=
    {|
          GRing.isNmodule.zero := is_pure f_field_zero;
          GRing.isNmodule.add := lower2 f_add;
          GRing.isNmodule.addrA := f_lower_addA;
          GRing.isNmodule.addrC := f_lower_addC;
          GRing.isNmodule.add0r := f_lower_add0r
    |}.


  Lemma f_lower_mulrA : forall x y z,
      lower2 f_mul x (lower2 f_mul y z) = lower2 f_mul (lower2 f_mul x y) z.
  Proof.
    intros.
    unfold lower2.

    rewrite hacspec_function_guarantees2.
    simpl (ret_both (is_pure _)) at 2.
    rewrite <- hacspec_function_guarantees2.

    symmetry.
    rewrite hacspec_function_guarantees2.
    simpl (ret_both (is_pure _)) at 1.
    rewrite <- hacspec_function_guarantees2.

    symmetry.

    apply (proj1 both_equivalence_is_pure_eq (f_mulA (ret_both x) (ret_both y) (ret_both z))).
  Qed.

  Lemma f_lower_mulrC :
      commutative (lower2 f_mul).
  Proof.
    intros x y.
    unfold lower2.

    apply (proj1 both_equivalence_is_pure_eq (f_mulC (ret_both x) (ret_both y))).
  Qed.

  Lemma f_lower_mul1r : forall x,
      lower2 f_mul (is_pure f_field_one) x = x.
  Proof.
    intros.
    unfold lower2.

    rewrite hacspec_function_guarantees2.
    simpl (ret_both (is_pure _)) at 1.
    rewrite <- hacspec_function_guarantees2.

    apply (proj1 both_equivalence_is_pure_eq (f_mul1 (ret_both x))).
  Qed.

  Lemma f_lower_mulr1 : forall x,
      lower2 f_mul x (is_pure f_field_one) = x.
  Proof.
    intros.
    rewrite f_lower_mulrC.
    apply f_lower_mul1r.
  Qed.

  Lemma f_lower_mul0r : forall x,
      lower2 f_mul (is_pure f_field_zero) x = is_pure f_field_zero.
  Proof.
    intros.
    unfold lower2.

    rewrite hacspec_function_guarantees2.
    simpl (ret_both (is_pure _)) at 1.
    rewrite <- hacspec_function_guarantees2.

    apply (proj1 both_equivalence_is_pure_eq (f_mul0 (ret_both x))).
  Qed.

  Lemma f_lower_mulr0 : forall x,
      lower2 f_mul x (is_pure f_field_zero) = is_pure f_field_zero.
  Proof.
    intros.
    rewrite f_lower_mulrC.
    apply f_lower_mul0r.
  Qed.

  Lemma f_lower_mulrDl : left_distributive (lower2 f_mul) (lower2 f_add).
  Proof.
    intros.
    unfold left_distributive, lower2.
    intros.

    rewrite hacspec_function_guarantees2.
    simpl (ret_both (is_pure _)) at 1.
    rewrite <- hacspec_function_guarantees2.

    rewrite <- hacspec_function_guarantees2.

    apply (proj1 both_equivalence_is_pure_eq (f_mulDl (ret_both x) (ret_both y) (ret_both z))).
  Qed.

  Lemma f_lower_mulrDr : right_distributive (lower2 f_mul) (lower2 f_add).
  Proof.
    intros.
    unfold right_distributive, lower2.
    intros.

    rewrite hacspec_function_guarantees2.
    simpl (ret_both (is_pure _)) at 2.
    rewrite <- hacspec_function_guarantees2.

    rewrite <- hacspec_function_guarantees2.

    apply (proj1 both_equivalence_is_pure_eq (f_mulDr (ret_both x) (ret_both y) (ret_both z))).
  Qed.

  Lemma f_lower_oner_neq0 : is_pure f_field_one != is_pure f_field_zero.
  Proof.
    apply /eqP.
    red ; intros.
    apply f_one_not_zero.
    now apply (both_equivalence_is_pure_eq).
  Qed.

  Program Definition v_Z_Nmodule_isSemiRing : GRing.Nmodule_isSemiRing.axioms_ f_Z v_Z_isNmodule (Choice.class v_Z) (Choice.class v_Z) :=
    {|
      GRing.Nmodule_isSemiRing.one := is_pure f_field_one;
      GRing.Nmodule_isSemiRing.mul := lower2 f_mul;
      GRing.Nmodule_isSemiRing.mulrA := f_lower_mulrA;
      GRing.Nmodule_isSemiRing.mul1r := f_lower_mul1r;
      GRing.Nmodule_isSemiRing.mulr1 := f_lower_mulr1;
      GRing.Nmodule_isSemiRing.mulrDl := f_lower_mulrDl;
      GRing.Nmodule_isSemiRing.mulrDr := f_lower_mulrDr;
      GRing.Nmodule_isSemiRing.mul0r := f_lower_mul0r;
      GRing.Nmodule_isSemiRing.mulr0 := f_lower_mulr0;
      GRing.Nmodule_isSemiRing.oner_neq0 := f_lower_oner_neq0
    |}.
  Fail Next Obligation.

  Program Definition v_Z_hasCommutativeMul :
    GRing.SemiRing_hasCommutativeMul.axioms_ f_Z v_Z_isNmodule (Choice.class v_Z)
      (Choice.class v_Z) v_Z_Nmodule_isSemiRing :=
    {| GRing.SemiRing_hasCommutativeMul.mulrC := f_lower_mulrC |}.

  Lemma f_lower_addNr : forall x, (lower2 f_add) (lower1 f_opp x) x = is_pure f_field_zero.
  Proof.
    intros.
    unfold lower2.
    unfold lower1.
    
    rewrite hacspec_function_guarantees2.
    simpl (ret_both (is_pure _)) at 1.
    rewrite <- hacspec_function_guarantees2.

    apply (proj1 both_equivalence_is_pure_eq (f_addNz (ret_both x))).
  Qed.

  Program Definition v_Z_isZmodule : GRing.Nmodule_isZmodule.axioms_ f_Z v_Z_isNmodule (Choice.class v_Z) (Choice.class v_Z) :=
    {| GRing.Nmodule_isZmodule.opp := lower1 f_opp; GRing.Nmodule_isZmodule.addNr := f_lower_addNr |}.

  Lemma f_lower_mulVr : forall x, x != is_pure f_field_zero -> lower2 f_mul (lower1 f_inv x) x = is_pure f_field_one.
  Proof.
    intros.
    unfold lower1, lower2.

    rewrite hacspec_function_guarantees2.
    simpl (ret_both (is_pure _)) at 1.
    rewrite <- hacspec_function_guarantees2.

    refine (proj1 both_equivalence_is_pure_eq (mul_inv_cancel _ _)).

    red ; intros.
    apply (ssrbool.elimN eqP H).
    apply (proj1 both_equivalence_is_pure_eq H0).
  Qed.

  Program Definition f_lower_mulVr_subproof : _ :=
    proj2 (classical_sets.in_setP ( fun (x : f_Z) => x != is_pure f_field_zero ) (fun x => lower2 f_mul (lower1 f_inv x) x = is_pure f_field_one)) _.
  Next Obligation.
    apply f_lower_mulVr.
    assumption.
  Qed.

  Program Definition f_lower_mulrV_subproof : _ :=
    proj2 (classical_sets.in_setP ( fun (x : f_Z) => x != is_pure f_field_zero ) (fun x => lower2 f_mul x (lower1 f_inv x) = is_pure f_field_one)) _.
  Next Obligation.
    rewrite f_lower_mulrC.
    apply f_lower_mulVr.
    assumption.
  Qed.

  Definition f_lower_unitrP_subproof : forall (x y : f_Z), lower2 f_mul y x = is_pure f_field_one /\ lower2 f_mul x y = is_pure f_field_one -> classical_sets.in_set (λ x0 : f_Z, x0 != is_pure f_field_zero) x.
  Proof.
    intros ? ? [].

    
    unfold classical_sets.in_set.
    unfold boolp.asbool.
    destruct boolp.pselect.
    - reflexivity.
    - exfalso.
      apply n0.
      apply /eqP.
      red ; intros.
      subst x.
      rewrite (f_lower_mulr0 y) in H.
      apply f_one_not_zero.
      now apply both_equivalence_is_pure_eq.
  Qed.

  Definition f_lower_invr_out : {in [predC classical_sets.in_set (λ x0 : f_Z, x0 != is_pure f_field_zero)],
        lower1 f_inv =1 id}.
  Proof.
    intros ? ?.
    rewrite inE in H.
    rewrite classical_sets.notin_set in H.
    destruct (x == is_pure f_field_zero) eqn:H0 ; [ clear H | now exfalso ].
    apply (ssrbool.elimT eqP) in H0.
    rewrite H0.

    unfold lower1.
    rewrite <- hacspec_function_guarantees.

    apply (proj1 both_equivalence_is_pure_eq f_inv0).
  Qed.

  Program Definition v_Z_hasMulInverse : GRing.Ring_hasMulInverse.axioms_ f_Z v_Z_isNmodule (Choice.class v_Z) (Choice.class v_Z) v_Z_Nmodule_isSemiRing v_Z_isZmodule :=
    {|
      GRing.Ring_hasMulInverse.unit_subdef := classical_sets.in_set (λ x0 : f_Z, x0 != is_pure f_field_zero);
      GRing.Ring_hasMulInverse.inv := lower1 f_inv;
      GRing.Ring_hasMulInverse.mulVr_subproof := f_lower_mulVr_subproof;
      GRing.Ring_hasMulInverse.divrr_subproof := f_lower_mulrV_subproof;
      GRing.Ring_hasMulInverse.unitrP_subproof := f_lower_unitrP_subproof;
      GRing.Ring_hasMulInverse.invr_out_subproof := f_lower_invr_out
    |}.
  Fail Next Obligation.

  Program Definition v_Z_fieldP :
    GRing.MathCompCompatField.Field.mixin_of f_Z v_Z_isNmodule (Choice.class v_Z)
      (Choice.class v_Z) v_Z_Nmodule_isSemiRing v_Z_isZmodule v_Z_hasMulInverse :=
    {| GRing.UnitRing_isField.fieldP := _ |}.
  Next Obligation.
    rewrite unitrE.
    unfold "/".
    simpl.
    unfold "^-1"%R.
    simpl.
    rewrite f_lower_mulrC.
    now rewrite f_lower_mulVr ; [ apply eqxx | ].
  Qed.

  Program Definition v_Z_IntegralDomain :
  GRing.MathCompCompatIntegralDomain.IntegralDomain.mixin_of f_Z v_Z_isNmodule
    (Choice.class v_Z) (Choice.class v_Z) v_Z_Nmodule_isSemiRing v_Z_hasCommutativeMul v_Z_isZmodule
    v_Z_hasMulInverse.
  Proof.
    constructor.
    unfold GRing.MathCompCompatIntegralDomain.IntegralDomain.axiom.
    intros.
    admit.
  Admitted.

  Program Definition v_Z_Field : GRing.Field (v_G_t_Group.(f_Z)) :=
    {|
      GRing.Field.GRing_isNmodule_mixin := v_Z_isNmodule;
      GRing.Field.choice_hasChoice_mixin := v_Z_Finite;
      GRing.Field.eqtype_hasDecEq_mixin := v_Z_Finite;
      GRing.Field.GRing_Nmodule_isSemiRing_mixin := v_Z_Nmodule_isSemiRing;
      GRing.Field.GRing_SemiRing_hasCommutativeMul_mixin := v_Z_hasCommutativeMul;
      GRing.Field.GRing_Nmodule_isZmodule_mixin := v_Z_isZmodule;
      GRing.Field.GRing_Ring_hasMulInverse_mixin := v_Z_hasMulInverse;
      GRing.Field.GRing_UnitRing_isField_mixin := v_Z_fieldP;
      GRing.Field.GRing_ComUnitRing_isIntegral_mixin := v_Z_IntegralDomain
    |}.

  Definition v_Z_is_field : fieldType := {| GRing.Field.sort := f_Z; GRing.Field.class := v_Z_Field |}.

  Require Import Field.
  Check Field_theory.field_theory.

  Definition hacspec_ring_theory :
    ring_theory (R := v_Z_is_field) (is_pure f_field_zero) (is_pure f_field_one)
      (lower2 f_add) (lower2 f_mul)
      (lower2 (fun x y => f_add x (f_opp y)))
      (lower1 f_opp) eq_op.
  Proof.
    apply (mk_rt (is_pure f_field_zero) (is_pure f_field_one)
      (lower2 f_add)
      (lower2 f_mul)
      (lower2 (fun x y => f_add x (f_opp y)))
      (lower1 f_opp)
      eq_op).
    all: intros.
    all: apply (ssrbool.introT eqP).
    {
      intros.
      pose proof (proj1 both_equivalence_is_pure_eq (f_add0z (ret_both x))).
      rewrite hacspec_function_guarantees2 in H.
      apply H.
    }
    {
      apply (proj1 both_equivalence_is_pure_eq (f_addC (ret_both x)  (ret_both y))).
    }
    {
      pose proof (proj1 both_equivalence_is_pure_eq (f_addA (ret_both x)  (ret_both y) (ret_both z))).
      rewrite (hacspec_function_guarantees2) in H.
      rewrite (hacspec_function_guarantees2 _ (f_add _ _)) in H.
      apply H.
    }
    {
      pose proof (proj1 both_equivalence_is_pure_eq (f_mul1 (ret_both x))).
      rewrite (hacspec_function_guarantees2) in H.
      apply H.
    }
    {
      apply (proj1 both_equivalence_is_pure_eq (f_mulC (ret_both x) (ret_both y))).
    }
    {
      pose proof (proj1 both_equivalence_is_pure_eq (f_mulA (ret_both x) (ret_both y) (ret_both z))).
      rewrite hacspec_function_guarantees2 in H.
      rewrite (hacspec_function_guarantees2 _ (f_mul _ _)) in H.
      apply H.
    }
    {
      pose proof (proj1 both_equivalence_is_pure_eq (f_mul_addr (ret_both x) (ret_both y) (ret_both z))).
      rewrite hacspec_function_guarantees2 in H.
      rewrite (hacspec_function_guarantees2 _ (f_mul _ _)) in H.
      apply H.
    }
    {
      unfold lower2.
      unfold lower1.
      now rewrite hacspec_function_guarantees2.
    }
    {
      pose proof (proj1 both_equivalence_is_pure_eq (f_addC (ret_both x) (f_opp (ret_both x))  )).
      unfold lower2.
      unfold lower1.
      rewrite hacspec_function_guarantees2 in H.
      rewrite H ; clear H.
      apply (proj1 both_equivalence_is_pure_eq (f_addNz (ret_both x)  )).
    }
  Defined.

  Definition hacspec_field_theory :
    field_theory (R := v_Z_is_field) (is_pure f_field_zero) (is_pure f_field_one) (lower2 f_add)
             (lower2 f_mul) (lower2 (fun x y => f_add x (f_opp y)))
             (lower1 f_opp) (lower2 (fun x y => f_mul x (f_inv y)))
             (lower1 f_inv) eq_op.
  Proof.
    apply (mk_field
             (lower2 (fun x y => f_mul x (f_inv y)))
             (lower1 f_inv)
             hacspec_ring_theory
          ).
    {
      intros x.
      apply f_one_not_zero.
      apply (ssrbool.elimT eqP) in x.
      apply both_equivalence_is_pure_eq.
      easy.
    }
    {
      intros.
      apply (ssrbool.introT eqP).
      unfold lower2.
      unfold lower1.
      now rewrite hacspec_function_guarantees2.
    }
    {
      intros.
      apply (ssrbool.introT eqP).
      unfold lower2.
      unfold lower1.
      epose proof (proj1 both_equivalence_is_pure_eq (mul_inv_cancel (ret_both p) _)).
      rewrite hacspec_function_guarantees2 in H0.
      refine H0.
      Unshelve.
      intros x.
      apply H.
      apply (ssrbool.introT eqP).
      epose proof (proj1 both_equivalence_is_pure_eq x).
      apply H0.
    }
  Defined.

  Definition eqType_setoid_structure : forall {A : eqType}, Setoid.Setoid_Theory A eq_op.
  Proof.
    constructor.
    - intros x.
      apply eqxx.
    - intros x y H.
      now rewrite eq_sym.
    - intros x y z H0 H1.
      apply (ssrbool.introT eqP).
      apply (ssrbool.elimT eqP) in H0, H1.
      easy.
  Defined.

  Add Parametric Relation (A : eqType) :
    A eq_op
      reflexivity proved by (@RelationClasses.Equivalence_Reflexive A eq_op eqType_setoid_structure)
      symmetry proved by  (@RelationClasses.Equivalence_Symmetric A eq_op eqType_setoid_structure)
      transitivity  proved by (@RelationClasses.Equivalence_Transitive A eq_op eqType_setoid_structure)
      as eqType_setoid.

  Definition ring_eq_ext : Ring_theory.ring_eq_ext
      (lower2 f_add) (lower2 f_mul)
      (lower1 f_opp) eq_op.
  Proof.
    constructor.
    - intros x y H.
      intros z w H0.
      apply (ssrbool.introT eqP).
      apply (ssrbool.elimT eqP) in H , H0.
      subst.
      reflexivity.
    - intros x y H.
      intros z w H0.
      apply (ssrbool.introT eqP).
      apply (ssrbool.elimT eqP) in H , H0.
      subst.
      reflexivity.
    - intros x y H.
      apply (ssrbool.introT eqP).
      apply (ssrbool.elimT eqP) in H.
      subst.
      reflexivity.
  Defined.
  
  Add Ring v_Z_ring : hacspec_ring_theory ( setoid (eqType_setoid_structure (A := f_Z)) ring_eq_ext ).

  Require Import Setoid.
  Require Import Relation_Definitions.

  Add Morphism (@GRing.inv v_Z_is_field) with signature (@Logic.eq f_Z ==> @Logic.eq f_Z) as f_Z_inv.
  Proof. reflexivity. Qed.
  Add Parametric Morphism : (lower2 f_add) with signature (@Logic.eq v_Z_is_field ==> @Logic.eq v_Z_is_field ==> @Logic.eq v_Z_is_field) as f_Z_add.
  Proof. reflexivity. Qed.

  Check R_setoid3.

  Add Field v_Z_field : hacspec_field_theory ( setoid (R_setoid3 (eqType_setoid_structure (A := f_Z))) ring_eq_ext ).

  Program Definition inverse_morphism {R : fieldType} : Ring_theory.ring_morph _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ :=
    (@mkmorph
             R 0%R 1%R (fun x y => (GRing.add (x^-1) (y^-1))^-1)%R
             (fun x y => GRing.mul y x) (fun x y => (GRing.add (x^-1) (GRing.opp (y^-1)))^-1)%R
             (GRing.opp) eq_op

             R 0%R 1%R (GRing.add)
             (GRing.mul) (fun x y => GRing.add x (GRing.opp y))
             (GRing.opp) eq_op

             (GRing.inv)

             (ssrbool.introT eqP (invr0 _))
             (ssrbool.introT eqP (invr1 _))
             _
             (* (fun x _ => ssrbool.introT eqP (invrN (R := R) x)) *)
             _
             _
             (fun x => ssrbool.introT eqP (invrN (R := R) x))
             _
          ).
  Next Obligation.
    now rewrite !invrK.
  Qed.
  Next Obligation.
    now rewrite !invrK.
  Qed.
  Next Obligation.
    destruct (x != 0%R) eqn:x_not_zero.
    2:{
      apply (ssrbool.elimNf eqP) in x_not_zero.
      rewrite x_not_zero.
      rewrite mul0r.
      rewrite invr0.
      rewrite mulr0.
      apply eqxx.
    }

    destruct (y != 0%R) eqn:y_not_zero.
    2:{
      apply (ssrbool.elimNf eqP) in y_not_zero.
      rewrite y_not_zero.
      rewrite mulr0.
      rewrite invr0.
      rewrite mul0r.
      apply eqxx.
    }

    rewrite <- (unitfE) in x_not_zero, y_not_zero.
    refine (ssrbool.introT eqP (@invrM _ _ _ x_not_zero y_not_zero)).
  Qed.
  Next Obligation.
    now apply (ssrbool.elimT eqP) in H ; subst.
  Qed.
  Fail Next Obligation.

  Definition zq_ring_theory `{R : fieldType} :
    ring_theory (R := R) (0)%R (1)%R
      (GRing.add) (GRing.mul)
      (fun x y => GRing.add x (GRing.opp y))
      (GRing.opp) eq_op.
  Proof.
    apply (mk_rt (R := R) (0)%R (1)%R
      (GRing.add) (GRing.mul)
      (fun x y => GRing.add x (GRing.opp y))
      (GRing.opp) eq_op).
    all: intros.
    all: apply (ssrbool.introT eqP).
    { apply add0r.}
    { apply addrC.}
    { apply addrA.}
    { apply mul1r.}
    { apply mulrC.}
    { apply mulrA.}
    { apply mulrDl.}
    { reflexivity.}
    {
      apply (ssrbool.elimT eqP).
      rewrite subr_eq0.
      apply eqxx.
    }
  Defined.

  Definition zq_field_theory {R : fieldType} :
    field_theory (R := R) 0%R 1%R (GRing.add)
             (GRing.mul) (fun x y => GRing.add x (GRing.opp y))
             (GRing.opp) (fun x y => GRing.mul x (GRing.inv y))
             (GRing.inv) eq_op.
  Proof.
    apply (mk_field
             (fun x y => GRing.mul x (GRing.inv y))
             (GRing.inv)
             (zq_ring_theory)
          ).
    { now rewrite GRing.oner_eq0.}
    { easy.}
    {
      intros.
      apply (ssrbool.introT eqP).
      apply mulVr.
      now rewrite unitfE.
    }
  Defined.

  Lemma zq_ring_eq_ext {R : fieldType} : Ring_theory.ring_eq_ext
       (R := R) (GRing.add)
       (GRing.mul)
       (GRing.opp) eq_op.
  Proof.
    constructor.
    - intros x y H.
      intros z w H0.
      apply (ssrbool.introT eqP).
      apply (ssrbool.elimT eqP) in H , H0.
      subst.
      reflexivity.
    - intros x y H.
      intros z w H0.
      apply (ssrbool.introT eqP).
      apply (ssrbool.elimT eqP) in H , H0.
      subst.
      reflexivity.
    - intros x y H.
      apply (ssrbool.introT eqP).
      apply (ssrbool.elimT eqP) in H.
      subst.
      reflexivity.
  Qed.

End HacspecGroup.

Module Type SecureGroup  (OVN_impl : Hacspec_ovn.HacspecOVNParams) (GOP : GroupOperationProperties OVN_impl).
  Module Group := HacspecGroup OVN_impl GOP.
  Export Group.
  Include Group.

  Axiom v_G_prime_order : prime #[ is_pure f_g : v_G_is_group].
  Axiom v_G_g_gen : [set : v_G_is_group] = <[ is_pure f_g : v_G_is_group]>.
End SecureGroup.

Module HacspecGroupParam (OVN_impl : Hacspec_ovn.HacspecOVNParams) (GOP : GroupOperationProperties OVN_impl) (SG : SecureGroup OVN_impl GOP) <: GroupParam.
  Include SG.
  Export SG.

  Definition gT : finGroupType := v_G_is_group.
  Definition ζ : {set gT} := [set : gT].
  Definition g :  gT := is_pure f_g.

  Definition g_gen : ζ = <[g]> := v_G_g_gen.
  Definition prime_order : prime #[g] := v_G_prime_order.

  (* order of g *)
  Definition q : nat := #[g].

  Definition hacspec_zq_ring_theory := @zq_ring_theory 'F_q.
  Definition hacspec_zq_field_theory := @zq_field_theory 'F_q.

  Definition hacspec_zq_setoid_structure := (setoid_structure ('F_q)).
  Definition hacspec_zq_ring_eq_ext := @zq_ring_eq_ext 'F_q.

  Check sign_theory.
  Check Ring_theory.sign_theory _ _ _.
  Definition sign_zq (R : fieldType) : Ring_theory.sign_theory (GRing.opp) (eq_op) (fun x =>
    Some (GRing.opp x : R)).
  Proof.
    constructor.
    intros.
    inversion H.
    rewrite opprK.
    apply eqxx.
  Qed.

  Locate "_ ?=! _".
  (* Definition decidable_zq (R : fieldType) : (forall x y, (x ?=! y) = true -> x == y). *)
  (* Proof. *)
  (*   intros ; now apply /eqP. *)
  (* Qed. *)

  (* plugins/ring/InitialRing.v *)
  Add Ring zq_ring : hacspec_zq_ring_theory ( setoid hacspec_zq_setoid_structure hacspec_zq_ring_eq_ext ).

  Require Import Field.
  Check Field_theory.field_theory.

  (* Add Field zq_field : hacspec_zq_field_theory ( setoid hacspec_zq_setoid_structure hacspec_zq_ring_eq_ext ). *)

End HacspecGroupParam.

Module Type OVN_schnorr_proof_preconditions (OVN_impl : Hacspec_ovn.HacspecOVNParams) (GOP : GroupOperationProperties OVN_impl) (SG : SecureGroup OVN_impl GOP).
  Include SG.

  Module HacspecGroup := HacspecGroupParam OVN_impl GOP SG.
  Module Schnorr := Schnorr HacspecGroup.

  Import Schnorr.MyParam.
  Import Schnorr.MyAlg.

  Import Schnorr.Sigma.Oracle.
  Import Schnorr.Sigma.

  From mathcomp Require Import ssralg.

  Axiom WitnessToField :
    Witness -> v_G_t_Group.(f_Z).

  Axiom FieldToWitness :
    v_G_t_Group.(f_Z) -> Witness.

  Axiom WitnessToFieldCancel :
    (* cancel WitnessToField FieldToWitness. *)
    forall x, WitnessToField (FieldToWitness x) = x.

  Axiom FieldToWitnessCancel :
    (* cancel FieldToWitness WitnessToField. *)
    forall x, FieldToWitness (WitnessToField x) = x.

  Axiom WitnessToFieldAdd : forall x y, WitnessToField (x + y) = is_pure (f_add (ret_both (WitnessToField x)) (ret_both (WitnessToField y))).

  Axiom WitnessToFieldMul : forall x y, WitnessToField (Zp_mul x y) = is_pure (f_mul (ret_both (WitnessToField x)) (ret_both (WitnessToField y))).

  Axiom randomness_sample_is_bijective :
    bijective
    (λ x : 'I_(2 ^ 32),
       fto
         (FieldToWitness
            (is_pure
               (f_random_field_elem (ret_both (Hacspec_Lib_Pre.repr _ (Z.of_nat (nat_of_ord x)))))))).

  Axiom hash_is_psudorandom :
    forall {A B} i (H : Positive i) f pre post (c0 : _ -> raw_code A) (c1 : _ -> raw_code B) l,
            bijective f
            → (∀ x1 : Arit (uniform i), ⊢ ⦃ pre ⦄ c0 x1 ≈ c1 (f x1) ⦃ post ⦄) ->
            ⊢ ⦃ pre ⦄
          e ← sample uniform i ;;
          c0 e ≈
          x ← is_state
            (f_hash (t_Group := v_G_t_Group)
               (impl__into_vec
                  (unsize
                     (box_new
                        (array_from_list l))))) ;; c1 x ⦃ post ⦄.

  Axiom conversion_is_true :
    forall (b : both (v_G_t_Group.(f_Z))),
    (HacspecGroup.g ^+ FieldToWitness (is_pure b)) = is_pure (f_g_pow b).

End OVN_schnorr_proof_preconditions.

Module OVN_schnorr_proof (OVN_impl : Hacspec_ovn.HacspecOVNParams) (GOP : GroupOperationProperties OVN_impl) (SG : SecureGroup OVN_impl GOP) (proof_args : OVN_schnorr_proof_preconditions OVN_impl GOP SG).
  Import proof_args.

  Import Schnorr.MyParam.
  Import Schnorr.MyAlg.

  Import Schnorr.Sigma.Oracle.
  Import Schnorr.Sigma.

  Include proof_args.
  Export proof_args.

  Include Misc.

  Transparent OVN.schnorr_zkp.

  Definition run_code (ab : src (RUN, (choiceStatement × choiceWitness, choiceTranscript))) : code fset0 [interface
          #val #[ VERIFY ] : chTranscript → 'bool ;
          #val #[ RUN ] : chRelation → chTranscript
                                                                                                ] choiceTranscript :=
    {code (x ← op (RUN, ((chProd choiceStatement choiceWitness), choiceTranscript)) ⋅ ab ;;
              ret x) }.

  Transparent OVN.schnorr_zkp.
  Transparent run.

  Definition schnorr_run_post_cond :
    tgt (RUN, (choiceStatement × choiceWitness, choiceTranscript))
    → OVN.t_SchnorrZKPCommit → Prop.
  Proof.
    intros [[[l1 l2] l3] l4] [[r1 r2] r3] ; cbn in *.
    refine (((otf l2) = r1) /\ (WitnessToField (otf l3) = r2) /\ (WitnessToField (otf l4) = r3)).
  Defined.

 Lemma schnorr_run_eq  (pre : precond) :
    forall (b : Witness) c,
      Some c = lookup_op RUN_interactive (RUN, ((chProd choiceStatement choiceWitness), choiceTranscript)) ->
      ⊢ ⦃ pre ⦄
        c (fto (HacspecGroup.g ^+ b), fto b)
        ≈
        r ← sample uniform (2^32) ;;
        is_state (OVN.schnorr_zkp (ret_both (Hacspec_Lib_Pre.repr _ (Z.of_nat (nat_of_ord r)))) (ret_both ((HacspecGroup.g ^+ b))) (ret_both (WitnessToField b)))
          ⦃ fun '(x,_) '(y,_) => schnorr_run_post_cond x y  ⦄.
  Proof.
    intros.

    cbn in H.
    destruct choice_type_eqP ; [ | discriminate ].
    destruct choice_type_eqP ; [ | discriminate ].
    rewrite cast_fun_K in H.
    clear e e1.
    inversion_clear H.

    unfold OVN.schnorr_zkp.

    rewrite !otf_fto; unfold R; rewrite eqxx; unfold assertD.

    eapply rsymmetry ;
    eapply r_uniform_bij with (f := fun x => fto (FieldToWitness(is_pure (f_random_field_elem (t_Field := v_G_t_Group.(f_Z_t_Field)) (ret_both (Hacspec_Lib_Pre.repr _ (Z.of_nat (nat_of_ord x)))))))) ; [ apply randomness_sample_is_bijective | intros ] ;
    eapply rsymmetry.

    apply better_r_put_lhs.

    eapply (r_transR_both).
    - apply both_equivalence_is_pure_eq.
      repeat unfold let_both at 1.
      Transparent lift1_both.
      Transparent OVN.Build_t_SchnorrZKPCommit.
      simpl.
      apply prod_both_pure_eta_3.
    - eapply (r_transR_both).
      + set (r := prod_b (_, _, _)).
        set (f_hash _) in r.
        pattern b0 in r.
        subst r.
        apply bind_both_eta.
      + hnf.
        simpl.

        (* TODO : connect hash to random sample value ! *)
        (* apply (r_const_sample_L) ; [ apply LosslessOp_uniform | intros ]. *)
        eapply (hash_is_psudorandom _ _ (fun x => WitnessToField (otf x)) _ _ _ _ [:: _; _; _]).
        {
          exists (fun x => fto (FieldToWitness x)).
          -- now intros n ; rewrite FieldToWitnessCancel ; rewrite fto_otf.
          -- now intros n; rewrite otf_fto ; rewrite WitnessToFieldCancel.
        }
        intros.

        apply getr_set_lhs.

        set (ret _).
        set (prod_b (_,_,_)).
        apply (make_pure (x := r) (y := b0)).
        subst r b0.
        (* TODO : connect hash to random sample value ! *)

        apply r_ret.
        intros.
        repeat split.
        * rewrite! otf_fto.
           set (b0 := f_random_field_elem _) ; generalize dependent b0 ; intros.
           rewrite <- expgnE.
           apply conversion_is_true.
        * rewrite! otf_fto.
           rewrite WitnessToFieldAdd.
           rewrite WitnessToFieldCancel.
           rewrite WitnessToFieldMul.
           now rewrite <- !hacspec_function_guarantees2.
  Qed.
End OVN_schnorr_proof.

Module Type OVN_or_proof_preconditions (OVN_impl : Hacspec_ovn.HacspecOVNParams) (GOP : GroupOperationProperties OVN_impl) (SG : SecureGroup OVN_impl GOP).
  Module HacspecGroup := HacspecGroupParam OVN_impl GOP SG.
  Include HacspecGroup.
  Export HacspecGroup.

  Lemma order_ge1 : succn (succn (Zp_trunc (pdiv q))) = q.
  Proof.
    apply Fp_cast, prime_order.
  Qed.

  Lemma trunc_pow : forall (h : gT) x, h ^+ (x %% (Zp_trunc (pdiv q)).+2) = h ^+ x.
    intros.
    destruct (ssrbool.elimT (cycleP g h)) ; [ | subst ].
    - unfold g.
      setoid_rewrite <- v_G_g_gen.
      simpl.
      apply in_setT.
    - rewrite expgAC.
      rewrite (expgAC _ x0).
      f_equal.
      epose (@expg_mod_order gT g x).
      fold q in e.
      rewrite <- order_ge1 in e.
      intros.
      apply e ; clear e.
  Qed.

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

  Lemma invg_id : (forall (x : gT), x ^-1 = x ^- 1%R).
  Proof. reflexivity. Qed.

  Lemma trunc_extra : forall (h : gT), h ^+ (Zp_trunc (pdiv q)).+2 = 1.
    intros.
    rewrite <- trunc_pow.
    now rewrite modnn.
  Qed.

  Lemma reverse_opp : (forall (x : gT) (n : 'F_q), x ^+ ((Zp_trunc (pdiv q)).+2 - n) = x ^+ GRing.opp n).
  Proof.
    now intros ; rewrite trunc_pow.
  Qed.

  Lemma neg_is_opp : (forall (x : gT) (n : 'F_q), x ^- n = x ^+ GRing.opp n).
  Proof.
    intros x n.
    rewrite trunc_pow.
    destruct n as [n ?] ; simpl.
    induction n.
    - rewrite invg1.
      rewrite subn0.
      now rewrite trunc_extra.
    - rewrite expgSr.
      rewrite invMg.
      rewrite IHn ; [ | easy ].
      rewrite subnS.
      eapply canLR with (f := fun y => mulg (x^+1) y).
      {
        clear ; intros ?.
        rewrite mulgA.
        rewrite mulVg.
        rewrite mul1g.
        reflexivity.
      }

      rewrite <- expgD.
      rewrite addSn.
      rewrite add0n.
      set (subn _ _).
      now rewrite (Nat.lt_succ_pred 0 n1).
  Qed.

  Lemma mulg_cancel : forall (x : gT) (y : 'F_q),
      (cancel (mulg^~ (x ^+ y))  (mulg^~ (x ^- y))
      /\ cancel (mulg^~ (x ^- y))  (mulg^~ (x ^+ y)))
      /\ (cancel (mulg (x ^+ y))  (mulg (x ^- y))
      /\ cancel (mulg (x ^- y))  (mulg (x ^+ y))).
  Proof.
    now intros x y
    ; repeat split
    ; intros z
    ; (rewrite <- mulgA || rewrite mulgA)
    ; (rewrite mulgV || rewrite mulVg)
    ; (rewrite mulg1 || rewrite mul1g).
  Qed.

  Lemma prod_swap_iff : (forall a b (x : gT) (y : 'F_q), (a * x ^- y = b <-> a = b * x ^+ y) /\ (x ^- y * a = b <-> a = x ^+ y * b)).
  Proof.
    repeat split ;
      [ eapply (canRL (f := mulg^~ _) (g := mulg^~ _))
      | eapply (canLR (f := mulg^~ _) (g := mulg^~ _))
      | eapply (canRL)
      | eapply (canLR) ] ; apply (mulg_cancel x y).
  Qed.

  Lemma mulg_invg_sub : (forall (x : gT) (y z : 'F_q), x ^+ y * x ^- z = x ^+ nat_of_ord (y - z)).
  Proof.
    intros.
    rewrite neg_is_opp.
    rewrite <- expgD.
    now rewrite trunc_pow.
  Qed.

  Lemma mulg_invg_left_sub : (forall (x : gT) (y z : 'F_q), x ^- y * x ^+ z = x ^+ nat_of_ord (z - y)).
  Proof.
    intros.
    rewrite neg_is_opp.
    rewrite <- expgD.
    now rewrite trunc_pow.
  Qed.

  Lemma cyclic_always_commute : forall (x y : gT), commute x y.
  Proof.
    intros.
    destruct (ssrbool.elimT (cycleP g x)) ; [ | subst ].
    {
      unfold gT in x.
      unfold g.
      setoid_rewrite <- v_G_g_gen.
      simpl.
      apply in_setT.
    }

    destruct (ssrbool.elimT (cycleP g y)) ; [ | subst ].
    {
      unfold g.
      setoid_rewrite <- v_G_g_gen.
      simpl.
      apply in_setT.
    }

    apply commuteX2.
    apply commute_refl.
  Qed.

  Lemma div_cancel : forall (x : gT) (s : 'F_q), s <> 0 -> x ^+ nat_of_ord (s / s)%R = x.
  Proof.
    clear ; intros.
    rewrite mulrV.
    2: now rewrite unitfE ; apply /eqP.
    now rewrite expg1.
  Qed.

  Module MyParam <: SigmaProtocolParams.

    Definition Witness : finType := prod (prod (Finite.clone _ 'F_q) (Finite.clone _ 'bool)) gT.
    Definition Statement : finType := prod (prod gT gT) gT.
    Definition Message : finType :=  prod (prod (prod gT gT) gT) gT.
    Definition Challenge : finType := Finite.clone _ 'F_q.
    Definition Response : finType :=  (prod (prod (prod (Finite.clone _ 'F_q) (Finite.clone _ 'F_q)) (Finite.clone _ 'F_q)) (Finite.clone _ 'F_q)).

    Definition w0 : Witness := (0, false, 1).
    Definition e0 : Challenge := 0.
    Definition z0 : Response := 0.

    Definition R : Statement -> Witness -> bool :=
      (λ (xhy : Statement) (mv : Witness),
        let '(x,h,y) := xhy in
        let '(m,v,h2) := mv in
        (x == g ^+ m)
        && (h == h2)
        && ((y == h^+m * g ^+ v))
        (* && ((g ^+ v == g) || (g ^+ v == 1)) *)
      ).

    Lemma relation_valid_left:
      ∀ (x : 'F_q) (h : gT),
        R (g^+x, h, h^+x * g) (x, 1%R, h).
    Proof.
      intros x yi.
      unfold R.
      (* rewrite expgM. *)
      now rewrite !eqxx.
    Qed.

    Lemma relation_valid_right:
      ∀ (x : 'F_q) (h : gT),
        R (g ^+ x, h, h ^+x) (x, 0%R, h).
    Proof.
      intros x yi.
      unfold R.
      rewrite expg0.
      rewrite mulg1.
      now rewrite !eqxx.
    Qed.

    #[export] Instance positive_gT : Positive #|HacspecGroup.gT|.
    Proof.
      apply /card_gt0P. exists HacspecGroup.g. auto.
    Qed.

    #[export] Instance Bool_pos : Positive #|'bool|.
    Proof.
      rewrite card_bool. done.
    Defined.

    #[export] Instance Zq_pos : Positive #|Finite.clone _ 'F_q|.
    Proof.
      apply /card_gt0P. exists 0. auto.
    Defined.

    #[export] Instance prod_pos : forall {A B : finType}, Positive #|A| -> Positive #|B| -> Positive #|(prod A B : finType)|.
    Proof.
      intros.
      rewrite card_prod.
      now apply Positive_prod.
    Defined.

    Instance Witness_pos : Positive #|Witness| := _.
    Definition Statement_pos : Positive #|Statement| := _.
    Definition Message_pos : Positive #|Message| := _.
    Definition Challenge_pos : Positive #|Challenge| := _.
    Definition Response_pos : Positive #|Response| := _.

  End MyParam.

  Module MyAlg <: SigmaProtocolAlgorithms MyParam.

    Import MyParam.

    #[local] Existing Instance Bool_pos.

    Definition choiceWitness : choice_type := 'fin #|Witness|.
    Definition choiceStatement : choice_type := 'fin #|Statement|.
    Definition choiceMessage : choice_type := 'fin #|Message|.
    Definition choiceChallenge : choice_type := 'fin #|Challenge|.
    Definition choiceResponse : choice_type := 'fin #|Response|.
    Definition choiceTranscript : choice_type :=
      chProd
        (chProd (chProd choiceStatement choiceMessage) choiceChallenge)
        choiceResponse.
    Definition choiceBool := 'fin #|'bool|.

    Definition i_witness := #|Finite.clone _ 'F_q|.

    Definition HIDING : nat := 0.
    Definition SOUNDNESS : nat := 1.

    Definition commit_loc : Location := (('fin #|Finite.clone _ 'F_q| × 'fin #|Finite.clone _ 'F_q| × 'fin #|Finite.clone _ 'F_q| : choice_type); 2%N).

    Definition Sigma_locs : {fset Location} := fset [:: commit_loc].
    Definition Simulator_locs : {fset Location} := fset0.

    Definition Commit (hy : choiceStatement) (xv : choiceWitness):
      code Sigma_locs [interface] choiceMessage :=
      {code
         w ← sample uniform i_witness ;;
         d ← sample uniform i_witness ;;
         r ← sample uniform i_witness ;;
         #put commit_loc := (w, r, d) ;;
         let '(x, h, y) := (otf hy) in
         let '(m, v, _) := (otf xv) in
         if v
         then
           (
             let r1 := r in
             let d1 := d in

             let a1 := (g ^+ (otf r1 : 'F_q) * x ^+ (otf d1 : 'F_q)) in
             let b1 := (h ^+ (otf r1 : 'F_q) * y ^+ (otf d1 : 'F_q)) in

             let a2 := (g ^+ (otf w : 'F_q)) in
             let b2 := (h ^+ (otf w : 'F_q)) in
             ret (fto (a1, b1, a2, b2)))
         else
           (let r2 := r in
            let d2 := d in

            let a1 := (g ^+ (otf w : 'F_q)) in
            let b1 := (h ^+ (otf w : 'F_q)) in

            let a2 := (g ^+ (otf r2 : 'F_q) * x ^+ (otf d2 : 'F_q)) in
            let b2 := (h ^+ (otf r2 : 'F_q) * (y * g^-1) ^+ (otf d2 : 'F_q)) in
            ret (fto (a1, b1, a2, b2)))
      }.

    Definition Verify (xhy : choiceStatement) (a : choiceMessage)
      (c : choiceChallenge) (z : choiceResponse) : choiceBool :=
      let '(x, h, y) := otf xhy in
      let '(a1, b1, a2, b2) := (otf a) in
      let '(r1, d1, r2, d2) := (otf z) in
      fto ((otf c == d1 + d2) &&
             (a1 == (g ^+ r1) * (x ^+ d1)) &&
             (b1 == (h ^+ r1) * (y ^+ d1)) &&
             (a2 == (g ^+ r2) * (x ^+ d2)) &&
             (b2 == (h ^+ r2) * ((y * (g ^-1)) ^+ d2))).


    Definition Response (xhy : choiceStatement) (xv : choiceWitness) (_ : choiceMessage) (c : choiceChallenge) :
      code Sigma_locs [interface] choiceResponse :=
      {code
         '(w, r, d) ← get commit_loc ;;
         let '(x, h, y) := (otf xhy) in
         let '(m, v, _) := (otf xv) in
         if v (* y == h ^+ m * g *)
         then
           (let d2 := (otf c - otf d) in
            let r2 := (otf w - (m * d2)) in
            ret (fto (otf r, otf d, r2, d2)))
         else
           (let d1 := (otf c - otf d) in
            let r1 := (otf w - (m * d1)) in
            ret (fto (r1, d1, otf r, otf d)))
      }.

    Definition Simulate (xhy : choiceStatement) (c : choiceChallenge) :
      code Simulator_locs [interface] choiceTranscript :=
      {code
         d ← sample uniform i_witness ;;
         r ← sample uniform i_witness ;;
         r_other ← sample uniform i_witness ;;
         let '(x, h, y) := otf xhy in
         let d2 := otf d in
         let r2 := otf r in
         let r1 := otf r_other in
         let d1 := otf c - d2 in
         let a1 := g ^+ r1 * x ^+ d1 in
         let b1 := h ^+ r1 * y ^+ d1 in
         let a2 := g ^+ r2 * x ^+ d2 in
         let b2 := h ^+ r2 * (y * invg g) ^+ d2 in
         ret (xhy , fto (a1,b1,a2,b2), c , fto (r1,d1,r2,d2))
      }.

    Definition Extractor (xhy : choiceStatement) (a : choiceMessage)
      (c : choiceChallenge) (c' : choiceChallenge)
      (z : choiceResponse)  (z' : choiceResponse) : 'option choiceWitness :=
      let '(
              (x, h, y),
              (a1, b1, a2, b2),
              (r1,d1,r2,d2),
              (r1',d1',r2',d2')
            ) :=
        (otf xhy, otf a, otf z, otf z') in

      let m := if d1 - d1' != 0
               then ((r1' - r1) / (d1 - d1'))
               else ((r2' - r2) / ((d2 - d2'))) in
      let v := ~~ (d1 - d1' != 0) (* y == h ^+ m * g *) in
      Some (fto (m, v, h)).
    Fail Next Obligation.

    Definition KeyGen (xv : choiceWitness) :=
      let '(m, v, h) := otf xv in
      fto (g ^+ m, h ^+ m, h ^+ m * g ^+ v).

  End MyAlg.

  Module Sigma := SigmaProtocol MyParam MyAlg.
  Check Sigma.run_interactive_shvzk.
  Import MyParam.
  Import MyAlg.
  Import Sigma.Oracle.
  Import Sigma.
  Axiom WitnessToField : {rmorphism 'F_ HacspecGroup.q -> v_Z_is_field}.
    (* 'F_q -> v_G_t_Group.(f_Z). *)
  Axiom FieldToWitness : {rmorphism v_Z_is_field -> 'F_ HacspecGroup.q}.
    (* v_G_t_Group.(f_Z) -> Finite.clone _ 'F_q. *)
  Axiom WitnessToFieldCancel :
    (* cancel WitnessToField FieldToWitness. *)
    forall x, WitnessToField (FieldToWitness x) = x.
  Axiom FieldToWitnessCancel :
    (* cancel FieldToWitness WitnessToField. *)
    forall x, FieldToWitness (WitnessToField x) = x.

  Axiom randomness_sample_is_bijective :
    bijective
    (λ x : 'I_(2 ^ 32),
       fto
         (FieldToWitness
            (is_pure
               (f_random_field_elem (ret_both (Hacspec_Lib_Pre.repr _ (Z.of_nat (nat_of_ord x)))))))).
  Axiom hash_is_psudorandom :
    forall {A B} i (H : Positive i) f pre post (c0 : _ -> raw_code A) (c1 : _ -> raw_code B) l,
            bijective f
            → (∀ x1 : Arit (uniform i), ⊢ ⦃ pre ⦄ c0 x1 ≈ c1 (f x1) ⦃ post ⦄) ->
            ⊢ ⦃ pre ⦄
          e ← sample uniform i ;;
          c0 e ≈
          x ← is_state
            (f_hash (t_Group := v_G_t_Group)
               (impl__into_vec
                  (unsize
                     (box_new
                        (array_from_list l))))) ;; c1 x ⦃ post ⦄.

  Axiom pow_witness_to_field :
    forall (h : gT) (b : 'F_q),
      (h ^+ b = is_pure (f_pow (ret_both h) (ret_both (WitnessToField b)))).

  Axiom pow_base : forall x, f_g_pow x ≈both f_pow (ret_both g) x.
  Axiom div_is_prod_inv : forall x y, f_div x y ≈both f_prod x (f_group_inv y).

  Definition FieldToWitnessOpp : (forall (b : both _), Zp_opp (FieldToWitness (is_pure b)) = FieldToWitness (is_pure (f_opp b))).
  Proof.
    intros.
    setoid_rewrite <- (rmorphN FieldToWitness).
    unfold "- _".
    simpl.
    unfold lower1.
    rewrite <- hacspec_function_guarantees.
    reflexivity.
  Qed.
    
  (* (* Axiom FieldToWitnessInv : (forall (b : both (v_G_t_Group.(f_Z))), Zp_inv (FieldToWitness (is_pure b)) = FieldToWitness (is_pure (f_inv b))). *) *)
  (* Lemma FieldToWitnessInv : forall (b : f_Z), Zp_inv (FieldToWitness b) = FieldToWitness (is_pure (f_inv (ret_both b))). *)
  (* Proof. *)
  (*   intros. *)
  (*   simpl. *)
    
  
  Axiom WitnessToField_f_inv : forall s, (f_inv (ret_both (WitnessToField s)) = ret_both (WitnessToField (Zp_inv s))).
  
  Lemma FieldToWitnessOne : FieldToWitness (is_pure f_field_one) = 1%R.
  Proof.
    intros.
    now rewrite GRing.rmorph1.
  Qed.

End OVN_or_proof_preconditions.

Module OVN_or_proof (OVN_impl : Hacspec_ovn.HacspecOVNParams) (GOP : GroupOperationProperties OVN_impl) (SG : SecureGroup OVN_impl GOP) (proof_args : OVN_or_proof_preconditions OVN_impl GOP SG).
  Import proof_args.

  Import MyParam.
  Import MyAlg.

  Import Sigma.Oracle.
  Import Sigma.

  Include proof_args.
  Export proof_args.

  Include Misc.

  Transparent OVN.zkp_one_out_of_two.

  Definition f_d2r2_to_wd : 'F_q -> 'I_MyAlg.i_witness -> Arit (uniform (MyAlg.i_witness * MyAlg.i_witness)) → Arit (uniform (MyAlg.i_witness * MyAlg.i_witness)) :=
    fun m c dr =>
      let '(d2, r2) := (ch2prod dr) in
      prod2ch (fto ((otf r2) + (m * (otf d2))), fto (otf c - otf d2)).

  Lemma f_d2r2_to_wd_bij : forall m c, bijective (f_d2r2_to_wd m c).
    intros.
    eapply (Bijective (g := fun dr =>
      let '(d2, r2) := (ch2prod dr) in
      prod2ch (fto (otf c - otf r2), fto (otf d2 - (otf c - otf r2) * m)))).
    - intros z.
      unfold f_d2r2_to_wd.
      rewrite <- prod2ch_ch2prod.
      set (ch2prod _) at 2 3.
      destruct s eqn:ch2z.
      rewrite ch2prod_prod2ch.
      rewrite !otf_fto.
      f_equal.
      rewrite subKr.
      rewrite !fto_otf.
      f_equal.
      rewrite mulrC.
      rewrite addrK.
      rewrite !fto_otf.
      reflexivity.
    - intros z.
      unfold f_d2r2_to_wd.
      rewrite <- prod2ch_ch2prod.
      set (ch2prod _) at 2 3.
      destruct s eqn:ch2z.
      rewrite ch2prod_prod2ch.
      rewrite !otf_fto.
      f_equal.
      rewrite subKr.
      rewrite !fto_otf.
      f_equal.
      rewrite mulrC.
      rewrite subrK.
      rewrite !fto_otf.
      reflexivity.
  Qed.

  Definition f_d1r1_to_wd : 'F_q -> 'I_MyAlg.i_witness -> Arit (uniform (MyAlg.i_witness * MyAlg.i_witness)) → Arit (uniform (MyAlg.i_witness * MyAlg.i_witness)) :=
    fun m c dr =>
      let '(d2, r1) := ch2prod dr in
      prod2ch (fto ((otf r1) + (m * (otf c - otf d2))), fto (otf d2)).

  Lemma f_d1r1_to_wd_bij : forall m c, bijective (f_d1r1_to_wd m c).
    intros.
    eapply (Bijective (g := fun dr =>
                              let '(d2, r2) := (ch2prod dr) in
                              prod2ch (r2, fto (otf d2 - m * (otf c - otf r2))))).
    - intros z.
      unfold f_d1r1_to_wd.
      rewrite <- prod2ch_ch2prod.
      set (ch2prod _) at -1.
      destruct s eqn:ch2z.
      rewrite ch2prod_prod2ch.
      rewrite !fto_otf.
      rewrite !otf_fto.
      f_equal.
      f_equal.
      rewrite addrK.
      rewrite !fto_otf.
      reflexivity.
    - intros z.
      unfold f_d1r1_to_wd.
      rewrite <- prod2ch_ch2prod.
      set (ch2prod _) at -1.
      destruct s eqn:ch2z.
      rewrite ch2prod_prod2ch.
      rewrite !fto_otf.
      rewrite !otf_fto.
      f_equal.
      f_equal.
      rewrite subrK.
      rewrite !fto_otf.
      reflexivity.
  Qed.

  Definition run_code (ab : src (RUN, (choiceStatement × choiceWitness, choiceTranscript))) : code fset0 [interface
          #val #[ VERIFY ] : chTranscript → 'bool ;
          #val #[ RUN ] : chRelation → chTranscript
                                                                                                ] choiceTranscript :=
    {code (x ← op (RUN, ((chProd choiceStatement choiceWitness), choiceTranscript)) ⋅ ab ;;
              ret x) }.

  Transparent run.
  Definition hacspec_ret_to_or_sigma_ret : Statement -> OVN.t_OrZKPCommit -> choiceTranscript.
  Proof.
    intros hy [[[[[[[[[[r1x r2y] r3a1] r4b1] r5a2] r6b2] r7c] r8d1] r9d2] r10r1] r11r2].
    refine (fto _, fto _, fto _, fto _).
    (* choiceStatement *)
    - refine hy.

    (* choiceMessage *)
    - refine (r3a1, r4b1, r5a2, r6b2).

    (* choiceChallenge = hash *)
    - refine (FieldToWitness r7c).

    (* choiceResponse *)
    - refine (FieldToWitness r10r1, FieldToWitness r8d1, FieldToWitness r11r2, FieldToWitness r9d2).
  Defined.

  Definition or_run_post_cond :
    choiceStatement ->
    tgt (RUN, (choiceStatement × choiceWitness, choiceTranscript))
    → OVN.t_OrZKPCommit → Prop.
  Proof.
    intros stmt a b.
    refine (a = hacspec_ret_to_or_sigma_ret (otf stmt) b).
  Defined.

 Lemma or_run_eq  (pre : precond) :
    forall (b : Statement * Witness) c,
      Some c = lookup_op RUN_interactive (RUN, ((chProd choiceStatement choiceWitness), choiceTranscript)) ->
      ⊢ ⦃ fun '(h₁, h₀) => heap_ignore Sigma_locs (h₀, h₁) ⦄
        c (fto (fst b), fto (snd b))
        ≈
        #assert R (b.1) (b.2) ;;
        wr ← sample uniform (2^32) ;;
        dr ← sample uniform (2^32) ;;
        rr ← sample uniform (2^32) ;;
        is_state (OVN.zkp_one_out_of_two
                    (ret_both (Hacspec_Lib_Pre.repr _ (Z.of_nat (nat_of_ord wr))))
                    (ret_both (Hacspec_Lib_Pre.repr _ (Z.of_nat (nat_of_ord rr))))
                    (ret_both (Hacspec_Lib_Pre.repr _ (Z.of_nat (nat_of_ord dr))))
                    (ret_both (snd (fst (fst b))))
                    (ret_both (WitnessToField (fst (fst (snd b)))))
                    (ret_both ((snd (fst b) == (snd (fst (fst b)) ^+  (fst (fst (snd b))) * g)) : 'bool)))
          ⦃ fun '(x,h0) '(y,h1) => or_run_post_cond (fto (fst b)) x y ∧ heap_ignore Sigma_locs (h0, h1) ⦄.
  Proof.
    intros [[[x h] y] [[m v] n]] c H.

    simpl fst ; simpl snd.

    simpl in H.
    destruct choice_type_eqP as [ e | ] ; [ | discriminate ].
    destruct choice_type_eqP as [ e1 | ] ; [ | discriminate ].
    rewrite cast_fun_K in H.
    clear e e1.
    inversion_clear H.

    unfold OVN.zkp_one_out_of_two.

    rewrite !otf_fto; unfold R.
    apply r_assertD ; [ reflexivity | ].
    intros _ ?.
    simpl in e₁.
    repeat (apply andb_prop in e₁ ; destruct e₁ as [e₁ ?]).
    (* apply (ssrbool.elimT orP) in H. *)
    apply reflection_nonsense in e₁(* , H *)(* , H0 *)(* , H1 *).
    subst.

    pose (bij_f := randomness_sample_is_bijective).
    set (f_rand := fun _ => _) in bij_f.

    eapply rsymmetry ; eapply r_uniform_bij with (f := fun x => _) ; [ apply bij_f | intros x0 ] ; apply rsymmetry ; apply better_r.
    eapply rsymmetry ; eapply r_uniform_bij with (f := fun x => _) ; [ apply bij_f | intros x1 ] ; apply rsymmetry ; apply better_r.
    eapply rsymmetry ; eapply r_uniform_bij with (f := fun x => _) ; [ apply bij_f | intros x2] ; apply rsymmetry ; apply better_r.

    apply better_r_put_lhs.

    pose (f_rand_inner := fun (x : 'I_(2 ^ 32)) => (FieldToWitness
            (is_pure
               (f_random_field_elem (ret_both (Hacspec_Lib_Pre.repr _ (Z.of_nat (nat_of_ord x)))))))).
    progress repeat match goal with
    | [ |- context [ otf (f_rand ?x) ] ] =>
        replace (_ (f_rand x)) with (f_rand_inner x) by now rewrite otf_fto
      end.
    subst f_rand f_rand_inner.

    (* destruct (y == h ^+ m * g) eqn:H. *)
    destruct v.
    {
      apply reflection_nonsense in H(* , H0, H1 *).
      subst.

      rewrite !eqxx.

      repeat unfold let_both at 1.
      simpl.
      Transparent Build_t_OrZKPCommit.
      unfold Build_t_OrZKPCommit; hnf.

      eapply (r_transR_both (B := t_OrZKPCommit)) ; [ set (H_hash := f_hash _); pattern_lhs_both_pat H_hash ; apply (bind_both_eta) |  hnf ; unfold bind_both at 1, bind_raw_both, both_prog at 1, is_state at 1; set (f_or := fun _ => is_state (bind_both _ _)) ].

      (* TODO : connect hash to random sample value ! *)
      (* apply (r_const_sample_L) ; [ apply LosslessOp_uniform | intros ]. *)
      eapply (hash_is_psudorandom _ _ (fun x => WitnessToField (otf x)) _ _ _ _ [:: _; _; _; _; _; _]).
      {
        exists (fun x => fto (FieldToWitness x)).
        -- now intros ? ; rewrite FieldToWitnessCancel ; rewrite fto_otf.
        -- now intros ? ; rewrite otf_fto ; rewrite WitnessToFieldCancel.
      }
      intros x3.

      apply getr_set_lhs.
      apply make_pure ; simpl.

      apply r_ret.
      intros ? ? ?.

      unfold or_run_post_cond.
      unfold hacspec_ret_to_or_sigma_ret.

      rewrite FieldToWitnessCancel.
      rewrite !otf_fto.
      unfold lower2 ; simpl.
      (* rewrite !mulg1. *)

      set (f_random_field_elem _).
      set (f_random_field_elem _).
      set (f_random_field_elem _).

      split.
      - repeat (rewrite pair_equal_spec ; split).
        (* Statement *)
        {
          reflexivity.
        }
        (* Commit *)
        {
          apply f_equal.
          repeat rewrite pair_equal_spec ; repeat split.
          all: clear ; simpl; push_down_sides.
          all: repeat setoid_rewrite <- expgnE.

          - (* g ^ r * g ^ s ^ d = f_prod (f_g_pow r) (f_pow (f_g_pow s) d) *)
            rewrite pow_witness_to_field; rewrite WitnessToFieldCancel.
            rewrite pow_witness_to_field; rewrite WitnessToFieldCancel.
            rewrite !(proj1 both_equivalence_is_pure_eq (pow_base _)).
            rewrite pow_witness_to_field.
            reflexivity.
          - rewrite pow_witness_to_field; rewrite WitnessToFieldCancel.
            rewrite (pow_witness_to_field (is_pure (f_prod _ _))) ; rewrite WitnessToFieldCancel.
            rewrite !pow_witness_to_field.
            now push_down_sides.
          - rewrite pow_witness_to_field; rewrite WitnessToFieldCancel.
            now rewrite !(proj1 both_equivalence_is_pure_eq (pow_base _)).
          - now rewrite pow_witness_to_field; rewrite WitnessToFieldCancel.
        }
        (* Challenges *)
        {
          now rewrite fto_otf.
        }
        (* Response *)
        {
          apply f_equal.
          repeat (rewrite pair_equal_spec ; split).
          all: clear ; simpl; push_down_sides.
          all: repeat setoid_rewrite <- expgnE.
          - reflexivity.
          - reflexivity.
          -
            rewrite !(proj1 both_equivalence_is_pure_eq (f_sub_by_opp _ _)).
            rewrite hacspec_function_guarantees2.
            rewrite !rmorphD.
            rewrite <- !FieldToWitnessOpp.
            apply f_equal.
            apply f_equal.
            rewrite  hacspec_function_guarantees2.
            simpl.
            rewrite (rmorphM).
            rewrite !FieldToWitnessCancel.
            apply f_equal.
            rewrite !(proj1 both_equivalence_is_pure_eq (f_sub_by_opp _ _)).
            rewrite hacspec_function_guarantees2.
            rewrite rmorphD.
            rewrite <- FieldToWitnessOpp.
            simpl.
            rewrite !FieldToWitnessCancel.
            reflexivity.
          - rewrite !(proj1 both_equivalence_is_pure_eq (f_sub_by_opp _ _)).
            rewrite hacspec_function_guarantees2.
            rewrite rmorphD.
            rewrite <- FieldToWitnessOpp.

            simpl.
            rewrite FieldToWitnessCancel.
            reflexivity.
        }
      - clear -H.
        destruct H.
        destruct H.
        subst.
        unfold heap_ignore.
        intros.
        unfold heap_ignore in H.

        rewrite H ; [ | assumption ].
        unfold Sigma_locs in H0 ; rewrite <- fset1E in H0 ; rewrite in_fset1 in H0.
        now rewrite <- get_heap_set_heap.
    }
    {
      apply reflection_nonsense in H(* , H0, H1 *).
      subst.
      set (_ == _).
      replace b with false.
      2:{
        symmetry.
        apply /eqP.
        intros ?.
        subst.

        apply generator_is_not_one.
        eapply both_equivalence_is_pure_eq.
        apply prod_swap_iff in H.
        rewrite expg0 in H.
        rewrite mulg1 in H.
        rewrite mulVg in H.

        fold g.
        rewrite <- H.
        reflexivity.
      }

      Opaque Build_t_OrZKPCommit.
      simpl.
      repeat unfold let_both at 1.
      simpl.
      Transparent Build_t_OrZKPCommit.
      unfold Build_t_OrZKPCommit; hnf.

      eapply (r_transR_both (B := t_OrZKPCommit)) ; [ set (H_hash := f_hash _); pattern_lhs_both_pat H_hash ; apply (bind_both_eta) |  hnf ; unfold bind_both at 1, bind_raw_both, both_prog at 1, is_state at 1; set (f_or := fun _ => is_state (bind_both _ _)) ].

      (* TODO : connect hash to random sample value ! *)
      (* apply (r_const_sample_L) ; [ apply LosslessOp_uniform | intros ]. *)
      eapply (hash_is_psudorandom _ _ (fun x => WitnessToField (otf x)) _ _ _ _ [:: _; _; _; _; _; _]).
      {
        exists (fun x => fto (FieldToWitness x)).
        -- now intros ? ; rewrite FieldToWitnessCancel ; rewrite fto_otf.
        -- now intros ? ; rewrite otf_fto ; rewrite WitnessToFieldCancel.
      }
      intros x3.

      apply getr_set_lhs.
      apply make_pure ; simpl.

      apply r_ret.
      intros ? ? ?.

      unfold or_run_post_cond.
      rewrite !otf_fto.
      unfold lower2 ; simpl.

      set (f_random_field_elem _).
      set (f_random_field_elem _).
      set (f_random_field_elem _).

      split.
      - repeat (rewrite pair_equal_spec ; split).
        {
          reflexivity.
        }
        (* Commit *)
        {
          apply f_equal.
          repeat rewrite pair_equal_spec ; repeat split.
          all: clear ; simpl; push_down_sides.
          all: repeat setoid_rewrite <- expgnE.

          + rewrite pow_witness_to_field; rewrite WitnessToFieldCancel.
            now rewrite !(proj1 both_equivalence_is_pure_eq (pow_base _)).
          + now rewrite pow_witness_to_field; rewrite WitnessToFieldCancel.
          + rewrite pow_witness_to_field; rewrite WitnessToFieldCancel.
            rewrite pow_witness_to_field; rewrite WitnessToFieldCancel.
            rewrite !(proj1 both_equivalence_is_pure_eq (pow_base _)).
            (* rewrite prod_witness_to_field. *)
            rewrite <- pow_witness_to_field.
            reflexivity.
          + rewrite expg0.
            rewrite mulg1.

            rewrite pow_witness_to_field; rewrite WitnessToFieldCancel.
            (* rewrite prod_witness_to_field. *)
            rewrite pow_witness_to_field.
            unfold lower1.
            rewrite (proj1 both_equivalence_is_pure_eq (div_is_prod_inv _ _)).

            (* rewrite WitnessToFieldCancel. *)
            rewrite pow_witness_to_field.
            rewrite WitnessToFieldCancel.
            (* rewrite pow_witness_to_field. *)
            (* rewrite prod_witness_to_field. *)
            now push_down_sides.
        }
        (* Challenges *)
        {
          now rewrite FieldToWitnessCancel ; rewrite fto_otf.
        }
        (* Response *)
        {
          apply f_equal.
          repeat (rewrite pair_equal_spec ; split).
          all: clear ; simpl; push_down_sides.
          all: repeat setoid_rewrite <- expgnE.
          - rewrite !(proj1 both_equivalence_is_pure_eq (f_sub_by_opp _ _)).
            rewrite hacspec_function_guarantees2.
            rewrite rmorphD.
            rewrite <- FieldToWitnessOpp.
            simpl.
            apply f_equal.
            apply f_equal.

            rewrite hacspec_function_guarantees2.
            rewrite rmorphM.

            rewrite !(proj1 both_equivalence_is_pure_eq (f_sub_by_opp _ _)).
            rewrite hacspec_function_guarantees2.
            rewrite rmorphD.
            rewrite <- FieldToWitnessOpp.
            simpl.
            now rewrite !FieldToWitnessCancel.
          - rewrite !(proj1 both_equivalence_is_pure_eq (f_sub_by_opp _ _)).
            rewrite hacspec_function_guarantees2.
            rewrite rmorphD.
            rewrite <- FieldToWitnessOpp.
            simpl.
            now rewrite !FieldToWitnessCancel.
          - reflexivity.
          - reflexivity.
        }
      - clear -H.
        destruct H.
        destruct H.
        subst.
        unfold heap_ignore.
        intros.
        unfold heap_ignore in H.

        rewrite H ; [ | assumption ].
        unfold Sigma_locs in H0 ; rewrite <- fset1E in H0 ; rewrite in_fset1 in H0.
        now rewrite <- get_heap_set_heap.
    }
    (* Qed. *)
    Fail Timeout 5 Qed. Admitted. (* SLOW: 525.61 sec *)

  Program Definition hacspec_or_run :
    package Sigma_locs
        [interface]
        [interface
          #val #[ RUN ] : chRelation → chTranscript
        ]
    :=
      [package
         #def #[ RUN ] (b : chRelation) : chTranscript
        {
          #assert R (otf b.1) (otf b.2) ;;
          wr ← sample uniform (2^32) ;;
          dr ← sample uniform (2^32) ;;
          rr ← sample uniform (2^32) ;;
          v ← is_state (OVN.zkp_one_out_of_two
                      (ret_both (Hacspec_Lib_Pre.repr _ (Z.of_nat (nat_of_ord wr))))
                      (ret_both (Hacspec_Lib_Pre.repr _ (Z.of_nat (nat_of_ord rr))))
                      (ret_both (Hacspec_Lib_Pre.repr _ (Z.of_nat (nat_of_ord dr))))
                      (ret_both (snd (fst (otf (fst b)))))
                      (ret_both (WitnessToField (fst (fst (otf (snd b))))))
                      (ret_both ((snd (otf (fst b)) == (snd (fst (otf (fst b))) ^+  (fst (fst (otf (snd b)))) * g)) : 'bool))) ;;
          ret (hacspec_ret_to_or_sigma_ret (otf b.1) v)
      }].
  Next Obligation.
    eapply (valid_package_cons _ _ _ _ _ _ [] []).
    - apply valid_empty_package.
    - intros.
      ssprove_valid.
      set (zkp_one_out_of_two _ _ _ _ _ _).
      apply valid_scheme.
      rewrite <- fset0E.
      apply (ChoiceEquality.is_valid_code (both_prog_valid b)).
    - try (rewrite <- fset0E ; setoid_rewrite @imfset0 ; rewrite in_fset0 ; reflexivity).
  Qed.
  Fail Next Obligation.

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

  Lemma hacspec_vs_RUN_interactive :
    ∀ LA A,
      ValidPackage LA [interface
                         #val #[ RUN ] : chRelation → chTranscript
        ] A_export A →
      fdisjoint LA Sigma_locs →
      AdvantageE hacspec_or_run RUN_interactive A = 0.
  Proof.
    intros LA A Va Hdisj.
    eapply eq_rel_perf_ind_ignore.
    6,7: apply Hdisj.
    5: apply Va.
    2:{
      unfold RUN_interactive.
      eapply valid_package_inject_export.
      2:{
        eapply (valid_package_cons).
        + eapply (valid_package_cons).
          * apply valid_empty_package.
          * intros.
            ssprove_valid ; apply prog_valid.
          * try (rewrite <- fset0E ; setoid_rewrite @imfset0 ; rewrite in_fset0 ; reflexivity).
        + intros.
          ssprove_valid ; apply prog_valid.
        + rewrite <- fset1E.
          rewrite imfset1.
          reflexivity.
      }
      - rewrite !fset_cons.
        apply fsubsetUr.
    }
    {
      apply hacspec_or_run.
    }
    {
      apply fsubsetUl.
    }
    unfold eq_up_to_inv.
    intros.
    unfold get_op_default.

    set (match _ with | Option_Some _ => _ | None => _ end) at 2.
    rewrite <- fset1E in H.
    apply (ssrbool.elimT (fset1P _ _)) in H.
    inversion H.
    Opaque zkp_one_out_of_two.
    simpl (lookup_op _ _).
    destruct choice_type_eqP ; [ | subst ; contradiction ].
    destruct choice_type_eqP ; [ | subst ; contradiction ].
    subst.
    rewrite cast_fun_K.
    apply rsymmetry.

    destruct x.

    set (pkg_core_definition.sampler _ _).

    eassert (r =
              (v ← (wr ← sample uniform (2 ^ 32) ;;
                    dr ← sample uniform (2 ^ 32) ;;
                    rr ← sample uniform (2 ^ 32) ;;
                    is_state
                      (zkp_one_out_of_two _
                         _
                         _
                         (ret_both ((snd (fst (otf (s, s0).1)))))
                         _
                         _)) ;;
               ret (hacspec_ret_to_or_sigma_ret (otf (s, s0).1) v))) by (now subst r ; simpl) ; rewrite H0 ; clear H0.
    clear.

    eapply r_transR ; [ apply r_bind_assertD | hnf ].
    apply compute_in_post_cond_R.
    eapply rpost_weaken_rule.
    1:{
      eapply r_transL.
      2:{
        eapply (or_run_eq (λ '(h₁, h₀), heap_ignore Sigma_locs (h₀, h₁)) (otf s, otf s0) y).
        subst y.
        simpl.
        destruct choice_type_eqP ; [ | subst ; contradiction ].
        destruct choice_type_eqP ; [ | subst ; contradiction ].
        subst.
        rewrite cast_fun_K.
        reflexivity.
      }
      {
        rewrite !fto_otf.
        apply rreflexivity_rule.
      }
    }
    {
      intros.
      destruct a₀.
      destruct a₁.
      destruct H.
      unfold or_run_post_cond in H.
      rewrite H.
      rewrite fto_otf.
      split ; [ reflexivity | ].
      unfold heap_ignore in H0.
      unfold heap_ignore.
      intros.
      specialize (H0 ℓ H1).
      easy.
    }
  Qed.

  (* Special honest verify zero knowledge *)
  Lemma run_interactive_or_shvzk :
    ∀ LA A,
      ValidPackage LA [interface
                         #val #[ RUN ] : chRelation → chTranscript
        ] A_export A →
      fdisjoint LA Sigma_locs →
      AdvantageE hacspec_or_run (SHVZK_real_aux ∘ SHVZK_real) A = 0.
  Proof.
    intros.
    apply (AdvantageE_le_0 _ _ _ ).
    eapply Order.le_trans ; [ eapply (Advantage_triangle _ _ RUN_interactive _) | ].
    rewrite (run_interactive_shvzk Simulator_locs (fun x => {code r ← sample uniform #|Challenge| ;; Simulate x r }) LA A H H0).
    rewrite GRing.addr0.
    now rewrite hacspec_vs_RUN_interactive.
  Qed.

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


  Lemma shvzk_success:
    ∀ LA A,
      ValidPackage LA [interface
                         #val #[ TRANSCRIPT ] : chInput → chTranscript
        ] A_export A →
      fdisjoint LA Sigma_locs →
      ɛ_SHVZK A = 0.
  Proof.
    intros.
    unfold ɛ_SHVZK.
    unfold SHVZK_real.
    unfold SHVZK_ideal.
    apply: eq_rel_perf_ind.
    all: ssprove_valid.
    1:{ instantiate (1 := heap_ignore Sigma_locs).
        ssprove_invariant.
        apply fsubsetUl. }
    2: apply fdisjoints0.
    clear H0.
    1:{
      unfold eq_up_to_inv.
      intros.
      unfold get_op_default.

      rewrite <- fset1E in H0.
      apply (ssrbool.elimT (fset1P _ _)) in H0.
      inversion H0.

      subst.

      Opaque Simulate Commit Response.

      simpl (lookup_op _ _).


      destruct choice_type_eqP ; [ | subst ; contradiction ].
      destruct choice_type_eqP ; [ | subst ; contradiction ].
      subst.
      rewrite !cast_fun_K.

      clear e e1.

      destruct x as [[hy mv] c].
      ssprove_sync_eq. intros.

      Transparent Simulate.
      unfold Simulate.
      Transparent Commit.
      unfold Commit.
      Transparent Response.
      unfold Response.
      unfold prog. rewrite bind_ret.

      destruct (otf mv) as [[m vi] n] eqn:mvo.
      destruct (otf hy) as [[x h] y] eqn:hyo.

      simpl bind.

      unfold R in e.
      simpl in e.
      repeat (apply andb_prop in e ; destruct e as [e ?]).
      apply reflection_nonsense in e, H1, H2.
      symmetry in H2.
      subst.

      eapply r_transR ; [ apply r_uniform_triple ; intros ; apply rreflexivity_rule | ].
      apply rsymmetry.
      eapply r_transR ; [ apply r_uniform_triple ; intros ; apply rreflexivity_rule | ].

      eapply r_uniform_bij with
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
        )).
      {
        eapply Bijective with
          (g :=  fun (wdr : Arit (uniform (_ * _ * _))) =>
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
                   prod3ch (d, r, r_other)).
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
      intros d2r2r1.
      apply rsymmetry.

      simpl ch3prod.

      destruct (ch3prod _) as [[d2 r2] r1] at 2 3.

      rewrite (if_bind (fun '(w,d0,r0) => _)).
      rewrite (if_bind ch3prod).
      rewrite !ch3prod_prod3ch.
      rewrite (if_bind (fun '(w,d0,r0) => _)).

      rewrite !otf_fto.
      rewrite !trunc_pow.
      rewrite !expgD.
      rewrite !trunc_pow.
      rewrite !expgM.

      assert (forall {A} (ℓ : Location) b a c (f g : raw_code A),
                 ⊢ ⦃ λ '(s₀, s₁), s₀ = s₁ ⦄ #put ℓ := (if b then a else c) ;;
                             if b
                             then f
                             else g
                   ≈ if b
                   then #put ℓ := a ;; f
                   else #put ℓ := c ;; g
                    ⦃ Logic.eq ⦄) by now intros ? ? [] ? ? ? ? ; apply rreflexivity_rule.

      assert (forall {A B} b (y z : raw_code A) (f k : A -> raw_code B),
                 (if b
              then x ← y ;;
                   f x
              else x ← z ;;
                   k x) = (x ← (if b then y else z) ;;
                           (if b then f else k) x)) by now intros ; destruct b.

      eapply r_transL.
      1: apply H1.
      apply better_r_put_lhs.


      rewrite H2.

      rewrite !(if_bind bind).

      rewrite (if_then_if).
      rewrite (if_else_if).

      assert (forall {A B} b (x y : raw_code A) (f g : A -> raw_code B),
                 (if b then bind x else bind y) (if b
                  then f
                  else g) = (if b then bind x f else bind y g)) by now intros ; destruct b.
      rewrite H3.
      rewrite !bind_rewrite.

      assert (forall {B} b ℓ (f g : _ -> raw_code B),
                 (if b then x ← get ℓ ;; f x else x ← get ℓ ;; g x) = (x ← get ℓ ;; if b then f x else g x)) by now intros ; destruct b.
      rewrite H4.

      apply getr_set_lhs (* rewrite otf_fto *).

      rewrite (if_bind (fun '(w,d0,r0) => _)).
      rewrite !(if_then_if).
      rewrite !(if_else_if).


      rewrite !(if_bind bind).
      unfold bind at 1 2.

      assert (forall {A B} b (x y : A) (f g : A -> raw_code B),
                 (if b then (if b
                            then f
                            else g) x else (if b
                            then f
                            else g) y) = (if b then f x else g y)) by now intros ; destruct b.
      rewrite H5.
      rewrite !bind_rewrite.

      rewrite !(trunc_pow).
      rewrite !(expgD).
      rewrite !(trunc_pow).

      rewrite <- (if_bind (fun x => ret x)).
      apply r_ret.

      intros ? ? H_post.
      split ; [clear s₀ s₁ H_post | ].
      2:{
        destruct H_post as [? [H_post ?]].
        subst.
        unfold heap_ignore in H_post.
        unfold heap_ignore.
        intros ℓ H_loc.
        specialize (H_post ℓ H_loc).
        rewrite <- H_post.

        unfold Sigma_locs in H_loc.
        rewrite <- fset1E in H_loc.
        rewrite in_fset1 in H_loc.

        now rewrite get_set_heap_neq.
      }

      set (p := (_,_,_,_)).
      pattern vi in p.
      subst p.

      set (p := (_,_,_,_)) at 2.
      pattern vi in p.
      subst p.

      assert (forall {A} (f g : bool -> A) b, (if b then f b else g b) = if b then f true else g false) by now intros ; destruct b.
      rewrite H6.

      match goal with
      | [ |- context [ _ = ?rhs ] ] => set (p := rhs) ; pattern vi in p ; subst p
      end.

      assert (forall {A} (f : bool -> A) b, (if b then f true else f false) = f b) by now intros ; destruct b.
      set (f := fun _ => _).
      rewrite <- (H7 _ f vi).
      subst f.
      hnf.

      rewrite !expg0.
      rewrite !mulg1.

      assert (forall {A} b (a e : A) (c d : A), (if b then a = e else c = d) <-> ((if b then a else c) = (if b then e else d))) by now intros ; destruct b.
      apply H8.

      rewrite !otf_fto.

      assert (forall {A : finType} (x y : A), (fto x = fto y) <-> (x = y)).
      {
        intros.
        (* apply boolp.propeqP. *)
        split.
        - intros.
          rewrite <- (otf_fto y).
          rewrite <- H9.
          rewrite otf_fto.
          reflexivity.
        - easy.
      }

      repeat (rewrite (proj2 (boolp.propeqP _ _) (pair_equal_spec _ _ _ _))).
      rewrite !(proj2 (boolp.propeqP _ _) (H9 (Message) _ _)).
      rewrite !(proj2 (boolp.propeqP _ _) (H9 (MyParam.Response) _ _)).
      repeat (rewrite (proj2 (boolp.propeqP _ _) (pair_equal_spec _ _ _ _))).

      rewrite <- (mulgA (h^+m)).
      rewrite mulgV.
      rewrite mulg1.
      rewrite !subKr.
      rewrite !addrK.

      now destruct vi.
    }
  Qed.

  (* Lemma proving that the output of the extractor defined for Schnorr's *)
  (* protocol is perfectly indistinguishable from real protocol execution. *)
  (*  *)
  Lemma extractor_success:
    ∀ LA A,
      ValidPackage LA [interface
                         #val #[ SOUNDNESS ] : chSoundness → 'bool
        ] A_export A →
      ɛ_soundness A = 0.
        intros LA A VA.
    apply: eq_rel_perf_ind_eq.
    2,3: apply fdisjoints0.
    simplify_eq_rel temp.
    destruct temp as [xhy [a [[e z] [e' z']]]].

    unfold Extractor.
    unfold Verify.
    destruct
      (otf xhy) as [[x h] y],
      (otf a) as [[[la1 lb1] la2] lb2],
      (otf z) as [[[lr1 ld1] lr2] ld2],
      (otf z') as [[[rr1 rd1] rr2] rd2].
    rewrite !otf_fto.

    destruct [&& _, _, _ & _] eqn:ando ; [ | now apply r_ret ; intros ; clear -H].
    apply (ssrbool.elimT and4P) in ando.
    destruct ando.
    repeat (apply (ssrbool.elimT andP) in H0 ; destruct H0).
    repeat (apply (ssrbool.elimT andP) in H1 ; destruct H1).
    apply reflection_nonsense in H0, H6, H5, H4, H3, H1, H9, H8, H7, H2.

    unfold R.

    apply f_equal with (f := fto) in H0, H1.
    rewrite !fto_otf in H0, H1.

    subst la1 lb1 la2 lb2.

    apply (proj1 (prod_swap_iff _ _ _ _)) in H9, H7, H8, H2.
    rewrite <- mulgA in H9, H7, H8, H2.

    rewrite !mulg_invg_sub in H9, H7, H8, H2.
    symmetry in H9, H7, H8, H2.
    apply (proj2 (prod_swap_iff _ _ _ _)) in H9, H7, H8, H2.
    rewrite !mulg_invg_left_sub in H9, H7, H8, H2.

    assert (ld1 - rd1 + (ld2 - rd2) <> 0).
    {
      subst e e'.
      clear -H.
      intros ?.
      assert (fto (ld1 + ld2) = fto (rd1 + rd2)).
      2:{
        rewrite H1 in H.
        rewrite eqxx in H.
        discriminate.
      }
      f_equal.
      apply /eqP.
      setoid_rewrite <- (subr_eq (ld1 + ld2) rd1 rd2).
      rewrite <- addrA.
      rewrite addrC.
      rewrite <- (add0r rd1).
      setoid_rewrite <- subr_eq.
      rewrite <- addrA.
      rewrite addrC.
      apply /eqP.
      apply H0.
    }

    assert ((ld1 - rd1) <> 0 \/ (ld2 - rd2) <> 0).
    {
      destruct (ld1 == rd1) eqn:is_eq;
        [ apply (ssrbool.elimT eqP) in is_eq
        | apply (ssrbool.elimF eqP) in is_eq ].
      - rewrite is_eq in H3.
        rewrite addrN in H3.
        rewrite add0r in H3.
        now right.
      - left.
        red ; intros.
        apply is_eq.
        now apply /eqP ; setoid_rewrite <- subr_eq0 ; apply /eqP.
    }

    apply r_ret ; split ; [ clear H5 ; symmetry | easy ].

    assert (if_bind : forall b (a : gT) (c d : 'F_q), (a ^+ (if b then c else d)) = (if b then a ^+ c else a ^+ d)) by now clear ; intros [].

    replace (g ^+ _) with (x ^+ (if ld1 - rd1 != 0 then (ld1 - rd1) / (ld1 - rd1) else (ld2 - rd2) / (ld2 - rd2))) by
      now destruct (ld1 - rd1 != 0) ; rewrite !trunc_pow !expgM ; [ rewrite H9 | rewrite H7 ].

    replace (h ^+ _) with ((y * g ^- (~~ (ld1 - rd1 != 0))) ^+ (if ld1 - rd1 != 0 then (ld1 - rd1) / (ld1 - rd1) else (ld2 - rd2) / (ld2 - rd2))).
    2:{
      destruct (ld1 - rd1 != 0) ; rewrite !trunc_pow !expgM ; [ rewrite H8 | rewrite H2 ].
      - rewrite expg0.
        rewrite invg1.
        rewrite mulg1.
        reflexivity.
      - rewrite expg1.
        reflexivity.
    }

    destruct (ld1 == rd1) eqn:is_zero;
      [ apply (ssrbool.elimT eqP) in is_zero
      | apply (ssrbool.elimF eqP) in is_zero ].
    {
      rewrite is_zero in H4 |- *.
      rewrite addrN in H4 |- *.
      rewrite eqxx.
      simpl (~~ true) ; hnf.

      destruct H4 ; [ contradiction | ].
      rewrite !div_cancel ; [ | assumption ..].

      rewrite <- !(mulgA _ g^-1).
      rewrite !mulVg.
      rewrite mulg1.

      now rewrite !eqxx.
    }
    {
      assert (ld1 - rd1 <> 0).
      {
        red ; intros.
        apply is_zero.
        now apply /eqP ; setoid_rewrite <- subr_eq0 ; apply /eqP.
      }
      rewrite (ssrbool.introF eqP H5).
      simpl (~~false) ; hnf.

      rewrite !div_cancel ; [ | assumption ..].

      rewrite expg0.
      rewrite invg1.
      rewrite !mulg1.

      now rewrite !eqxx.
    }
  Qed.

End OVN_or_proof.
