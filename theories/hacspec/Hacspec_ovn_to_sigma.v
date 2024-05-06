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
      exists x. now destruct (find_subdef _ _).
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
    clear -H_inj (* H_inv_inj η *) β.
    induction enum_subdef as [ | y ] ; [ reflexivity | ] ; simpl in *.
    rewrite (IHenum_subdef).
    f_equal.
    f_equal. (* remove nat_of_bool *)
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

  (* Definition word32_Finite (n : nat) : Finite (word n) := *)
  (*   finite_bijective *)
  (*     finite_to_word *)
  (*     word_to_finite finite_word_cancel word_finite_cancel *)
  (*     (Finite.fintype_isFinite_mixin (Finite.class (fintype_ordinal__canonical__fintype_Finite (Z.to_nat (modulus n)).-1.+1))). *)

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


End Misc.

Definition lower1 {A B : choice_type} (f : both A -> both B) : A -> B :=
  fun x => is_pure (f (ret_both x)).

Definition lower2 {A B C : choice_type} (f : both A -> both B -> both C) : A -> B -> C :=
  fun x y => is_pure (f (ret_both x) (ret_both y)).

Module Type GroupOperationProperties (OVN_impl : Hacspec_ovn.HacspecOVNParams).
  Include OVN_impl.
  Export OVN_impl.

  Axiom f_opp_by_sub : forall x y, f_sub x y ≈both f_add x (f_sub f_field_zero y).

  Axiom f_addA : forall x y z, f_add x (f_add y z) ≈both f_add (f_add x y) z.
  Axiom f_addC: forall x y, f_add x y ≈both f_add y x.
  (* Axiom f_mul_addr: right_distributive (f_mul) (f_add). *)
  (* Axiom f_mul_addl: left_distributive (f_mul) (f_add). *)
  Axiom f_add0z: forall x, f_add f_field_zero x ≈both x.
  Axiom f_addNz: forall x, f_add ((f_sub f_field_zero x) (* f_opp *)) x ≈both f_field_zero.

  (* Definition hacspec_group_type : Type := (Choice.sort (chElement v_G)). *)
  Axiom prod_pow_add_mul : forall x y z, f_prod (f_g_pow x) (f_pow (f_g_pow z) y) ≈both f_g_pow (f_add x (f_mul z y)).
  Axiom prod_pow_pow : forall h x a b, f_prod (f_pow h x) (f_pow (f_pow h a) b) ≈both f_pow h (f_add x (f_mul a b)).
  Axiom div_prod_cancel : forall x y, f_div (f_prod x y) y ≈both x.

  Axiom mul_comm : forall x y, f_mul x y ≈both f_mul y x.

  (* HB.instance Definition sort_group : hasChoice (Choice.sort (chElement v_G)) := _. (* Choice.clone (Choice.sort (chElement v_G)) _.  *) *)

  Axiom v_G_countable : Choice_isCountable (Choice.sort (chElement v_G)).
  Axiom v_G_isFinite : isFinite (Choice.sort (chElement v_G)).

  Axiom v_Z_countable : Choice_isCountable (Choice.sort (chElement v_G_t_Group.(f_Z))).
  Axiom v_Z_isFinite : isFinite (Choice.sort (chElement v_G_t_Group.(f_Z))).

  Axiom f_prodA : associative (lower2 f_prod).
  Axiom f_prod1 : associative (lower2 f_prod).
  Axiom f_prod_left_id : left_id (is_pure f_group_one) (lower2 f_prod).
  Axiom f_invK : involutive (lower1 f_inv).
  Axiom f_invM : {morph (lower1 f_inv)  : x y / (lower2 f_prod) x y >-> (lower2 f_prod)  y x}.

  Axiom v_Z_Field : GRing.Field (v_G_t_Group.(f_Z)).

  Axiom prod_inv_cancel : forall x, f_prod (f_inv x) x ≈both f_group_one.

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
    eapply both_eq_trans ; [ apply both_eq_fun_ext; apply (f_opp_by_sub _ _) | ].
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

  (* both v_Z is a field *)
  (* ChoiceEquality_both__canonical__GRing_Field *)
  Definition mul_group : isMulBaseGroup (v_G) :=
    {|
      isMulBaseGroup.mulg_subdef := lower2 f_prod;
      isMulBaseGroup.oneg_subdef := is_pure f_group_one;
      isMulBaseGroup.invg_subdef := lower1 f_inv;
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

  (* prime_cyclic *)

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

  (* Open Scope group_scope. *)

  Definition g_gen : ζ = <[g]> := v_G_g_gen.
  Definition prime_order : prime #[g] := v_G_prime_order.
End HacspecGroupParam.

Module Type OVN_schnorr_proof_preconditions (OVN_impl : Hacspec_ovn.HacspecOVNParams) (GOP : GroupOperationProperties OVN_impl) (SG : SecureGroup OVN_impl GOP).
  Include SG.

  Module HacspecGroup := HacspecGroupParam OVN_impl GOP SG.
  Module Schnorr := Schnorr HacspecGroup.

  Import Schnorr.MyParam.
  Import Schnorr.MyAlg.

  Import Schnorr.Sigma.Oracle.
  Import Schnorr.Sigma.

  (* Axiom StatementToGroup : *)
  (*   Statement -> v_G. *)

  Axiom WitnessToField :
    Witness -> v_G_t_Group.(f_Z).

  Axiom FieldToWitness :
    v_G_t_Group.(f_Z) -> Witness.

  Axiom WitnessToFieldCancel :
    forall x, WitnessToField (FieldToWitness x) = x.

  Axiom FieldToWitnessCancel :
    forall x, FieldToWitness (WitnessToField x) = x.

  Axiom WitnessToFieldAdd : forall x y, WitnessToField (Zp_add x y) = is_pure (f_add (ret_both (WitnessToField x)) (ret_both (WitnessToField y))).
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
  (* Include SG. *)

  Module HacspecGroup := HacspecGroupParam OVN_impl GOP SG.
  Include HacspecGroup.
  Export HacspecGroup.

  (* order of g *)
  Definition q : nat := #[HacspecGroup.g].

  Module MyParam <: SigmaProtocolParams.

    Definition Witness : finType :=  prod (Finite.clone _ 'Z_q) 'bool.
    Definition Statement : finType := gT.
    Definition Message : finType := prod (prod (prod (prod (prod (prod (prod gT gT) gT) gT) (Finite.clone _ 'Z_q)) (Finite.clone _ 'Z_q)) gT) gT.
    Definition Challenge : finType := Finite.clone _ 'Z_q.
    Definition Response : finType :=  (prod (prod (prod (Finite.clone _ 'Z_q) (Finite.clone _ 'Z_q)) (Finite.clone _ 'Z_q)) (Finite.clone _ 'Z_q)).
    Definition Transcript : finType :=
      prod (prod Message Challenge) Response.

    Definition w0 : Witness := 0.
    Definition e0 : Challenge := 0.
    Definition z0 : Response := 0.

    Definition R : Statement -> Witness -> bool :=
      (λ (h : Statement) (w : Witness), h == (HacspecGroup.g ^+ (fst w))).

    #[export] Instance positive_gT : Positive #|HacspecGroup.gT|.
    Proof.
      apply /card_gt0P. exists HacspecGroup.g. auto.
    Qed.

    #[export] Instance Bool_pos : Positive #|'bool|.
    Proof.
      rewrite card_bool. done.
    Defined.

    #[export] Instance Zq_pos : Positive #|Finite.clone _ 'Z_q|.
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

    Definition i_witness := #|Finite.clone _ 'Z_q|.

    Definition HIDING : nat := 0.
    Definition SOUNDNESS : nat := 1.

    Definition commit_loc : Location := (('fin #|Finite.clone _ 'Z_q| : choice_type); 2%N).

    Definition Sigma_locs : {fset Location} := fset [:: commit_loc].
    Definition Simulator_locs : {fset Location} := fset0.

    Definition Commit (h : choiceStatement) (xv : choiceWitness):
      code Sigma_locs [interface] choiceMessage :=
      {code
         w ← sample uniform i_witness ;;
         r ← sample uniform i_witness ;;
         d ← sample uniform i_witness ;;
         #put commit_loc := w ;;
         let '(xi, vi) := (otf xv) in
         let x := (g ^+ xi) in
         if vi
         then
           (
             let r1 := r in
             let d1 := d in

             let y := (otf h ^+ xi * g) in

             let a1 := (g ^+ (otf r1 : 'Z_q) * x ^+ (otf d1 : 'Z_q)) in
             let b1 := (otf h ^+ (otf r1 : 'Z_q) * y ^+ (otf d1 : 'Z_q)) in

             let a2 := (g ^+ (otf w : 'Z_q)) in
             let b2 := (otf h ^+ (otf w : 'Z_q)) in
             ret (fto (a1, b1, a2, b2, (otf r1 : 'Z_q), (otf d1 : 'Z_q), x, y)))
         else
           (let r2 := r in
            let d2 := d in

            let y := (otf h ^+ xi) in

            let a1 := (g ^+ (otf w : 'Z_q)) in
            let b1 := (otf h ^+ (otf w : 'Z_q)) in

            let a2 := (g ^+ (otf r2 : 'Z_q) * x ^+ (otf d2 : 'Z_q)) in
            let b2 := (otf h ^+ (otf r2 : 'Z_q) * (y * g^-1) ^+ (otf d2 : 'Z_q)) in

            ret (fto (a1, b1, a2, b2, (otf r2 : 'Z_q), (otf d2 : 'Z_q), x, y)))
      }.
    (* x, e *)
    (* a, e, z *)

    Definition Response (h : choiceStatement) (xv : choiceWitness) (a : choiceMessage) (c : choiceChallenge) :
      code Sigma_locs [interface] choiceResponse :=
      {code
         w ← get commit_loc ;;
         let '(xi, vi) := (otf xv) in
         let '(a1, b1, a2, b2, r, d, _, _) := (otf a) in
         if vi
         then
           (let d2 := otf c - d in
            let r2 := otf w - (xi * d2) in
            ret (fto (r, d, r2, d2)))
         else
           (let d1 := otf c - d in
            let r1 := otf w - (xi * d1) in
            ret (fto (r1, d1, r, d)))
      }.

    Program Definition Simulate (h : choiceStatement) (e : choiceChallenge) :
      code Simulator_locs [interface] choiceTranscript :=
      {code
         z ← sample uniform i_witness ;;
         ret _ (* (h, fto (g ^+ (otf z) * (otf h ^- (otf e))), e, z) *)
      }.
    Admit Obligations.

    Definition Verify (h : choiceStatement) (a : choiceMessage)
      (c : choiceChallenge) (z : choiceResponse) : choiceBool :=
          let '(a1, b1, a2, b2, _, _, x, y) := (otf a) in
          let '(r1, d1, r2, d2) := (otf z) in
          fto ((otf c == d1 + d2) &&
               (a1 == (g ^+ r1) * (x ^+ d1)) &&
               (b1 == (otf h ^+ r1) * (y ^+ d1)) &&
               (a2 == (g ^+ r2) * (x ^+ d2)) &&
               (b2 == (otf h ^+ r2) * ((y * (g ^-1)) ^+ d2))).

    Program Definition Extractor (h : choiceStatement) (a : choiceMessage)
      (e : choiceChallenge) (e' : choiceChallenge)
      (z : choiceResponse)  (z' : choiceResponse) : 'option choiceWitness :=
      Some _ (* (fto ((otf z - otf z') / (otf e - otf e'))) *).
    Admit Obligations.

    Definition KeyGen (xv : choiceWitness) :=
      let (xi, vi) := otf xv in
      fto (g ^+ xi).

  End MyAlg.

  Module Sigma := SigmaProtocol MyParam MyAlg.

  Import MyParam.
  Import MyAlg.

  Import Sigma.Oracle.
  Import Sigma.

  Axiom WitnessToField :
    'Z_q -> v_G_t_Group.(f_Z).

  Axiom FieldToWitness :
    v_G_t_Group.(f_Z) -> Finite.clone _ 'Z_q.

  Axiom WitnessToFieldCancel :
    forall x, WitnessToField (FieldToWitness x) = x.

  Axiom FieldToWitnessCancel :
    forall x, FieldToWitness (WitnessToField x) = x.

  (* Axiom WitnessToFieldAdd : forall x y, WitnessToField (Zp_add x y) = is_pure (f_add (ret_both (WitnessToField x)) (ret_both (WitnessToField y))). *)
  (* Axiom WitnessToFieldMul : forall x y, WitnessToField (Zp_mul x y) = is_pure (f_mul (ret_both (WitnessToField x)) (ret_both (WitnessToField y))). *)

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

  Axiom pow_field_to_witness :
    forall (h : both v_G) (b : both (v_G_t_Group.(f_Z))),
    ((is_pure h : gT) ^+ FieldToWitness (is_pure b)) = is_pure (f_pow h b).

  Axiom pow_witness_to_field :
    forall (h : gT) (b : 'Z_q),
      (h ^+ b = is_pure (f_pow (ret_both h) (ret_both (WitnessToField b)))).

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

  Definition run_code (ab : src (RUN, (choiceStatement × choiceWitness, choiceTranscript))) : code fset0 [interface
          #val #[ VERIFY ] : chTranscript → 'bool ;
          #val #[ RUN ] : chRelation → chTranscript
                                                                                                ] choiceTranscript :=
    {code (x ← op (RUN, ((chProd choiceStatement choiceWitness), choiceTranscript)) ⋅ ab ;;
              ret x) }.

  (* Transparent OVN.or_zkp. *)
  Transparent run.

  Definition or_run_post_cond :
    tgt (RUN, (choiceStatement × choiceWitness, choiceTranscript))
    → OVN.t_OrZKPCommit → Prop.
  Proof.
    intros [[[l1 x2] l10] x4] [[[[[[[[[[r1x r2y] r3a1] r4b1] r5a2] r6b2] r7c] r8d1] r9d2] r10r1] r11r2].
    destruct (otf x2) as [[[[[[[l2a1 l3b1] l4a2] l5b2] l6] l7] l8x] l9y] ; clear x2.
    destruct (otf x4) as [[[l11r1 l12d1] l13r2] l14d2] ; clear x4.
    cbn in *.
    (* refine (((otf l1) = _) /\ _). *)
    refine ((l2a1 = r3a1) /\ _).
    refine ((l3b1 = r4b1) /\ _).
    refine ((l4a2 = r5a2) /\ _).
    refine ((l5b2 = r6b2) /\ _).
    refine ((l8x = r1x) /\ _).
    refine ((l9y = r2y)).
    (* refine ((WitnessToField (otf l10) = r7) /\ _). *)
    (* refine ((WitnessToField l11 = r8) /\ _). *)
    (* refine ((WitnessToField l12 = r9) /\ _). *)
    (* refine ((WitnessToField l13 = r10) /\ _). *)
    (* refine ((WitnessToField l14 = r11)) *)
  Defined.

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
  (* Ltac compute_normal_form := *)
  (*   push_computation_down; simpl ; *)
  (*   rewrite both_equivalence_is_pure_eq ; *)
  (*   push_computation_up ; *)
  (*   rewrite <- both_equivalence_is_pure_eq. *)

  Ltac cancel_operations :=
    try apply both_eq_fun_ext ;
      try apply both_eq_fun_ext2 ;
      try (eapply both_eq_trans ; [ | apply both_eq_symmetry ; apply prod_pow_add_mul ]) ;
      try (eapply both_eq_trans ; [ | apply both_eq_symmetry ; apply add_sub_cancel ]) ;
      try (eapply both_eq_trans ; [ | apply both_eq_symmetry ; apply add_sub_cancel2 ]) ;
      try (eapply both_eq_trans ; [ | apply both_eq_symmetry ; apply prod_pow_pow ]) ;
      try (eapply both_eq_trans ; [ | apply both_eq_symmetry ; apply div_prod_cancel ]).

  Axiom pow_base : forall x, f_g_pow x ≈both f_pow (ret_both g) x.
  Axiom div_is_prod_inv : forall x y, f_div x y ≈both f_prod x (f_inv y).

 Lemma or_run_eq  (pre : precond) :
    forall (b : Witness) c,
      Some c = lookup_op RUN_interactive (RUN, ((chProd choiceStatement choiceWitness), choiceTranscript)) ->
      ⊢ ⦃ pre ⦄
        c (fto (HacspecGroup.g ^+ fst b), fto b)
        ≈
        wr ← sample uniform (2^32) ;;
        rr ← sample uniform (2^32) ;;
        dr ← sample uniform (2^32) ;;
        is_state (OVN.zkp_one_out_of_two
                    (ret_both (Hacspec_Lib_Pre.repr _ (Z.of_nat (nat_of_ord wr))))
                    (ret_both (Hacspec_Lib_Pre.repr _ (Z.of_nat (nat_of_ord rr))))
                    (ret_both (Hacspec_Lib_Pre.repr _ (Z.of_nat (nat_of_ord dr))))
                    (ret_both (HacspecGroup.g ^+ fst b))
                    (ret_both (WitnessToField (fst b)))
                    (ret_both (snd b : 'bool)))
          ⦃ fun '(x,_) '(y,_) => or_run_post_cond x y  ⦄.
  Proof.
    intros.

    cbn in H.
    destruct choice_type_eqP ; [ | discriminate ].
    destruct choice_type_eqP ; [ | discriminate ].
    rewrite cast_fun_K in H.
    clear e e1.
    inversion_clear H.

    unfold OVN.zkp_one_out_of_two.

    rewrite !otf_fto; unfold R; rewrite eqxx; unfold assertD.

    pose (bij_f := randomness_sample_is_bijective).
    set (f_rand := fun _ => _) in bij_f.

    eapply rsymmetry ; eapply r_uniform_bij with (f := fun x => _) ; [ apply bij_f | intros ] ; apply rsymmetry ; apply better_r.
    eapply rsymmetry ; eapply r_uniform_bij with (f := fun x => _) ; [ apply bij_f | intros ] ; apply rsymmetry ; apply better_r.
    eapply rsymmetry ; eapply r_uniform_bij with (f := fun x => _) ; [ apply bij_f | intros ] ; apply rsymmetry ; apply better_r.

    apply better_r_put_lhs.

    pose (f_rand_inner := fun (x : 'I_(2 ^ 32)) => (FieldToWitness
            (is_pure
               (f_random_field_elem (ret_both (Hacspec_Lib_Pre.repr _ (Z.of_nat (nat_of_ord x)))))))).
    progress repeat match goal with
    | [ |- context [ otf (f_rand ?x) ] ] =>
        replace (_ (f_rand x)) with (f_rand_inner x) by now rewrite otf_fto
      end.
    subst f_rand f_rand_inner.

    destruct b as [? []] eqn:bo.
    {
      simpl.
      rewrite otf_fto.
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
        -- now intros n ; rewrite FieldToWitnessCancel ; rewrite fto_otf.
        -- now intros n; rewrite otf_fto ; rewrite WitnessToFieldCancel.
      }
      intros.

      apply getr_set_lhs.
      apply make_pure ; simpl.

      apply r_ret.
      intros.

      unfold or_run_post_cond.
      rewrite !otf_fto.
      unfold lower2 ; simpl.

      set (f_random_field_elem _).
      set (f_random_field_elem _).
      set (f_random_field_elem _).

      repeat split ; clear ; simpl ; repeat setoid_rewrite <- expgnE ; push_down_sides.
      + rewrite pow_witness_to_field; rewrite WitnessToFieldCancel.
        rewrite pow_witness_to_field; rewrite WitnessToFieldCancel.
        rewrite !(proj1 both_equivalence_is_pure_eq (pow_base _)).
        rewrite pow_witness_to_field.
        now normalize_equation.
      + rewrite pow_witness_to_field; rewrite WitnessToFieldCancel.
        rewrite (pow_witness_to_field (is_pure (f_prod _ _))) ; rewrite WitnessToFieldCancel.
        rewrite !pow_witness_to_field.
        now push_down_sides.
      + rewrite pow_witness_to_field; rewrite WitnessToFieldCancel.
        now rewrite !(proj1 both_equivalence_is_pure_eq (pow_base _)).
      + now rewrite pow_witness_to_field; rewrite WitnessToFieldCancel.
      + rewrite pow_witness_to_field.
        now rewrite !(proj1 both_equivalence_is_pure_eq (pow_base _)).
      + now rewrite pow_witness_to_field.
    }
    {
      Opaque Build_t_OrZKPCommit.
      simpl.
      rewrite otf_fto.
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
        -- now intros n ; rewrite FieldToWitnessCancel ; rewrite fto_otf.
        -- now intros n; rewrite otf_fto ; rewrite WitnessToFieldCancel.
      }
      intros.

      apply getr_set_lhs.
      apply make_pure ; simpl.

      apply r_ret.
      intros.

      unfold or_run_post_cond.
      rewrite !otf_fto.
      unfold lower2 ; simpl.

      set (f_random_field_elem _).
      set (f_random_field_elem _).
      set (f_random_field_elem _).

      repeat split ; clear ; simpl ; repeat setoid_rewrite <- expgnE ; push_down_sides.
      + rewrite pow_witness_to_field; rewrite WitnessToFieldCancel.
        now rewrite !(proj1 both_equivalence_is_pure_eq (pow_base _)).
      + now rewrite pow_witness_to_field; rewrite WitnessToFieldCancel.
      + rewrite pow_witness_to_field; rewrite WitnessToFieldCancel.
        rewrite pow_witness_to_field; rewrite WitnessToFieldCancel.
        rewrite !(proj1 both_equivalence_is_pure_eq (pow_base _)).
        rewrite pow_witness_to_field.
        now normalize_equation.
      + rewrite pow_witness_to_field; rewrite WitnessToFieldCancel.
        repeat progress f_equal.
        rewrite pow_witness_to_field.
        unfold lower1.
        rewrite (proj1 both_equivalence_is_pure_eq (div_is_prod_inv _ _)).
        push_down_sides.
        now rewrite pow_witness_to_field; rewrite WitnessToFieldCancel.
      + rewrite pow_witness_to_field.
        now rewrite !(proj1 both_equivalence_is_pure_eq (pow_base _)).
      + now rewrite pow_witness_to_field.
    }
    Time Qed.
End OVN_or_proof.


(*** Example (Z89) *)

From OVN Require Import Hacspec_ovn_Ovn_z_89_.

Module Z89_impl <: HacspecOVNParams.
  #[local] Open Scope hacspec_scope.

  Definition v_G : choice_type := t_g_z_89_.
  Transparent v_G.
  Hint Unfold v_G.

  Definition n : both uint_size := ret_both 55.

  Instance Serializable_chFin (n : positive) : Serializable.Serializable (chFin n).
  Proof.
    destruct n as [[] ?] ; [ discriminate | ].
    refine (serialize_by_other (fun x => nat_of_ord x) (fun x => inord x) (inord_val)).
    apply Serializable.nat_serializable.
  Defined.

  Instance v_Z_t_Field : t_Field _ := t_z_89__t_Field.
  (* Instance t_Eq_from_eqType (A : eqType) : t_Eq A := *)
  (*   {| Hacspec_Lib_Comparable.eqb := fun x y => x == y; eqb_leibniz := fun x y => RelationClasses.symmetry (rwP eqP) |}. *)
  (* Instance v_G_t_Eq : t_Eq v_G := _. *)

  Instance v_G_t_Copy : t_Copy v_G := _.
  Instance v_G_t_PartialEq : t_PartialEq v_G v_G := _.
  Instance v_G_t_Clone : t_Clone v_G := _.
  Instance v_G_t_Serialize : t_Serialize v_G := _.
  Instance v_G_t_Eq : t_Eq v_G := _.

  Instance v_G_t_Group : t_Group v_G := t_g_z_89__t_Group.

  Definition v_A : choice_type := 'nat.
  Instance v_A_t_Sized : t_Sized v_A. Admitted.
  Definition v_A_t_HasActions : t_HasActions v_A.
  Proof.
    constructor.
    refine (ret_both (0%nat : 'nat)).
  Defined.

  Instance f_field_type_Serializable : Serializable.Serializable v_G_t_Group.(f_Z). Admitted.
  Instance f_group_type_Serializable : Serializable.Serializable v_G. Admitted.

End Z89_impl.

Module Z89_group_operations <: GroupOperationProperties Z89_impl.
  Include Z89_impl.

  Ltac unfold_both_eq :=
    intros ;
    apply both_equivalence_is_pure_eq ;
    cbn ;
    repeat (try unfold lift2_both at 1 ; try unfold lift1_both at 1 ; simpl).

(* (a + b) + c = a + (b + c) *)

  Corollary both_equivalence_bind_comm : forall {A} {a : both A} {b : both A} {f : A -> A -> both A},
      bind_both a (fun x =>
      bind_both b (fun y => f x y))
        ≈both
      bind_both b (fun y => bind_both a (fun x => f x y))
      .
  Proof.
    intros.
    cbn.
    unfold both_equivalence.
    now rewrite <- both_pure.
  Qed.

  Lemma f_opp_by_sub : forall x y, f_sub x y ≈both f_add x (f_sub f_field_zero y).
  Proof. Admitted.
  (*   intros. *)
  (*   simpl. *)

  (*   repeat unfold Build_t_z_89_ at 1. *)

  (*   repeat unfold f_z_val at 1. *)
  (*   repeat unfold ".-" at 1. *)
  (*   repeat unfold ".+" at 1. *)
  (*   repeat unfold ".%" at 1. *)
  (*   unfold_both_eq. *)

  (*   Set Printing Coercions. *)

  (*   set (x' := is_pure _). *)
  (*   set (y' := is_pure _). *)

  (*   set (int_xO _); change (Hacspec_Lib_Pre.int_sub (int_xI s) _) with (@int_xO U8 s); subst s. *)
  (*   set (n88 := int_xO _). *)

  (*   replace (wrepr U8 0) with (Hacspec_Lib_Pre.zero (WS := U8)). *)
  (*   2: admit. *)
  (*   rewrite add_zero_l. *)



  (*   rewrite !add_repr. *)


  (*   replace (Hacspec_Lib_Pre.int_sub 89 1) with *)
  (*     (88). *)

  (*   unfold Hacspec_Lib_Pre.int_sub. *)
  (*   unfold Hacspec_Lib_Pre.int_add. *)
  (*   unfold Hacspec_Lib_Pre.int_mod. *)

  (*   (* unfold wrepr. *) *)
  (*   (* set (unsigned _ mod _) ; fold (wrepr U8 z) ; subst z. *) *)
  (*   (* set (unsigned _ mod _) at 2 ; fold (wrepr U8 z) ; subst z. *) *)

  (*   assert (forall x, wrepr U8 (urepr x) = x) by apply ureprK. *)

  (*   unfold unsigned. *)
  (*   unfold sub_word. *)

  (*   (* unfold wrepr. *) *)
  (*   change (nat_of_wsize U8) with (wsize_size_minus_1 U8).+1. *)
  (*   set (z := urepr _ - _) ; fold (wrepr U8 z) ; subst z. *)
  (*   set (z := urepr _ - _) at 2 ; fold (wrepr U8 z) ; subst z. *)
  (*   set (z := urepr _ - _) at 3 ; fold (wrepr U8 z) ; subst z. *)
  (*   set (z := urepr _ - _) at 4 ; fold (wrepr U8 z) ; subst z. *)
  (*   set (z := urepr _ - _) at 5 ; fold (wrepr U8 z) ; subst z. *)
  (*   set (z := urepr _ - _) at 6 ; fold (wrepr U8 z) ; subst z. *)
  (*   set (z := urepr _ - _) at 7 ; fold (wrepr U8 z) ; subst z. *)

  (*   set (int_xO _); change (urepr (int_xI s) - _) with (urepr (@int_xO U8 s)); subst s. *)
  (*   set (n88 := int_xO _). *)

  (*   unfold add_word. *)
  (*   set (z := urepr _ + _) ; fold (wrepr U8 z) ; subst z. *)
  (*   set (z := urepr _ + _) at 2 ; fold (wrepr U8 z) ; subst z. *)
  (*   set (z := urepr _ + _) at 3 ; fold (wrepr U8 z) ; subst z. *)
  (*   rewrite !H. *)

  (*   rewrite wrepr_add. *)
  (*   rewrite !H. *)

  (*   rewrite wrepr_sub. *)
  (*   rewrite !H. *)

  (*   set (urepr _). *)
  (*   set (urepr _). *)

  (* Admitted. *)

  Lemma f_addA : forall x y z, f_add x (f_add y z) ≈both f_add (f_add x y) z.
  Admitted.
  (* Proof. unfold_both_eq. now rewrite Zp_addA. Qed. *)

  Lemma f_addC: forall x y, f_add x y ≈both f_add y x.
  Proof. Admitted.
    (* Proof. unfold_both_eq. now rewrite Zp_addC. Qed. *)
  (* Axiom f_mul_addr: right_distributive (f_mul) (f_add). *)
  (* Axiom f_mul_addl: left_distributive (f_mul) (f_add). *)
  Lemma f_add0z: forall x, f_add f_field_zero x ≈both x.
  Proof. Admitted.
  (* Proof. *)
  (*   unfold_both_eq. *)
  (*   replace (inord _) with (Zp0 (p' := 88 (* 89 *))) by now apply ord_inj ; rewrite inordK. *)
  (*   now rewrite Zp_add0z. *)
  (* Qed. *)

  Lemma f_addNz: forall x, f_add ((f_sub f_field_zero x) (* f_opp *)) x ≈both f_field_zero.
  Proof. Admitted.
  (* Proof. *)
  (*   unfold_both_eq. *)
  (*   replace (inord _) with (Zp0 (p' := (* 89 *) 88)) by now apply ord_inj ; rewrite inordK. *)
  (*   rewrite Zp_add0z. *)
  (*   now rewrite Zp_addNz. *)
  (* Qed. *)

  (* Lemma nat_of_ord_helper : *)
  (*   (forall (a b : v_G), (nat_of_ord a * nat_of_ord b)%nat = nat_of_ord (a * b)). *)
  (* Admitted. *)

  Definition prod_pow_add_mul : ∀ x y z : both f_Z, f_prod (f_g_pow x) (f_pow (f_g_pow z) y) ≈both f_g_pow (f_add x (f_mul z y)).
  Proof. Admitted.
  (* Proof. *)
  (*   unfold_both_eq ; repeat setoid_rewrite <- expgnE. *)

  (*   (* unfold Zp_mul. *) *)
  (*   (* rewrite nat_of_ord_helper. *) *)

  (*   (* rewrite modZp. *) *)

  (*   unfold expgn at 1, expgn_rec. *)
  (*   unfold Zp_mul. *)
  (*   unfold expgn at 1, expgn_rec. *)
  (* Admitted. *)

  Definition prod_pow_pow : forall h x a b, f_prod (f_pow h x) (f_pow (f_pow h a) b) ≈both f_pow h (f_add x (f_mul a b)).
  Proof. Admitted.
  (*   intros. *)
  (*   unfold_both_eq ; repeat setoid_rewrite <- expgnE. *)
  (*   Set Printing Coercions. *)
  (*   (* unfold Zp_mul. *) *)

  (*   set (h' := is_pure (both_prog _)). *)
  (*   set (x' := nat_of_ord _). *)
  (*   set (a' := nat_of_ord _). *)
  (*   set (b' := nat_of_ord _). *)

  (*   unfold Zp_mul. *)
  (*   rewrite nat_of_ord_helper. *)
  (*   rewrite valZpK. *)

  (*   rewrite <- expgM. *)
  (*   rewrite <- expgD. *)

  (*   (* f_equal. *) *)

  (*   rewrite <- modnDm. *)
  (*   rewrite modn_mod. *)
  (*   rewrite modnDm. *)

  (*   rewrite expg_mod ; [reflexivity | ]. *)

  (*   apply ord_inj. *)
  (*   simpl. *)

  (*   destruct h' ; simpl. *)
  (*   repeat (discriminate || (destruct m as [ | m ] ; [ reflexivity | ])). (* SLOW *) *)
  (* Qed. *)

  Definition div_prod_cancel : forall x y, f_div (f_prod x y) y ≈both x. Admitted.

  Definition mul_comm : forall x y, f_mul x y ≈both f_mul y x. Admitted.

  (* HB.instance Definition sort_group : hasChoice (Choice.sort (chElement v_G)) := _. (* Choice.clone (Choice.sort (chElement v_G)) _.  *) *)

  (* HB.instance Definition Choice_choice : Choice v_G := _. *)
  Definition v_G_countable : Choice_isCountable (Choice.sort (chElement v_G)) := [ Countable of v_G by <: ].
  Definition v_G_isFinite : isFinite (Choice.sort (chElement v_G)).
  Proof. Admitted.
    (* [ Finite of v_G by <: ]. *)

  Definition v_Z_countable : Choice_isCountable (Choice.sort (chElement v_G_t_Group.(f_Z))) := [ Countable of v_G_t_Group.(f_Z) by <: ].
  Definition v_Z_isFinite : isFinite (Choice.sort (chElement v_G_t_Group.(f_Z))).
  Proof. Admitted.
      (* [ Finite of v_G_t_Group.(f_Z) by <: ]. *)

  Definition f_prodA : associative (lower2 f_prod). Admitted.
  Definition f_prod1 : associative (lower2 f_prod). Admitted.
  Definition f_prod_left_id : left_id (is_pure f_group_one) (lower2 f_prod). Admitted.
  Definition f_invK : involutive (lower1 f_inv). Admitted.
  Definition f_invM : {morph (lower1 f_inv)  : x y / (lower2 f_prod) x y >-> (lower2 f_prod)  y x}. Admitted.

  Definition v_Z_Field : GRing.Field (v_G_t_Group.(f_Z)). Admitted.

  Definition prod_inv_cancel : forall x, f_prod (f_inv x) x ≈both f_group_one. Admitted.

End Z89_group_operations.

Module Z89_secure_group <: SecureGroup Z89_impl Z89_group_operations.
  Module Group := HacspecGroup Z89_impl Z89_group_operations.
  Include Group.

  (* Lemma prime_q : prime (nat_of_ord (is_pure f_q)). *)
  (* Proof. *)
  (*   rewrite inordK. *)
  (*   simpl. *)
  (* Qed. *)

  (* Lemma prime_g : prime (nat_of_ord (is_pure f_g)). *)
  (* Proof. now rewrite inordK. Qed. *)

  Lemma lower2_cancel_lift2_both : forall {A B C : choice_type} (f : A -> B -> C) x y, lower2 (lift2_both f) x y = f x y.
  Proof. reflexivity. Qed.

  Lemma v_G_prime_order : prime #[(is_pure f_g : v_G_is_group)].
    simpl.
  Admitted.
  (* Proof. *)
  (*   intros. *)
  (*   simpl. *)
  (*   (* replace (inord 1) with (inord 89). *) *)
  (*   (* pose (order_Zp1 88). *) *)
  (*   (* unfold Zp1 in e. *) *)
  (*   epose order1. *)
  (*   Set Printing All. *)
  (*   replace (inZp _) with (inord (n' := 88) 1) in e. *)
  (*   - rewrite order1. *)
  (*     rewrite order1 in e. *)
  (*     Set Printing All. *)

  (*     unfold v_G_is_group. *)
  (*     simpl. *)
  (*     unfold order. *)
  (*     simpl. *)
  (*     rewrite e. *)
  (*     easy. *)
  (*   - apply ord_inj; now rewrite inordK. *)
  (* Qed. *)

  Lemma v_G_g_gen : [set : v_G_is_group] = <[ is_pure f_g : v_G_is_group]>. Admitted.
End Z89_secure_group.

(* Module OVN_schnorr_proof_params_Z89 <: OVN_schnorr_proof_preconditions Z89_impl Z89_group_operations Z89_secure_group. *)
(*   Include Z89_secure_group. *)

(*   Module HacspecGroup := HacspecGroupParam Z89_impl Z89_group_operations Z89_secure_group. *)
(*   Module Schnorr := Schnorr HacspecGroup. *)

(*   Import Schnorr.MyParam. *)
(*   Import Schnorr.MyAlg. *)

(*   Import Schnorr.Sigma.Oracle. *)
(*   Import Schnorr.Sigma. *)

(*   Definition StatementToGroup : Statement -> v_G := id. *)

(*   (* Lemma group_size : #[HacspecGroup.g].-2.+2 = 89. *) *)
(*   (* Proof. *) *)
(*   (*   rewrite totient_gen. *) *)
(*   (*   epose (@generator_order v_G_is_group (is_pure f_g) (1)). *) *)
(*   (*   rewrite e. *) *)
(*   (*   2:{ *) *)
(*   (*     simpl. *) *)
(*   (*     pose (cycle_generator). *) *)
(*   (*     unfold generator. *) *)
(*   (*     reflexivity. *) *)
(*   (*   epose (@generator_cycle v_G_is_group (is_pure f_g)). *) *)
(*   (*   simpl in i. *) *)
(*   (*   unfold generator in i. *) *)

(*   (*   assert (HacspecGroup.g = inZp 1). *) *)
(*   (*   { *) *)
(*   (*     unfold inZp. *) *)
(*   (*     unfold HacspecGroup.g. *) *)
(*   (*     simpl. *) *)
(*   (*     unfold inord. *) *)
(*   (*     unfold ord0. *) *)
(*   (*     unfold insubd. *) *)
(*   (*     unfold insub. *) *)
(*   (*     unfold odflt. *) *)
(*   (*     unfold oapp. *) *)
(*   (*     unfold sub. *) *)
(*   (*     destruct idP. *) *)
(*   (*     - simpl. *) *)


(*   (*     simpl. *) *)

(*   (*     simpl. *) *)


(*   (*   cbn. *) *)
(*   (*   rewrite card_Aut_cycle. *) *)
(*   (*   reflexivity. *) *)

(*   Lemma inord_is_inZp : forall {n} x, (x < n.+1)%nat -> inord (n' := n) x = inZp (p' := n) x. *)
(*   Proof. *)
(*     intros n x H. *)
(*     rewrite <- (inordK (m := x) (n' := n)) ; [ | assumption ]. *)
(*     rewrite (valZpK (inord (n' := n) x)). *)
(*     rewrite inord_val. *)
(*     reflexivity. *)
(*   Qed. *)

(*   Definition WitnessToField : Witness -> v_G_t_Group.(f_Z) := fun x => mkword _ (Z.of_nat ((nat_of_ord x) %% Schnorr.q)). *)
(*   Definition FieldToWitness : v_G_t_Group.(f_Z) -> Witness := fun x => inord ((Z.to_nat (unsigned x)) %% Schnorr.q). *)

(*   Lemma group_size_is_q : (Schnorr.q = Z.to_nat (unsigned (is_pure (HacspecGroup.v_G_t_Group.(f_Z_t_Field).(f_q))))). *)
(*   Admitted. *)


(*   Lemma in_equality : forall v u, is_true (0 <= v < u)%R <-> is_true (Z.to_nat v < Z.to_nat u)%N. *)
(*   Admitted. *)

(*   Lemma WitnessToFieldCancel : forall x, WitnessToField (FieldToWitness x) = x. *)
(*   Proof. *)
(*     intros. *)
(*     simpl in *. *)

(*     destruct x. *)
(*     unfold WitnessToField, FieldToWitness. *)
(*     simpl. *)
(*     rewrite !inordK. *)
(*     2:{ *)
(*       simpl. *)
(*       rewrite Schnorr.order_ge1. *)
(*       simpl. *)
(*       Set Printing Coercions. *)
(*       unfold unsigned. *)
(*       unfold urepr. *)
(*       simpl. *)

(*       apply ltn_pmod. *)
(*       now rewrite group_size_is_q. *)
(*     } *)
(*     apply word_ext. *)
(*     rewrite modn_mod. *)
(*     rewrite modnZE ; [ |  now rewrite group_size_is_q]. *)
(*     rewrite Z2Nat.id ; [ | now destruct toword ]. *)
(*     cbn. *)

(*     rewrite group_size_is_q. *)
(*     cbn. *)
(*     rewrite Z2Nat.id ; [ | easy ]. *)
(*     unfold Build_t_z_89_ at 1. *)
(*     simpl. *)
(*     set (Z.pos _). *)
(*     rewrite (Z.mod_small z). *)
(*     - rewrite Z.mod_small. *)



(*     (* assert (forall p b x, Z.pos p <= b -> x mod (Z.pos p) mod b = x mod (Z.pos p)). *) *)
(*     (* { *) *)
(*     (*   intros. *) *)
(*     (*   rewrite Z.mod_small_iff. *) *)

(*     (*   epose (Znumtheory.Zmod_div_mod b (Z.pos p) xa). *) *)
(*     (*   rewrite <- e. *) *)

(*     (*   induction p. *) *)
(*     (*   - *) *)
(*     (*     cbn. *) *)
(*   Admitted. *)



(*   Lemma FieldToWitnessCancel : *)
(*     forall x, FieldToWitness (WitnessToField x) = x. *)
(*   Proof. *)
(*     intros. *)
(*     unfold WitnessToField, FieldToWitness. *)
(*     unfold unsigned. *)
(*     rewrite mkwordK. *)
(*     simpl. *)
(*     rewrite Zmod_small. *)
(*     2: { *)
(*       destruct x. *)
(*       cbn. *)
(*       rewrite Schnorr.order_ge1 in i. *)

(*     (* rewrite Nat2Z.id. *) *)
(*   (*   now rewrite inord_val. *) *)
(*       (* Qed. *) *)
(*       Admitted. *)

(*   Axiom WitnessToFieldAdd : forall x y, WitnessToField (Zp_add x y) = is_pure (f_add (ret_both (WitnessToField x)) (ret_both (WitnessToField y))). *)
(*   Axiom WitnessToFieldMul : forall x y, WitnessToField (Zp_mul x y) = is_pure (f_mul (ret_both (WitnessToField x)) (ret_both (WitnessToField y))). *)

(*   Axiom randomness_sample_is_bijective : *)
(*     bijective *)
(*     (λ x : 'I_(2 ^ 32), *)
(*        fto *)
(*          (FieldToWitness *)
(*             (is_pure *)
(*                (f_random_field_elem (ret_both (Hacspec_Lib_Pre.repr _ (Z.of_nat (nat_of_ord x)))))))). *)

(*   Axiom hash_is_psudorandom : *)
(*     forall {A B} i (H : Positive i) f pre post (c0 : _ -> raw_code A) (c1 : _ -> raw_code B) l, *)
(*             bijective f *)
(*             → (∀ x1 : Arit (uniform i), ⊢ ⦃ pre ⦄ c0 x1 ≈ c1 (f x1) ⦃ post ⦄) -> *)
(*             ⊢ ⦃ pre ⦄ *)
(*           e ← sample uniform i ;; *)
(*           c0 e ≈ *)
(*           x ← is_state *)
(*             (f_hash (t_Group := v_G_t_Group) *)
(*                (impl__into_vec *)
(*                   (unsize *)
(*                      (box_new *)
(*                         (array_from_list l))))) ;; c1 x ⦃ post ⦄. *)

(*   Axiom conversion_is_true : *)
(*     forall (b : both (v_G_t_Group.(f_Z))), StatementToGroup *)
(*     (HacspecGroup.g ^+ FieldToWitness (is_pure b)) = is_pure (f_g_pow b). *)

(* End OVN_schnorr_proof_params_Z89. *)

(* Module OVN_schnorr_proof_Z89 := OVN_schnorr_proof Z89_impl Z89_group_operations . *)

(* Schnorr_Z89.Sigma.RUN_interactive *)

(* Import Schnorr_Z89.Sigma. *)
(* Import Schnorr_Z89.MyAlg. *)
(* Import Schnorr_Z89.Sigma.Oracle. *)

(* Import Z89_impl. *)
