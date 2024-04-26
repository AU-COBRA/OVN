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

  Definition word32_Finite (n : nat) : Finite (word n) :=
    finite_bijective
      finite_to_word
      word_to_finite finite_word_cancel word_finite_cancel
      (Finite.fintype_isFinite_mixin (Finite.class (fintype_ordinal__canonical__fintype_Finite (Z.to_nat (modulus n)).-1.+1))).

End Misc.

Definition lower1 {A B : choice_type} (f : both A -> both B) : A -> B :=
  fun x => is_pure (f (ret_both x)).

Definition lower2 {A B C : choice_type} (f : both A -> both B -> both C) : A -> B -> C :=
  fun x y => is_pure (f (ret_both x) (ret_both y)).

Module Type GroupOperationProperties (OVN_impl : Hacspec_ovn.HacspecOVNParams).
  Import OVN_impl.

  Axiom add_sub_cancel : forall a b, f_add a (f_sub b a) ≈both b.
  Axiom add_sub_cancel2 : forall a b, f_add (f_sub b a) a ≈both b.
  (* Definition hacspec_group_type : Type := (Choice.sort (chElement v_G)). *)
  Axiom prod_pow_add_mul : forall x y z, f_prod (f_g_pow x) (f_pow (f_g_pow z) y) ≈both f_g_pow (f_add x (f_mul z y)).
  Axiom prod_pow_pow : forall h x a b, f_prod (f_pow h x) (f_pow (f_pow h a) b) ≈both f_pow h (f_add x (f_mul a b)).
  Axiom div_prod_cancel : forall x y, f_div (f_prod x y) y ≈both x.

  Axiom mul_comm : forall x y, f_mul x y ≈both f_mul y x.

  (* HB.instance Definition sort_group : hasChoice (Choice.sort (chElement v_G)) := _. (* Choice.clone (Choice.sort (chElement v_G)) _.  *) *)

  Axiom both_v_G_choice : hasChoice.axioms_ (both v_G).
  Axiom both_v_G_countable : Choice_isCountable (both v_G).
  Axiom both_v_G_hasDecEq : hasDecEq (both v_G).
  Axiom both_v_G_isFinite : isFinite.axioms_ (both v_G) both_v_G_hasDecEq.

  Axiom v_G_countable : Choice_isCountable (Choice.sort (chElement v_G)).
  Axiom v_G_isFinite : isFinite (Choice.sort (chElement v_G)).

  Axiom both_v_Z_choice : hasChoice.axioms_ (both v_Z).
  Axiom both_v_Z_countable : Choice_isCountable (both v_Z).
  Axiom both_v_Z_hasDecEq : hasDecEq (both v_Z).
  Axiom both_v_Z_isFinite : isFinite.axioms_ (both v_Z) both_v_Z_hasDecEq.

  Axiom v_Z_countable : Choice_isCountable (Choice.sort (chElement v_Z)).
  Axiom v_Z_isFinite : isFinite (Choice.sort (chElement v_Z)).

  Axiom f_prodA : associative (lower2 f_prod).
  Axiom f_prod1 : associative (lower2 f_prod).
  Axiom f_prod_left_id : left_id (is_pure f_group_one) (lower2 f_prod).
  Axiom f_invK : involutive (lower1 f_inv).
  Axiom f_invM : {morph (lower1 f_inv)  : x y / (lower2 f_prod) x y >-> (lower2 f_prod)  y x}.

  Axiom v_Z_Field : GRing.Field (v_Z).

  Axiom prod_inv_cancel : forall x, f_prod (f_inv x) x ≈both f_group_one.

End GroupOperationProperties.

Module HacspecGroup (OVN_impl : Hacspec_ovn.HacspecOVNParams) (GOP : GroupOperationProperties OVN_impl).
  Import OVN_impl.
  Import GOP.

  Definition both_v_G_Finite : Finite (both v_G) :=
    {|
      Finite.choice_hasChoice_mixin := both_v_G_choice;
      Finite.choice_Choice_isCountable_mixin := both_v_G_countable;
      Finite.eqtype_hasDecEq_mixin := both_v_G_hasDecEq;
      Finite.fintype_isFinite_mixin := both_v_G_isFinite
    |}.

  Definition v_G_Finite : Finite (Choice.sort (chElement v_G)) :=
    {|
      Finite.choice_hasChoice_mixin := Choice.choice_hasChoice_mixin (Choice.class v_G);
      Finite.choice_Choice_isCountable_mixin := v_G_countable;
      Finite.eqtype_hasDecEq_mixin := Choice.eqtype_hasDecEq_mixin (Choice.class v_G);
      Finite.fintype_isFinite_mixin := v_G_isFinite
    |}.
  
  Definition both_v_Z_Finite : Finite (both v_Z) :=
    {|
      Finite.choice_hasChoice_mixin := both_v_Z_choice;
      Finite.choice_Choice_isCountable_mixin := both_v_Z_countable;
      Finite.eqtype_hasDecEq_mixin := both_v_Z_hasDecEq;
      Finite.fintype_isFinite_mixin := both_v_Z_isFinite
    |}.

  Definition v_Z_Finite : Finite (Choice.sort (chElement v_Z)) :=
    {|
      Finite.choice_hasChoice_mixin := Choice.choice_hasChoice_mixin (Choice.class v_Z);
      Finite.choice_Choice_isCountable_mixin := v_Z_countable;
      Finite.eqtype_hasDecEq_mixin := Choice.eqtype_hasDecEq_mixin (Choice.class v_Z);
      Finite.fintype_isFinite_mixin := v_Z_isFinite
    |}.


  Definition both_f_field_finType : finType := Finite.Pack both_v_Z_Finite.
  Definition both_f_group_finType : finType := Finite.Pack both_v_G_Finite.

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

  #[export] Definition v_G_BaseFinGroup : baseFinGroupType :=
    BaseFinGroup.Pack
      {|
        BaseFinGroup.fingroup_isMulBaseGroup_mixin := mul_group;
        BaseFinGroup.choice_hasChoice_mixin := v_G_Finite;
        BaseFinGroup.choice_Choice_isCountable_mixin := v_G_Finite;
        BaseFinGroup.eqtype_hasDecEq_mixin := v_G_Finite;
        BaseFinGroup.fintype_isFinite_mixin := v_G_Finite
      |}.
  #[export] Lemma inv_mul_inverse : left_inverse (T := v_G_BaseFinGroup) (R := v_G) (oneg v_G_BaseFinGroup) invg mulg.
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
  Import OVN_impl.
  Import GOP.
  Module Group := HacspecGroup OVN_impl GOP.
  Export Group.
  Import Group.

  Axiom v_G_prime_order : prime #[is_pure f_g : v_G_is_group].
  Axiom v_G_g_gen : [set : v_G_is_group] = <[is_pure f_g : v_G_is_group]>.
End SecureGroup.

Module HacspecGroupParam (OVN_impl : Hacspec_ovn.HacspecOVNParams) (GOP : GroupOperationProperties OVN_impl) (SG : SecureGroup OVN_impl GOP) <: GroupParam.
  Import OVN_impl.
  Import GOP.
  Import SG.

  Definition gT : finGroupType := v_G_is_group.
  Definition ζ : {set gT} := [set : gT].
  Definition g :  gT := is_pure f_g.

  (* Open Scope group_scope. *)

  Definition prime_order : prime #[g] := v_G_prime_order.
  Definition g_gen : ζ = <[g]> := v_G_g_gen.
End HacspecGroupParam.

Module Type OVN_schnorr_proof (OVN_impl : Hacspec_ovn.HacspecOVNParams) (GOP : GroupOperationProperties OVN_impl) (SG : SecureGroup OVN_impl GOP).
  Module OVN := HacspecOVN OVN_impl.

  Module HacspecGroup := HacspecGroupParam OVN_impl GOP SG.
  Module Schnorr := Schnorr HacspecGroup.

  Import Schnorr.MyParam.
  Import Schnorr.MyAlg.

  Import Schnorr.Sigma.Oracle.
  Import Schnorr.Sigma.

  Axiom StatementToGroup :
    Statement -> OVN_impl.v_G.
 
  Axiom WitnessToField :
    Witness -> OVN_impl.v_G_t_Group.(f_Z).

  Axiom FieldToWitness :
    OVN_impl.v_G_t_Group.(f_Z) -> Witness.

  Axiom randomness_sample_is_bijective :
    bijective
    (λ x : 'I_(2 ^ 32),
       fto
         (FieldToWitness
            (is_pure
               (f_random_field_elem (ret_both (Hacspec_Lib_Pre.repr _ (Z.of_nat (nat_of_ord x)))))))).

  Axiom conversion_is_true :
    forall (b : both (OVN_impl.v_G_t_Group.(f_Z))), StatementToGroup
    (HacspecGroup.g ^+ FieldToWitness (is_pure b)) = is_pure (f_g_pow b).

  
  Transparent OVN.schnorr_zkp.
 
  Definition run_code (ab : src (RUN, (choiceStatement × choiceWitness, choiceTranscript))) : code fset0 [interface
          #val #[ VERIFY ] : chTranscript → 'bool ;
          #val #[ RUN ] : chRelation → chTranscript
                                                                                                ] choiceTranscript :=
    {code (x ← op (RUN, ((chProd choiceStatement choiceWitness), choiceTranscript)) ⋅ ab ;;
              ret x) }.

  Transparent OVN.schnorr_zkp.
  Transparent run.
 
  (* A slightly more general version where we don't fix the precondition *)
  Theorem rsame_head_cmd_alt :
    ∀ {A B C : ord_choiceType} {f₀ : A → raw_code B} {f₁ : A → raw_code C}
      (m : command A) pre (post : postcond B C),
      ⊢ ⦃ pre ⦄
        x ← cmd m ;; ret x ≈ x ← cmd m ;; ret x
                                            ⦃ λ '(a₀, s₀) '(a₁, s₁), pre (s₀, s₁) ∧ a₀ = a₁ ⦄ →
      (∀ a, ⊢ ⦃ pre ⦄ f₀ a ≈ f₁ a ⦃ post ⦄) →
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

  (* Ltac make_pure_rhs p := *)
  (*   match goal with *)
  (*   | [ |- context [ ⊢ ⦃ ?P ⦄ ?x ≈ _ ⦃ ?Q ⦄ ] ] => *)
  (*       let Hx := fresh in *)
  (*       set (Hx := x) ; *)
  (*       pattern p in Hx ; *)
  (*       subst Hx ; *)

  (*       (* Match bind and apply *) *)
  (*       match goal with *)
  (*       | [ |- context [ ⊢ ⦃ ?P ⦄ _ ≈ bind (is_state ?a) ?f ⦃ ?Q ⦄ ] ] => *)
  (*           let av := fresh in *)
  (*           let fv := fresh in *)
  (*           set (av := a) *)
  (*           ; set (fv := f) *)
  (*           ; eapply (r_bind (ret p) av _ fv P (fun '(v0, h0) '(v1, h1) => v0 = v1 /\ P (h0, h1)) Q) *)
  (*           ; subst av fv ; hnf ; [ | intros ; apply rpre_hypothesis_rule' ; intros ? ? [] ; apply rpre_weaken_rule with (pre := fun '(s₀, s₁) => P (s₀, s₁)) *)
  (*             ] *)
  (*       end *)
  (*   end. *)

 
  (* Corollary r_transR_val' : *)
  (*   forall {A B C : choice_type} (c₀ : raw_code A) (c₀' : raw_code B) (c₁ : raw_code B) (f : B -> A), *)
  (*     deterministic c₀' -> *)
  (*     deterministic c₀ -> *)
  (*     deterministic c₁ -> *)
  (*     ⊢ ⦃ true_precond ⦄ c₀' ≈ c₀ ⦃ fun '(v₀, _) '(v₁, _) => f v₀ = v₁ ⦄ -> *)
  (*     ⊢ ⦃ true_precond ⦄ c₁ ≈ c₀ ⦃ fun '(v₀, _) '(v₁, _) => f v₀ = v₁ ⦄ -> *)
  (*     ⊢ ⦃ true_precond ⦄ c₀' ≈ c₁ ⦃ fun '(v₀, _) '(v₁, _) => v₀ = v₁ ⦄. *)
  (* Proof. *)
  (*   intros. *)
  (*   intros A₀ A₁ P Q c₀ c₀' c₁ hd₀' hd₀ hd₁ he h. *)
  (* unshelve eapply det_to_sem. 1,2: assumption. *)
  (* unshelve eapply sem_to_det in he. 1,2: assumption. *)
  (* unshelve eapply sem_to_det in h. 1,2: assumption. *)
  (* intros s₀ s₁ hP. *)
  (* specialize (h s₀ s₁ hP). specialize (he s₀ s₀ hP). *)
  (* destruct (det_run c₀ _). *)
  (* destruct (det_run c₀' _). *)
  (* destruct (det_run c₁ _). *)
  (* subst. *)
  (* assumption. *)

  (*   apply r_transL_val with c₀ ; try assumption ; now apply r_nice_swap. *)
  (* Qed. *)

  Definition schnorr_run_post_cond :
    tgt (RUN, (choiceStatement × choiceWitness, choiceTranscript))
    → OVN.t_SchnorrZKPCommit → Prop.
  Proof.
    intros [[[l1 l2] l3] l4] [[r1 r2] r3] ; cbn in *.
    refine ((StatementToGroup (otf l2) = r1) /\ (WitnessToField (otf l3) = r2) /\ (WitnessToField (otf l4) = r3)).
  Defined.
 
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


 
 Lemma schnorr_run_eq  (pre : precond) :
    forall (b : Witness) c,
      Some c = lookup_op RUN_interactive (RUN, ((chProd choiceStatement choiceWitness), choiceTranscript)) ->
      (* (b = (f_random_field_elem *)
      (*        (ret_both (jasmin_word.wrepr jasmin_wsize.U32 (Z.of_nat (nat_of_ord x0)))))) -> *)
      ⊢ ⦃ pre ⦄
        c (fto (HacspecGroup.g ^+ b), fto b)
        ≈
        r ← sample uniform (2^32) ;;
        is_state (OVN.schnorr_zkp (ret_both (Hacspec_Lib_Pre.repr _ (Z.of_nat (nat_of_ord r)))) (ret_both (StatementToGroup (HacspecGroup.g ^+ b))) (ret_both (WitnessToField b)))
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

      (* Unset Printing Notations. *)
      (* pkg_core_definition.sampler *)
    (* apply (r_const_sample_L) ; [ apply LosslessOp_uniform | intros ]. *)
    (* apply (r_const_sample_R) ; [ apply LosslessOp_uniform | intros ]. *)

    eapply rsymmetry ;
    eapply r_uniform_bij with (f := fun x => fto (FieldToWitness(is_pure (f_random_field_elem (t_Field := OVN_impl.v_G_t_Group.(f_Z_t_Field)) (ret_both (Hacspec_Lib_Pre.repr _ (Z.of_nat (nat_of_ord x)))))))) ; [ apply randomness_sample_is_bijective | intros ] ;
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

        Check r_uniform_bij.
        assert (
            forall {A B} i (H : Positive i) f pre post (c0 : _ -> raw_code A) (c1 : _ -> raw_code B),
            bijective f
            → (∀ x1 : Arit (uniform i), ⊢ ⦃ pre ⦄ c0 x1 ≈ c1 (f x1) ⦃ post ⦄) ->         
            ⊢ ⦃ pre ⦄
          e ← sample uniform i ;;
          c0 e ≈ x ← is_state
            (f_hash (t_Group := OVN_impl.v_G_t_Group)
               (impl__into_vec
                  (unsize
                     (box_new
                        (array_from_list
                           [:: f_g(t_Group := OVN_impl.v_G_t_Group); ret_both (StatementToGroup (HacspecGroup.g ^+ b));
                               f_g_pow
                                 (f_random_field_elem (t_Field := OVN_impl.v_G_t_Group.(f_Z_t_Field))
                                    (ret_both (Hacspec_Lib_Pre.repr _ (Z.of_nat (nat_of_ord x)))))]))))) ;; c1 x ⦃ post ⦄) by admit.
        (* TODO : connect hash to random sample value ! *)

        eapply H ; clear H.
        * admit.
        * intros.

          apply getr_set_lhs.

          set (ret _).
          set (prod_b (_,_,_)).
          apply (make_pure (x := r) (y := b0)).
          subst r b0.

      apply r_ret.
      intros.
      simpl.
      repeat split.
      -- rewrite! otf_fto.
        set (b0 := f_random_field_elem _) ; generalize dependent b0 ; intros.
        rewrite <- expgnE.
        apply conversion_is_true.
      -- 

        admit.
  Admitted.
End OVN_schnorr_proof.

(*** Example (Z89) *)

Module Z89_impl : HacspecOVNParams.
  #[local] Open Scope hacspec_scope.
 
  Definition v_Z : choice_type := 'nat.
  Definition v_G : choice_type := 'nat.
   Definition v_A : choice_type := 'nat.
  Definition n : both uint_size := ret_both 55.

  Instance v_Z_t_Field : t_Field v_Z :=
    {|
      f_field_type_Serializable := Serializable.nat_serializable : Serializable.Serializable 'nat;
      f_q := ret_both (89%nat : 'nat);
      f_random_field_elem := fun x => bind_both x (fun x => ret_both (Z.to_nat (unsigned x) : 'nat));
      f_field_zero := ret_both (0%nat : 'nat);
      f_field_one := ret_both (1%nat : 'nat);
      f_add x y := bind_both x (fun (x : nat) => bind_both y (fun (y : nat) => ret_both (((x + y) mod 88)%nat : 'nat))) ;
      f_sub x y := bind_both x (fun (x : nat) => bind_both y (fun (y : nat) => ret_both (((x - y) mod 88)%nat : 'nat))) ;
      f_mul x y := bind_both x (fun (x : nat) => bind_both y (fun (y : nat) => ret_both (((x * y) mod 88)%nat : 'nat))) ; 
    |}.

  Fixpoint f_inv_helper (prod : both v_G -> both v_G -> both v_G) (one : both v_G) (n : 'nat) (x : both v_G) : both v_G :=
    match n with
    | O => ret_both (O : 'nat)  (* Failure *)
    | S n' =>
        ifb (prod x (ret_both n)) =.? one
        then ret_both n
        else f_inv_helper prod one n' x
    end.
  
  Program Definition v_G_t_Group : t_Group v_G :=
    (
      let f_Z := v_Z in
      let f_g := ret_both (3%nat : 'nat) in
      let f_pow x y := bind_both x (fun (x : v_G) => bind_both y (fun (y : f_Z) => ret_both (((x ^ y) mod 89)%nat : 'nat))) in
      let f_g_pow := f_pow f_g in
      let f_group_one := ret_both (1%nat : 'nat) in
      let f_prod x y := bind_both x (fun (x : v_G) => bind_both y (fun (y : v_G) => ret_both (((x * y) mod 89)%nat : 'nat))) in
      let f_inv := f_inv_helper f_prod f_group_one 88%nat in
      let f_div x y := f_prod x (f_inv y) in
      let f_hash x := (ret_both (0%nat : 'nat)) in
      {|
        f_group_type_Serializable := v_Z_t_Field.(f_field_type_Serializable);
        f_Z := f_Z;
        f_Z_t_Field := v_Z_t_Field;
        f_Z_t_Serialize := _;
        f_Z_t_Deserial := _;
        f_Z_t_Serial := _;
        f_Z_t_Clone := _;
        f_Z_t_Eq := Hacspec_Lib_Pre.nat_eqdec;
        f_Z_t_PartialEq := _;
        f_Z_t_Copy := _;
        f_Z_t_Sized := _;
        f_g := f_g;
        f_g_pow := f_g_pow;
        f_pow := f_pow;
        f_group_one := f_group_one;
        f_prod := f_prod ;
        f_inv := f_inv;
        f_div := f_div;
        f_hash := f_hash
      |}).
  Admit Obligations.
  
  Definition v_G_t_Eq : t_Eq v_G := Hacspec_Lib_Pre.nat_eqdec.
  Definition v_A_t_HasActions : t_HasActions v_A.
  Proof.
    constructor.
    refine (ret_both (0%nat : 'nat)).
  Defined.

End Z89_impl.

Module Z89_group_operations : GroupOperationProperties Z89_impl.
  #[local] Open Scope hacspec_scope.
  Import Z89_impl.

  Axiom v_G_t_Group : t_Group v_G.
  Axiom add_sub_cancel : ∀ a b : both v_Z, f_add a (f_sub b a) ≈both b.
  Axiom add_sub_cancel2 : ∀ a b : both v_Z, f_add (f_sub b a) a ≈both b. 
  Axiom prod_pow_add_mul : ∀ x y z : both f_Z, f_prod (f_g_pow x) (f_pow (f_g_pow z) y) ≈both f_g_pow (f_add x (f_mul z y)).
Axiom prod_pow_pow : forall h x a b, f_prod (f_pow h x) (f_pow (f_pow h a) b) ≈both f_pow h (f_add x (f_mul a b)).
  Axiom div_prod_cancel : forall x y, f_div (f_prod x y) y ≈both x.

  Axiom mul_comm : forall x y, f_mul x y ≈both f_mul y x.

  (* HB.instance Definition sort_group : hasChoice (Choice.sort (chElement v_G)) := _. (* Choice.clone (Choice.sort (chElement v_G)) _.  *) *)

  Axiom both_v_G_choice : hasChoice.axioms_ (both v_G).
  Axiom both_v_G_countable : Choice_isCountable (both v_G).
  Axiom both_v_G_hasDecEq : hasDecEq (both v_G).
  Axiom both_v_G_isFinite : isFinite.axioms_ (both v_G) both_v_G_hasDecEq.

  Axiom v_G_countable : Choice_isCountable (Choice.sort (chElement v_G)).
  Axiom v_G_isFinite : isFinite (Choice.sort (chElement v_G)).

  Axiom both_v_Z_choice : hasChoice.axioms_ (both v_Z).
  Axiom both_v_Z_countable : Choice_isCountable (both v_Z).
  Axiom both_v_Z_hasDecEq : hasDecEq (both v_Z).
  Axiom both_v_Z_isFinite : isFinite.axioms_ (both v_Z) both_v_Z_hasDecEq.

  Axiom v_Z_countable : Choice_isCountable (Choice.sort (chElement v_Z)).
  Axiom v_Z_isFinite : isFinite (Choice.sort (chElement v_Z)).

  Axiom f_prodA : associative (lower2 f_prod).
  Axiom f_prod1 : associative (lower2 f_prod).
  Axiom f_prod_left_id : left_id (is_pure f_group_one) (lower2 f_prod).
  Axiom f_invK : involutive (lower1 f_inv).
  Axiom f_invM : {morph (lower1 f_inv)  : x y / (lower2 f_prod) x y >-> (lower2 f_prod)  y x}.

  Axiom v_Z_Field : GRing.Field (v_Z).

  Axiom prod_inv_cancel : forall x, f_prod (f_inv x) x ≈both f_group_one.

End Z89_group_operations.

Module Z89_secure_group : SecureGroup Z89_impl Z89_group_operations.
  Import Z89_impl.
  Import Z89_group_operations.
  Module Group := HacspecGroup Z89_impl Z89_group_operations.
  Import Group.
  Axiom v_G_prime_order : prime #[is_pure f_g : v_G_is_group].
  Axiom v_G_g_gen : [set : v_G_is_group] = <[is_pure f_g : v_G_is_group]>.
End Z89_secure_group.

Module Hacspec_Z89 := HacspecGroupParam Z89_impl Z89_group_operations Z89_secure_group.
Module Schnorr_Z89 := Schnorr Hacspec_Z89.

Module OVN_Z89 := HacspecOVN Z89_impl.

(* Schnorr_Z89.Sigma.RUN_interactive *)

(* Import Schnorr_Z89.Sigma. *)
(* Import Schnorr_Z89.MyAlg. *)
(* Import Schnorr_Z89.Sigma.Oracle. *)

(* Import Z89_impl. *)
