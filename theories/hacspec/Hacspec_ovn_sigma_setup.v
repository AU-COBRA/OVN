(* begin details: Imports *)
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
From OVN Require Import Hacspec_ovn_group_and_field.

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

(* From mathcomp Require Import ring. *)
(* end details *)

(******************************************************************************)
(*                   OVN instances for Sigma protocols                        *)
(*                                                                            *)
(* Module HacspecGroup                                                        *)
(* - ovn implementation with proofs of group operation, to                    *)
(*   instantiate HB instances for group and field using hacspec OVN impl      *)
(*                                                                            *)
(* Module SecureGroup                                                         *)
(* - properties for security of group, e.g. prime fields                      *)
(*                                                                            *)
(* Module FieldEquality                                                       *)
(* - equality between group field Z/#[g]Z and OVN field and some properties   *)
(*   about the equality                                                       *)
(******************************************************************************)

(** * Hacspec Group *)
Module HacspecGroup.
  Module OVN := HacspecOVN.
  Include OVN.
  Export OVN.
  
  Instance f_Z_t_Field' : t_Field f_Z := _.

  Parameter v_G_group_properties : is_setoid_group_properties.axioms_ both_C
                                     (group_op.class (Hacspec_ovn_group_and_field_both_C__canonical__Hacspec_ovn_group_and_field_group_op v_G_t_Group))
                                     (eqR.class Hacspec_ovn_group_and_field_both_C__canonical__Hacspec_ovn_group_and_field_eqR).

  Definition v_G_is_group : finGroupType :=
    (Hacspec_ovn_group_and_field_C_type__canonical__fingroup_FinGroup (C := v_G) v_G_t_Group v_G_group_properties).


  Parameter v_Z_field_properties : is_setoid_field_properties.axioms_ (both_Z v_G_t_Group) (setoid_field_op.class (Hacspec_ovn_group_and_field_both_Z__canonical__Hacspec_ovn_group_and_field_setoid_field_op v_G_t_Group)) (eqR.class (Hacspec_ovn_group_and_field_both_Z__canonical__Hacspec_ovn_group_and_field_eqR v_G_t_Group)).

  Definition v_Z_is_field : fieldType :=
    Hacspec_ovn_group_and_field_Z_type__canonical__GRing_Field (C := v_G) v_G_t_Group v_Z_field_properties.

  Parameter pow_base : forall x, f_g_pow x ≈both f_pow f_g x. (* TODO: just have this as a definition *)
End HacspecGroup.

(** * Secure Group *)
Module Type SecureGroup.
  Module Group := HacspecGroup.
  Export Group.
  Include Group.

  (* A secure group is of prime order and has a generator *)
  Parameter v_G_prime_order : prime #[ is_pure f_g : v_G_is_group].
  Parameter v_G_g_gen : [set : v_G_is_group] = <[ is_pure f_g : v_G_is_group]>.

End SecureGroup.

Module Type FieldType.
  Parameter equivalent_field : fieldType.
End FieldType.

(** * Field equality *)
Module FieldEquality (SG : GroupParam) (FT : FieldType).
  Include SG.
  Export SG.

  (* order of g *)
  Definition q : nat := #[g].

  (** Field equality *)
  (* the field is given by the Z/#[g]Z, so the OVN field should be equal to this *)

  Program Definition Z_to_F : {rmorphism 'Z_q -> 'F_q} := GRing.ssrfun_idfun__canonical__GRing_RMorphism _.
  (* begin hide *)
  Next Obligation.
    now rewrite (@pdiv_id q prime_order).
  Defined.
  Fail Next Obligation.
  (* end hide *)

  Program Definition F_to_Z : {rmorphism 'F_q -> 'Z_q} := GRing.ssrfun_idfun__canonical__GRing_RMorphism _.
  (* begin hide *)
  Next Obligation.
    now rewrite (@pdiv_id q prime_order).
  Defined.
  Fail Next Obligation.
  (* end hide *)

  Lemma F_to_Z_cancel :
    cancel Z_to_F F_to_Z.
  Proof.
    intros x.
    unfold Z_to_F, F_to_Z.
    unfold eq_rect.
    unfold Z_to_F_obligation_1, F_to_Z_obligation_1.
    unfold eq_ind_r.
    unfold eq_ind.
    destruct (Logic.eq_sym (pdiv_id (p:=q) prime_order)).
    reflexivity.
  Qed.

  Lemma Z_to_F_cancel :
    cancel F_to_Z Z_to_F.
  Proof.
    intros x.
    unfold Z_to_F, F_to_Z.
    unfold eq_rect.
    unfold Z_to_F_obligation_1, F_to_Z_obligation_1.
    unfold eq_ind_r.
    unfold eq_ind.
    destruct (Logic.eq_sym (pdiv_id (p:=q) prime_order)).
    reflexivity.
  Qed.

  Parameter WitnessToField : {rmorphism 'Z_q -> FT.equivalent_field}.
  Parameter FieldToWitness : {rmorphism FT.equivalent_field -> 'Z_q}.
  Parameter WitnessToFieldCancel :
    cancel FieldToWitness WitnessToField.
  Parameter FieldToWitnessCancel :
    cancel WitnessToField FieldToWitness.

End FieldEquality.

(** * Hacspec Group Param *)
Module HacspecGroupParam (SG : SecureGroup) <: GroupParam.
  Include SG.
  Export SG.

  (* The finite group type is the ovn group *)
  Definition gT : finGroupType := v_G_is_group.
  Definition ζ : {set gT} := [set : gT].
  Definition g :  gT := is_pure f_g.

  Definition g_gen : ζ = <[g]> := v_G_g_gen.
  Definition prime_order : prime #[g] := v_G_prime_order.

  (* order of g *)
  Definition q : nat := #[g].

  (* pow spec, could be omitted by using iterated mul in hax code instead *)
  Theorem one_is_not_a_generator : generator ζ 1 -> False.
  Proof.
    intros.
    assert (generator ζ g) by now unfold generator ; rewrite g_gen.
    pose (generator_coprime (gT := gT) g 0).
    rewrite <- g_gen in e.
    rewrite expg0 in e.
    rewrite e in H.
    simpl in H.
    epose (prime_coprime 0 prime_order).
    rewrite e0 in H.
    unfold "_ %| _"%N in H.
    simpl in H.

    apply (ssrbool.elimN eqP H) ; clear.
    rewrite mod0n.
    reflexivity.
  Qed.

  Theorem generator_is_not_one : f_group_one ≈both f_g -> False.
  Proof.
    intros.
    apply one_is_not_a_generator.
    setoid_rewrite (proj1 H).
    now unfold generator ; rewrite g_gen.
  Qed.

  (** * Helper properties *)

  Lemma order_ge1 : succn (succn (Zp_trunc q)) = q.
  Proof.
    rewrite <- (@pdiv_id q prime_order) at 1.
    apply Fp_cast, prime_order.
  Qed.

  Lemma trunc_pow : forall (h : gT) x, h ^+ (x %% (Zp_trunc q).+2) = h ^+ x.
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

  Lemma invg_id : (forall (x : gT), x ^-1 = x ^- 1%R).
  Proof. reflexivity. Qed.

  Lemma trunc_extra : forall (h : gT), h ^+ (Zp_trunc q).+2 = 1%g.
    intros.
    rewrite <- trunc_pow.
    now rewrite modnn.
  Qed.

  Lemma reverse_opp : (forall (x : gT) (n : 'Z_q), x ^+ ((Zp_trunc (pdiv q)).+2 - n) = x ^+ GRing.opp n).
  Proof.
    intros.
    rewrite (@pdiv_id q prime_order).
    now rewrite trunc_pow.
  Qed.

  Lemma neg_is_opp : (forall (x : gT) (n : 'Z_q), x ^- n = x ^+ GRing.opp n).
  Proof.
    intros x n.
    rewrite trunc_pow.
    destruct n as [n ?] ; simpl.
    induction n as [ | n ].
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
      set (n0 := subn _ _).
      now rewrite (Nat.lt_succ_pred 0 n0).
  Qed.

  Lemma mulg_cancel : forall (x : gT) (y : 'Z_q),
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

  Lemma prod_swap_iff :
    forall a b (x : gT) (y : 'Z_q),
      (a * x ^- y = b <-> a = b * x ^+ y)%g
      /\ (x ^- y * a = b <-> a = x ^+ y * b)%g.
  Proof.
    repeat split ;
      [ eapply (canRL (f := mulg^~ _) (g := mulg^~ _))
      | eapply (canLR (f := mulg^~ _) (g := mulg^~ _))
      | eapply (canRL)
      | eapply (canLR) ] ; apply (mulg_cancel x y).
  Qed.

  Lemma mulg_invg_sub : (forall (x : gT) (y z : 'Z_q), x ^+ y * x ^- z = x ^+ nat_of_ord (y - z)%R)%g.
  Proof.
    intros.
    rewrite neg_is_opp.
    rewrite <- expgD.
    now rewrite trunc_pow.
  Qed.

  Lemma mulg_invg_left_sub : (forall (x : gT) (y z : 'Z_q), x ^- y * x ^+ z = x ^+ nat_of_ord (z - y)%R)%g.
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

  Lemma div_cancel_Fq : forall (x : gT) (s : 'F_q), s <> 0%R -> x ^+ nat_of_ord (s / s)%R = x.
  Proof.
    intros.
    rewrite mulrV.
    2: now rewrite (unitfE) ; apply /eqP.
    now rewrite expg1.
  Qed.

  (* Parameter pow_witness_to_field : *)
  (*   forall (h : gT) (b : 'Z_q), *)
  (*     (h ^ b = (setoid_lower2 f_pow) h (WitnessToField b))%g. *)
End HacspecGroupParam.

(** * Assumptions *)
Module Type HacspecGroupParamAxiom (SG : SecureGroup).
  Module HacspecGroup := HacspecGroupParam SG.
  Module FT.
    Definition equivalent_field : fieldType := HacspecGroup.v_Z_is_field.
  End FT.
  Module field_equality := FieldEquality HacspecGroup FT.

  Include field_equality.
  Export field_equality.

  Lemma div_cancel : forall (x : gT) (s : 'Z_q), s <> 0%R -> x ^+ nat_of_ord (s / s)%R = x.
  Proof.
    intros.
    rewrite mulrV.
    2:{
      rewrite <- (F_to_Z_cancel _).
      apply rmorph_unit.
      rewrite (unitfE).
      apply /eqP.
      red ; intros.
      apply H.
      rewrite <- (F_to_Z_cancel _).
      rewrite H0.
      apply  (@rmorph0 'F_q 'Z_q F_to_Z).
    }
    now rewrite expg1.
  Qed.

  (* pow spec, could be omitted by using iterated mul in hax code instead *)
  Parameter pow_witness_to_field :
    forall (h : gT) (b : 'Z_q),
      (h ^+ b = is_pure (f_pow (ret_both h) (ret_both (WitnessToField b)))).
  
  Parameter conversion_is_true :
    forall (b : both f_Z),
    (HacspecGroup.g ^+ FieldToWitness (is_pure b)) = is_pure (f_g_pow b).

    (* We have a bijection between f_random_field_elem and random sampling *)
    Parameter randomness_sample_is_bijective :
      bijective
        (λ x : 'I_(2 ^ 32),
            fto
              (FieldToWitness
                 (is_pure
                    (f_random_field_elem (ret_both (Hacspec_Lib_Pre.repr _ (Z.of_nat (nat_of_ord x)))))))).

    (* Taking the hash should be equal to sampling! *)
    Parameter hash_is_psudorandom :
      forall {A B} i (H : Positive i) f pre post (c0 : _ -> raw_code A) (c1 : _ -> raw_code B) l,
        (∀ x1 : Arit (uniform i), ⊢ ⦃ pre ⦄ c0 x1 ≈ c1 (f x1) ⦃ post ⦄) ->
        ⊢ ⦃ pre ⦄
          e ← sample uniform i ;;
        c0 e ≈
          x ← is_state
          (f_hash (t_Group := HacspecGroup.v_G_t_Group)
             (impl__into_vec
                (unsize
                   (box_new
                      (array_from_list l))))) ;; c1 x ⦃ post ⦄.

End HacspecGroupParamAxiom.

