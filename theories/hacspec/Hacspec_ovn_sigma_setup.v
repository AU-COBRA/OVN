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
  Context {v_G : choice_type}.

  (* TODO: Cannot find instance in hacspec lib? *)
  Instance v_G_t_copy : t_Copy v_G := _.
  Instance v_G_t_partial_eq : t_PartialEq v_G v_G := _.
  Instance v_G_t_eq : t_Eq v_G := _.
  Instance v_G_t_clone : t_Clone v_G := _.
  Instance v_G_t_serialize : t_Serialize v_G := _.

  Context {v_G_t_Group : t_Group v_G}.
  Instance v_G_t_Group_temp : t_Group v_G := v_G_t_Group.

  Instance f_Z_t_copy : t_Copy f_Z := f_Z_t_Copy.
  Instance f_Z_t_partial_eq : t_PartialEq f_Z f_Z := f_Z_t_PartialEq.
  Instance f_Z_t_eq : t_Eq f_Z := f_Z_t_Eq.
  Instance f_Z_t_clone : t_Clone f_Z := f_Z_t_Clone.
  Instance f_Z_t_serialize : t_Serialize f_Z := f_Z_t_Serialize.

  Instance f_Z_t_Field' : t_Field f_Z := _.

  Context {v_A : choice_type}.
  Context {v_A_t_Sized : t_Sized v_A}.
  Instance v_A_t_Sized_temp : t_Sized v_A := v_A_t_Sized.

  Context {v_A_t_HasActions : t_HasActions v_A}.
  Instance v_A_t_HasActions_temp : t_HasActions v_A := v_A_t_HasActions.

  Context {n : both uint_size}.

  Context {v_G_t_Sized : t_Sized v_G}.
  Instance v_G_t_Sized_temp : t_Sized v_G := v_G_t_Sized.

  #[local] Open Scope hacspec_scope.

  Parameter v_G_group_properties : is_setoid_group_properties.axioms_ both_C
                                     (group_op.class (Hacspec_ovn_group_and_field_both_C__canonical__Hacspec_ovn_group_and_field_group_op v_G_t_Group))
                                     (eqR.class Hacspec_ovn_group_and_field_both_C__canonical__Hacspec_ovn_group_and_field_eqR).

  Definition v_G_is_group : finGroupType :=
    (Hacspec_ovn_group_and_field_C_type__canonical__fingroup_FinGroup (C := v_G) v_G_t_Group v_G_group_properties).


  Parameter v_Z_field_properties : is_setoid_field_properties.axioms_ (both_Z v_G_t_Group) (setoid_field_op.class (Hacspec_ovn_group_and_field_both_Z__canonical__Hacspec_ovn_group_and_field_setoid_field_op v_G_t_Group)) (eqR.class (Hacspec_ovn_group_and_field_both_Z__canonical__Hacspec_ovn_group_and_field_eqR v_G_t_Group)).

  Definition v_Z_is_field : fieldType :=
    Hacspec_ovn_group_and_field_Z_type__canonical__GRing_Field (C := v_G) v_G_t_Group v_Z_field_properties.

  Parameter pow_base : forall x, f_g_pow x ≈both f_pow f_g x. (* TODO: just have this as a definition *)
  Parameter generator_is_not_one : f_group_one ≈both f_g -> False.
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

End HacspecGroupParam.

(** * Field equality *)
Module Type FieldEquality (SG : SecureGroup).

  Module HacspecGroup := HacspecGroupParam SG.
  Include HacspecGroup.
  Export HacspecGroup.

  (** Field equality *)
  (* the field is given by the Z/#[g]Z, so the OVN field should be equal to this *)

  Program Definition Z_to_F : {rmorphism 'Z_q -> 'F_q} := GRing.ssrfun_idfun__canonical__GRing_RMorphism _.
  (* begin hide *)
  Next Obligation.
    now rewrite (@pdiv_id q HacspecGroup.prime_order).
  Defined.
  Fail Next Obligation.
  (* end hide *)

  Program Definition F_to_Z : {rmorphism 'F_q -> 'Z_q} := GRing.ssrfun_idfun__canonical__GRing_RMorphism _.
  (* begin hide *)
  Next Obligation.
    now rewrite (@pdiv_id q HacspecGroup.prime_order).
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

  Parameter WitnessToField : {rmorphism 'Z_ HacspecGroup.q -> v_Z_is_field}.
  Parameter FieldToWitness : {rmorphism v_Z_is_field -> 'Z_ HacspecGroup.q}.
  Parameter WitnessToFieldCancel :
    cancel FieldToWitness WitnessToField.
  Parameter FieldToWitnessCancel :
    cancel WitnessToField FieldToWitness.

  (* Properties of the field isomorphism *)
  Definition WitnessToFieldAdd : forall x y, WitnessToField (x + y) = is_pure (f_add (ret_both (WitnessToField x)) (ret_both (WitnessToField y))).
  Proof.
    intros. now rewrite rmorphD.
  Qed.

  Definition WitnessToFieldMul : forall x y,
      WitnessToField (Zp_mul x y) = is_pure (f_mul (ret_both (WitnessToField x)) (ret_both (WitnessToField y))).
  Proof.
    intros. now rewrite rmorphM.
  Qed.

  Parameter conversion_is_true :
    forall (b : both (v_G_t_Group.(f_Z))),
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
            (f_hash (t_Group := v_G_t_Group)
               (impl__into_vec
                  (unsize
                     (box_new
                        (array_from_list l))))) ;; c1 x ⦃ post ⦄.

  (** Field equality *)
  (* the field is given by the Z/#[g]Z, so the OVN field should be equal to this, same as for Schnorr *)

  (* pow spec, could be omitted by using iterated mul in hax code instead *)
  Parameter pow_witness_to_field :
    forall (h : gT) (b : 'Z_q),
      (h ^+ b = is_pure (f_pow (ret_both h) (ret_both (WitnessToField b)))).

  Definition FieldToWitnessOpp : (forall (b : both _), Zp_opp (FieldToWitness (is_pure b)) = FieldToWitness (is_pure (f_opp b))).
    intros.
    setoid_rewrite <- (rmorphN FieldToWitness).
    unfold "- _"%R ; simpl.
    unfold setoid_lower1, U, F, sf_opp ; simpl.
    f_equal.
    now Misc.push_down_sides.
  Defined.

  Definition WitnessToField_f_inv : forall s, (is_pure (f_inv (ret_both (WitnessToField s))) = (WitnessToField (Zp_inv s))).
  Proof.
    intros.
    rewrite <- (F_to_Z_cancel s) at 1.

    setoid_rewrite <- (fmorphV (WitnessToField \o F_to_Z)).
    simpl.
    setoid_rewrite (fmorphV (F_to_Z)).
    now rewrite F_to_Z_cancel.
  Defined.

  Definition FieldToWitnessOne : FieldToWitness (is_pure f_field_one) = 1%R.
  Proof.
    rewrite rmorph1.
    reflexivity.
  Defined.

End FieldEquality.
