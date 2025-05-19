From mathcomp Require Import all_ssreflect fingroup.fingroup ssreflect.
Set Warnings "-notation-overridden,-ambiguous-paths".
From SSProve.Crypt Require Import choice_type Package Prelude.
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

From SSProve.Crypt Require Import jasmin_word.

From OVN Require Import Schnorr SigmaProtocol.

From SSProve.Relational Require Import OrderEnrichedCategory GenericRulesSimple.

Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp Require Import all_ssreflect all_algebra reals distr realsum
  fingroup.fingroup solvable.cyclic prime ssrnat ssreflect ssrfun ssrbool ssrnum
  eqtype choice seq.
Set Warnings "notation-overridden,ambiguous-paths".

From SSProve.Mon Require Import SPropBase.

From SSProve.Crypt Require Import Axioms ChoiceAsOrd SubDistr Couplings
  UniformDistrLemmas FreeProbProg Theta_dens RulesStateProb UniformStateProb
  pkg_core_definition choice_type pkg_composition pkg_rhl Package Prelude.

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
From OVN Require Import Hacspec_ovn_Ovn_z_89_.

From OVN Require Import Hacspec_helpers.
From OVN Require Import Hacspec_ovn_group_and_field.
From OVN Require Import Hacspec_ovn_sigma_setup.

Module OVN_Z89 <: HacspecOvnParameter.
  (** Move arguments to context *)
  Definition v_G : choice_type := t_g_z_89_.
  Definition v_G_t_Group : t_Group v_G := t_g_z_89__t_Group.

  Definition v_A : choice_type := 'unit.
  Definition v_A_t_Sized : t_Sized v_A := id.

  Definition v_A_t_HasActions : t_HasActions v_A := {| f_accept := ret_both tt |}.

  Definition n : both uint_size := ret_both 55.

  Definition v_G_t_Sized : t_Sized v_G := id.
End OVN_Z89.

Module OVN_GroupAndFieldParameter_Z89 <: HacspecOvnGroupAndFieldParameter OVN_Z89.
  Module GroupAndFieldPre := HacspecOvnGroupAndFieldPre OVN_Z89.
  Include GroupAndFieldPre.

  From mathcomp Require Import ring.
  From mathcomp Require Import zify.

  Lemma both_group_properties :
    is_setoid_group_properties.axioms_ (both_v_G)
      (group_op.class HacspecOvnGroupAndFieldPre_both_v_G__canonical__Hacspec_ovn_group_and_field_group_op)
      (eqR.class HacspecOvnGroupAndFieldPre_both_v_G__canonical__Hacspec_ovn_group_and_field_eqR).
  Proof.
    constructor.
    - intros x y z.
      cbn.
      (* repeat unfold f_z_val at 1. *)
      (* repeat unfold let_both at 1. *)
      (* repeat unfold Build_t_g_z_89_ at 1. *)

      apply (both_eq_fun_ext (fun x => solve_lift bind_both x _)).
      apply (both_eq_fun_ext).
      apply (both_eq_fun_ext (fun x => solve_lift bind_both x _)).

      repeat unfold let_both at 1.

      assert (
          H_assoc_through_bind :
          forall {A}
            (x : both A) (y : both A) (z : both A) (f : A -> A -> A),
            (forall (x y z : A), f (f x y) z = f x (f y z)) ->
            (bind_both (bind_both x (λ x', bind_both y (fun y' => ret_both (f x' y')))) (λ xy', bind_both z (fun z' => ret_both (f xy' z')))) =
              (bind_both x (λ x', bind_both (bind_both y (λ y', bind_both z (fun z' => ret_both (f y' z')))) (fun yz' => ret_both (f x' yz'))))).
      {
        clear ; intros.
        apply both_eq.
        unfold bind_both ; simpl.
        unfold bind_raw_both ; simpl.
        rewrite H.
        f_equal.
        repeat setoid_rewrite bind_assoc.
        repeat setoid_rewrite bind_rewrite.
        setoid_rewrite H.
        reflexivity.
      }

      assert (forall (x y z : both int8), (x .* y .* z) = (x .* (y .* z))).
      {
        clear -H_assoc_through_bind ; intros.

        unfold ".*" at 1.
        unfold lift2_both at 1.
        simpl.

        unfold ".*" at 1.
        unfold lift2_both at 1.
        simpl.

        unfold ".*" at 1.
        unfold lift2_both at 1.
        simpl.

        unfold ".*" at 1.
        unfold lift2_both at 1.
        simpl.

        rewrite H_assoc_through_bind ; [ reflexivity | ].
        clear ; intros.
        unfold Hacspec_Lib_Pre.int_mul.
        now rewrite mulwA.
      }

      assert (forall a b : both int8, ((cast_int a .* cast_int b) .% (ret_both (modulus U8)) : both int16) = cast_int (a .* b)).
      {
        clear -H_assoc_through_bind ; intros.
        repeat unfold cast_int at 1.
        repeat unfold lift1_both at 1.
        repeat unfold ".*" at 1.
        repeat unfold ".%" at 1.
        repeat unfold lift2_both at 1.


        apply both_eq.
        cbn ; unfold bind_raw_both ; cbn.
        assert (
            (Hacspec_Lib_Pre.int_mod (Hacspec_Lib_Pre.int_mul (wrepr U16 (toword x)) (wrepr U16 (toword x0)))
        (Z_to_int (modulus (nat_of_wsize U8)))) = (wrepr U16 (toword (Hacspec_Lib_Pre.int_mul x x0)))).
        {
          unfold Hacspec_Lib_Pre.int_mul.
          unfold Hacspec_Lib_Pre.int_mod.
          unfold mul_word.
          rewrite !urepr_word.
          setoid_rewrite <- wrepr_mul.
          rewrite <- wrepr_unsigned.
          rewrite wunsigned_repr.
          rewrite wunsigned_repr.
          f_equal.

          rewrite <- Znumtheory.Zmod_div_mod.
          1:{
            symmetry.
            rewrite <- Zmod_small with (n := modulus U16).
            1:{
              reflexivity.
            }
            split ; [ | eapply Z.lt_trans ] ; now apply (Z.mod_pos_bound).
          }
          1,2: easy.
          simpl.
          replace (modulus nat15.+1) with (modulus U8 * modulus U8) by reflexivity.
          apply Z.divide_factor_l.
        }
        (* rewrite H. *)
        f_equal.
        2:{
        repeat setoid_rewrite bind_assoc.
        repeat setoid_rewrite bind_rewrite.
        Set Printing Coercions.
        unfold Hacspec_Lib_Pre.int_mul.
        unfold mul_word.
        setoid_rewrite H.

        setoid_rewrite
      }

      rewrite both_equivalence_is_pure_eq.
      rewrite hacspec_function_guarantees2.
      symmetry.
      rewrite hacspec_function_guarantees2.
      symmetry.
      rewrite <- both_equivalence_is_pure_eq.

      set (f_z_val (solve_lift Build_t_z_89_)).

      unfold cast_int at 1.
      unfold lift1_both at 1.
      unfold bind_both.
      simpl.

      unfold cast_int at 1.
      unfold lift1_both at 1.
      unfold bind_both.
      simpl.

      unfold Build_t_g_z_89_ at 1 2.

      unfold ".%" at 2.
      unfold lift2_both at 1.
      simpl.

      unfold f_g_val at 2.
      simpl.
      unfold cast_int at 1.
      unfold lift1_both at 1.
      simpl.

      unfold ".%" at 2.
      unfold lift2_both at 1.
      simpl.

      unfold Hacspec_Lib_Pre.int_mod.
      unfold unsigned.
      rewrite !urepr_word.



      rewrite both_equivalence_is_pure_eq.




      cbn.

      unfold ".*" at 2.
      unfold lift2_both at 1.
      simpl.

      unfold cast_int at 1.
      unfold lift1_both at 1.
      simpl.

      unfold cast_int at 1.
      unfold lift1_both at 1.
      simpl.

      unfold cast_int at 1.
      unfold lift1_both at 1.
      simpl.

      unfold ".*" at 1.
      unfold lift2_both at 1.
      simpl.

      unfold Hacspec_Lib_Pre.int_mul.
      unfold unsigned.
      unfold mul_word.
      rewrite !urepr_word.



      setoid_rewrite <- wrepr_mul.

      (* set (_ mod _). *)
      (* set (_ * _) in z0. *)
      (* pattern z1 in z0. *)
      (* set (fun _ => _) in z0. *)
      (* subst z0 z1. *)

      rewrite <- !Zmult_mod_distr_l.
      simpl.
      rewrite <- !Zmult_mod_distr_r.
      simpl.


      rewrite <- !Zmult_mod_distr_r.

      rewrite Zmod_small.

      set (_ mod _) at 5.
      replace (is_pure b mod nat15.+1) with (is_pure b).

      rewrite <- Zmult_mod.
      rewrite <- Zmult_mod.

      rewrite !Zmod_small ; [ | admit.. ].
      setoid_rewrite <- wmulE.

      unfold cast_int at 1.
      unfold lift1_both at 1.
      simpl.
      unfold Hacspec_Lib_Pre.int_mod.
      unfold unsigned.
      rewrite !urepr_word.

      unfold cast_int at 1.
      unfold lift1_both at 1.
      simpl.
      unfold Hacspec_Lib_Pre.int_mod.
      unfold unsigned.
      rewrite !urepr_word.

      unfold ".*" at 1.
      unfold lift2_both at 1.
      simpl.

      unfold Hacspec_Lib_Pre.int_mul.
      unfold mul_word.

      rewrite both_equivalence_is_pure_eq.
      simpl.

      setoid_rewrite <- wmulE.

      {
        symmetry.
        simpl.

        unfold cast_int at 1.
        unfold lift1_both at 1.
        unfold bind_both.
        simpl.

        unfold f_g_val at 1.
        simpl.
        unfold cast_int at 1.
        unfold lift1_both at 1.
        simpl.

        unfold ".%" at 1.
        unfold lift2_both at 1.
        simpl.

        unfold Hacspec_Lib_Pre.int_mod.
        unfold unsigned.
        rewrite !urepr_word.

        cbn.

        unfold ".*" at 1.
        unfold lift2_both at 1.
        simpl.

        unfold cast_int at 1.
        unfold lift1_both at 1.
        simpl.
        unfold Hacspec_Lib_Pre.int_mod.
        unfold unsigned.

        unfold bind_both at 1.
        unfold bind_raw_both at 1.
        simpl.

        unfold ".%" at 1.
        unfold lift2_both at 1.
        simpl.

        unfold Hacspec_Lib_Pre.int_mul.
        unfold mul_word.

        rewrite !Zmod_small ; [ | admit.. ].

        unfold unsigned.
        rewrite !urepr_word.
        simpl.

        unfold cast_int at 1.
        unfold lift1_both at 1.
        simpl.
        unfold Hacspec_Lib_Pre.int_mod.
        unfold unsigned.

        rewrite !Zmod_small ; [ | admit.. ].

        unfold cast_int at 1.
        unfold lift1_both at 1.
        simpl.
        unfold Hacspec_Lib_Pre.int_mod.
        unfold unsigned.

        rewrite !urepr_word.
        rewrite !wrepr_mul.

        rewrite mulrA.

        reflexivity.
      }
  Qed.


  (* A proof of the field laws *)
  Parameter both_field_properties : is_setoid_field_properties.axioms_ (GroupAndFieldPre.both_Z) (field_op.class GroupAndFieldPre.HacspecOvnGroupAndFieldPre_both_Z__canonical__Hacspec_ovn_group_and_field_field_op) (eqR.class GroupAndFieldPre.HacspecOvnGroupAndFieldPre_both_Z__canonical__Hacspec_ovn_group_and_field_eqR).
End OVN_GroupAndFieldParameter_Z89.
e
Module Ovn_GroupAndFieldExtra_Z89 : HacspecOvnGroupAndFieldExtra OVN_Z89 OVN_GroupAndFieldParameter_Z89.
  Module GroupAndField := HacspecOvnGroupAndField OVN_Z89 OVN_GroupAndFieldParameter_Z89.
  Include GroupAndField.
  Export GroupAndField.

  (* Additional requirements and defintions *)
  Definition pow_base : forall x, f_g_pow x ≈both f_pow f_g x.
  Proof.
    intros.

    cbn.
    unfold f_g_pow.
    unfold GroupAndField.GroupAndFieldPre.OVN.v_G_t_Group_temp.
    unfold GroupAndField.GroupAndFieldPre.OVN.v_G_t_Group.
    Transparent OVN_Z89.v_G_t_Group.
    unfold OVN_Z89.v_G_t_Group.
    simpl.
  Qed.
  (* Instance f_Z_t_Field' : t_Field f_Z := _. *)

  (* A secure group is of prime order and has a generator *)
  Parameter v_G_prime_order : prime #[ is_pure f_g : v_G_is_group].
  Parameter v_G_g_gen : [set : v_G_is_group] = <[ is_pure f_g : v_G_is_group]>.
End Ovn_GroupAndFieldExtra_Z89.

Module OVN_GroupParamAxiom_Z89 :
  HacspecGroupParamAxiom OVN_Z89 OVN_GroupAndFieldParameter_Z89 Ovn_GroupAndFieldExtra_Z89.

  Module GaFP := HacspecGroupAndFieldParam OVN_Z89 OVN_GroupAndFieldParameter_Z89 Ovn_GroupAndFieldExtra_Z89.
  Include GaFP.
  Export GaFP.

  (* pow spec, could be omitted by using iterated mul in hax code instead *)
  Parameter pow_witness_to_field :
    forall (h : gT) (b : 'Z_q),
      (h ^+ b = is_pure (f_pow (ret_both h) (ret_both (WitnessToField b)))).

  Parameter conversion_is_true :
    forall (b : both f_Z),
    (g ^+ FieldToWitness (is_pure b)) = is_pure (f_g_pow b).

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
End OVN_GroupParamAxiom_Z89.

From OVN Require Import Hacspec_ovn_schnorr.
From OVN Require Import Hacspec_ovn_or.

From OVN Require Import Hacspec_ovn_total_proof.

(* Proof properties of z89 *)
Module ovn_z89_proof := OVN_proof OVN_Z89 OVN_GroupAndFieldParameter_Z89 Ovn_GroupAndFieldExtra_Z89 OVN_GroupParamAxiom_Z89.
