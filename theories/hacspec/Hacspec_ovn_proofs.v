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

Module Type GroupOperationProperties.
  Axiom add_sub_cancel : forall a b, f_add a (f_sub b a) ≈both b.
  Axiom add_sub_cancel2 : forall a b, f_add (f_sub b a) a ≈both b.
  Definition hacspec_group_type : Type := (Choice.sort (chElement f_group_type)).
  Axiom prod_pow_add_mul : forall x y z, f_prod (f_g_pow x) (f_pow (f_g_pow z) y) ≈both f_g_pow (f_add x (f_mul z y)).
  Axiom prod_pow_pow : forall h x a b, f_prod (f_pow h x) (f_pow (f_pow h a) b) ≈both f_pow h (f_add x (f_mul a b)).
  Axiom div_prod_cancel : forall x y, f_div (f_prod x y) y ≈both x.
  HB.instance Definition _ : Finite hacspec_group_type := _.
End GroupOperationProperties.

Module OVN_proofs (group_properties : GroupOperationProperties).
  Include group_properties.

  (* Commitments compute correctly *)
  Lemma commitment_correct : forall x, (check_commitment x (commit_to x)) ≈both ret_both (true : 'bool).
  Proof.
    intros.
    apply both_equivalence_is_pure_eq.
    apply eqb_refl.
  Qed.

  Lemma zkp_one_out_of_two_correct :
    forall x y z h j b, zkp_one_out_of_two_validate h (zkp_one_out_of_two x y z h j b) ≈both ret_both (true : 'bool).
    intros.
    set (zkp_one_out_of_two _ _ _ _ _ _).

    assert (is_pure b0 = if is_pure b
                         then is_pure (@Build_t_OrZKPCommit
                                         (f_g_pow j)
                                         (f_prod (f_pow h j) f_g)
                                         (f_prod (f_g_pow (f_random_field_elem y)) (f_pow (f_g_pow j) (f_random_field_elem z)))
                                         (f_prod (f_pow h (f_random_field_elem y)) (f_pow (f_prod (f_pow h j) f_g) (f_random_field_elem z)))
                                         (f_g_pow (f_random_field_elem x))
                                         (f_pow h (f_random_field_elem x))
                                         (f_hash
                                            (impl__into_vec
                                               (unsize
                                                  (box_new
                                                     (array_from_list
                                                        [f_g_pow j; f_prod (f_pow h j) f_g;
                                                         f_prod (f_g_pow (f_random_field_elem y)) (f_pow (f_g_pow j) (f_random_field_elem z));
                                                         f_prod (f_pow h (f_random_field_elem y))
                                                           (f_pow (f_prod (f_pow h j) f_g) (f_random_field_elem z));
                                                         f_g_pow (f_random_field_elem x); f_pow h (f_random_field_elem x)])))))
                                         (f_random_field_elem z) (f_sub
                                                                    (f_hash
                                                                       (impl__into_vec
                                                                          (unsize
                                                                             (box_new
                                                                                (array_from_list
                                                                                   [f_g_pow j; f_prod (f_pow h j) f_g;
                                                                                    f_prod (f_g_pow (f_random_field_elem y))
                                                                                      (f_pow (f_g_pow j) (f_random_field_elem z));
                                                                                    f_prod (f_pow h (f_random_field_elem y))
                                                                                      (f_pow (f_prod (f_pow h j) f_g) (f_random_field_elem z));
                                                                                    f_g_pow (f_random_field_elem x); f_pow h (f_random_field_elem x)])))))
                                                                    (f_random_field_elem z)) (f_random_field_elem y) (f_sub (f_random_field_elem x)
                                                                                                                        (f_mul j
                                                                                                                           (f_sub
                                                                                                                              (f_hash
                                                                                                                                 (impl__into_vec
                                                                                                                                    (unsize
                                                                                                                                       (box_new
                                                                                                                                          (array_from_list
                                                                                                                                             [f_g_pow j; f_prod (f_pow h j) f_g;
                                                                                                                                              f_prod (f_g_pow (f_random_field_elem y))
                                                                                                                                                (f_pow (f_g_pow j) (f_random_field_elem z));
                                                                                                                                              f_prod (f_pow h (f_random_field_elem y))
                                                                                                                                                (f_pow (f_prod (f_pow h j) f_g) (f_random_field_elem z));
                                                                                                                                              f_g_pow (f_random_field_elem x); f_pow h (f_random_field_elem x)])))))
                                                                                                                              (f_random_field_elem z)))))
                         else is_pure (@Build_t_OrZKPCommit (f_g_pow j) (f_pow h j) (f_g_pow (f_random_field_elem x))
                                         (f_pow h (f_random_field_elem x))
                                         (f_prod (f_g_pow (f_random_field_elem y)) (f_pow (f_g_pow j) (f_random_field_elem z))) (f_prod (f_pow h (f_random_field_elem y)) (f_pow (f_div (f_pow h j) f_g) (f_random_field_elem z))) (f_hash
                                                                                                                                                                                                                                      (impl__into_vec
                                                                                                                                                                                                                                         (unsize
                                                                                                                                                                                                                                            (box_new
                                                                                                                                                                                                                                               (array_from_list
                                                                                                                                                                                                                                                  [f_g_pow j; f_pow h j; f_g_pow (f_random_field_elem x);
                                                                                                                                                                                                                                                   f_pow h (f_random_field_elem x);
                                                                                                                                                                                                                                                   f_prod (f_g_pow (f_random_field_elem y)) (f_pow (f_g_pow j) (f_random_field_elem z));
                                                                                                                                                                                                                                                   f_prod (f_pow h (f_random_field_elem y))
                                                                                                                                                                                                                                                     (f_pow (f_div (f_pow h j) f_g) (f_random_field_elem z))])))))
                                         (f_sub
                                            (f_hash
                                               (impl__into_vec
                                                  (unsize
                                                     (box_new
                                                        (array_from_list
                                                           [f_g_pow j; f_pow h j; f_g_pow (f_random_field_elem x);
                                                            f_pow h (f_random_field_elem x);
                                                            f_prod (f_g_pow (f_random_field_elem y))
                                                              (f_pow (f_g_pow j) (f_random_field_elem z));
                                                            f_prod (f_pow h (f_random_field_elem y))
                                                              (f_pow (f_div (f_pow h j) f_g) (f_random_field_elem z))])))))
                                            (f_random_field_elem z))
                                         (f_random_field_elem z)
                                         (f_sub (f_random_field_elem x)
                                            (f_mul j
                                               (f_sub
                                                  (f_hash
                                                     (impl__into_vec
                                                        (unsize
                                                           (box_new
                                                              (array_from_list
                                                                 [f_g_pow j; f_pow h j; f_g_pow (f_random_field_elem x);
                                                                  f_pow h (f_random_field_elem x);
                                                                  f_prod (f_g_pow (f_random_field_elem y))
                                                                    (f_pow (f_g_pow j) (f_random_field_elem z));
                                                                  f_prod (f_pow h (f_random_field_elem y))
                                                                    (f_pow (f_div (f_pow h j) f_g) (f_random_field_elem z))])))))
                                                  (f_random_field_elem z))))
                                         (f_random_field_elem y) )).
    { intros.
      unfold b0 at 1.
      rewrite zkp_one_out_of_two_equation_1.
      repeat unfold let_both at 1.
      unfold lift_both ; simpl.
      now destruct (is_pure b).
    }

    assert (forall {A B} (a : bool) (b c : A) (f : A -> B), f (if a then b else c) = if a then f b else f c) by now destruct a.
    do 2 rewrite <- H0 in H ; apply both_equivalence_is_pure_eq in H.

    eapply both_eq_trans ; [ apply both_eq_fun_ext, H | clear H b0 ].

    set (if _ then _ else _).
    rewrite zkp_one_out_of_two_validate_equation_1.

    eapply both_eq_trans ; [ apply both_eq_let_both | ].
    eapply both_eq_trans ; [ apply both_eq_solve_lift | ].

    repeat (eapply both_eq_trans ; [ apply both_eq_andb_true | ]) ; try rewrite <- both_eq_eqb_true.
    - eapply both_eq_trans ; [ | apply both_eq_symmetry ; apply (proj2 both_equivalence_is_pure_eq (hacspec_function_guarantees2 f_add _ _)) ].

      rewrite f_or_zkp_d1_equation_1; rewrite f_or_zkp_d2_equation_1 ; simpl.
      unfold y0 at 7 8.
      simpl.
      destruct (is_pure b).
      1: set (add_cancel := add_sub_cancel).
      2: set (add_cancel := add_sub_cancel2).
      1,2: rewrite !Build_t_OrZKPCommit_equation_1; simpl ; eapply both_eq_trans ; [ | apply (proj2 both_equivalence_is_pure_eq (hacspec_function_guarantees2 f_add _ _)) ] ; eapply both_eq_trans ; [ | apply both_eq_symmetry ; apply add_cancel ] ; do 4 apply both_eq_fun_ext ; now apply both_equivalence_is_pure_eq.
    - destruct (is_pure b).
      + rewrite f_or_zkp_r1_equation_1.
        rewrite f_or_zkp_a1_equation_1.
        rewrite f_or_zkp_x_equation_1.
        rewrite f_or_zkp_d1_equation_1.
        rewrite both_eq_guarantees ; subst y0 ; simpl ; rewrite !Build_t_OrZKPCommit_equation_1; simpl ; rewrite <- both_eq_guarantees.

        eapply both_eq_trans ; [ | apply both_eq_symmetry ; apply (proj2 both_equivalence_is_pure_eq (hacspec_function_guarantees2 f_prod _ _)) ].

        rewrite (hacspec_function_guarantees f_g_pow); simpl.
        rewrite <- (hacspec_function_guarantees f_g_pow).

        rewrite (hacspec_function_guarantees2 f_pow); simpl.
        rewrite <- (hacspec_function_guarantees2 f_pow).

        eapply both_eq_trans ; [ | apply (proj2 both_equivalence_is_pure_eq (hacspec_function_guarantees2 f_prod _ _)) ].

        repeat (apply both_eq_fun_ext2 || apply both_eq_fun_ext || apply both_eq_reflexivity).
      + rewrite f_or_zkp_r1_equation_1.
        rewrite f_or_zkp_a1_equation_1.
        rewrite f_or_zkp_x_equation_1.
        rewrite f_or_zkp_d1_equation_1.

        rewrite both_eq_guarantees ; simpl ; subst y0 ; simpl ; rewrite !Build_t_OrZKPCommit_equation_1 ; simpl ; rewrite <- both_eq_guarantees.

        eapply both_eq_trans ; [ | apply both_eq_symmetry ; apply (proj2 both_equivalence_is_pure_eq (hacspec_function_guarantees2 f_prod _ _)) ].

        rewrite (hacspec_function_guarantees f_g_pow (bind_both _ _)) ; simpl.
        rewrite <- (hacspec_function_guarantees f_g_pow).

        rewrite (hacspec_function_guarantees2 f_pow); simpl.
        rewrite <- (hacspec_function_guarantees2 f_pow).

        eapply both_eq_trans ; [ | apply (proj2 both_equivalence_is_pure_eq (hacspec_function_guarantees2 f_prod _ _)) ].

        eapply both_eq_trans ; [ | apply both_eq_symmetry ; apply prod_pow_add_mul ].

        apply both_eq_fun_ext.
        eapply both_eq_trans ; [ | apply both_eq_symmetry ; apply add_sub_cancel2 ].
        apply both_eq_reflexivity.
    - apply both_eq_reflexivity.
    - rewrite f_or_zkp_b1_equation_1.
      rewrite f_or_zkp_r1_equation_1.
      rewrite f_or_zkp_y_equation_1.
      rewrite f_or_zkp_d1_equation_1.

      destruct (is_pure b).
      +
        rewrite both_eq_guarantees ; simpl ; subst y0 ; simpl ; rewrite !Build_t_OrZKPCommit_equation_1 ; simpl ; rewrite <- both_eq_guarantees.

        eapply both_eq_trans ; [ | apply both_eq_symmetry ; apply (proj2 both_equivalence_is_pure_eq (hacspec_function_guarantees2 f_prod _ _)) ].

        rewrite (hacspec_function_guarantees2 f_pow); simpl.
        rewrite <- (hacspec_function_guarantees2 f_pow).

        rewrite (hacspec_function_guarantees2 f_pow (bind_both _ _)); simpl.
        rewrite <- (hacspec_function_guarantees2 f_pow).

        eapply both_eq_trans ; [ | apply (proj2 both_equivalence_is_pure_eq (hacspec_function_guarantees2 f_prod _ _)) ].

        apply both_eq_reflexivity.
      +

        rewrite both_eq_guarantees ; simpl ; subst y0 ; simpl ; rewrite !Build_t_OrZKPCommit_equation_1 ; simpl ; rewrite <- both_eq_guarantees.

        eapply both_eq_trans ; [ | apply both_eq_symmetry ; apply (proj2 both_equivalence_is_pure_eq (hacspec_function_guarantees2 f_prod _ _)) ].

        rewrite (hacspec_function_guarantees2 f_pow); simpl.
        rewrite <- (hacspec_function_guarantees2 f_pow).

        rewrite (hacspec_function_guarantees2 f_pow (bind_both _ _)); simpl.
        rewrite <- (hacspec_function_guarantees2 f_pow).

        eapply both_eq_trans ; [ | apply (proj2 both_equivalence_is_pure_eq (hacspec_function_guarantees2 f_prod _ _)) ].

        eapply both_eq_trans ; [ | apply both_eq_symmetry ; apply prod_pow_pow ].

        apply both_eq_fun_ext2.
        * apply both_eq_reflexivity.
        * eapply both_eq_trans ; [ | apply both_eq_symmetry ; apply add_sub_cancel2 ].
          apply both_eq_reflexivity.
    - apply both_eq_reflexivity.
    - rewrite f_or_zkp_a2_equation_1.
      rewrite f_or_zkp_r2_equation_1.
      rewrite f_or_zkp_x_equation_1.
      rewrite f_or_zkp_d2_equation_1.

      destruct (is_pure b).
      +
        rewrite both_eq_guarantees ; simpl ; subst y0 ; simpl ; rewrite !Build_t_OrZKPCommit_equation_1 ; simpl ; rewrite <- both_eq_guarantees.

        eapply both_eq_trans ; [ | apply both_eq_symmetry ; apply (proj2 both_equivalence_is_pure_eq (hacspec_function_guarantees2 f_prod _ _)) ].

        rewrite (hacspec_function_guarantees f_g_pow); simpl.
        rewrite <- (hacspec_function_guarantees f_g_pow).

        rewrite (hacspec_function_guarantees2 f_pow (bind_both _ _)); simpl.
        rewrite <- (hacspec_function_guarantees2 f_pow).

        eapply both_eq_trans ; [ | apply (proj2 both_equivalence_is_pure_eq (hacspec_function_guarantees2 f_prod _ _)) ].

        eapply both_eq_trans ; [ | apply both_eq_symmetry ; apply prod_pow_add_mul ].
        apply both_eq_fun_ext.
        eapply both_eq_trans ; [ | apply both_eq_symmetry ; apply add_sub_cancel2 ].
        apply both_eq_reflexivity.
      +
        rewrite both_eq_guarantees ; simpl ; subst y0 ; simpl ; rewrite !Build_t_OrZKPCommit_equation_1 ; simpl ; rewrite <- both_eq_guarantees.

        eapply both_eq_trans ; [ | apply both_eq_symmetry ; apply (proj2 both_equivalence_is_pure_eq (hacspec_function_guarantees2 f_prod _ _)) ].

        rewrite (hacspec_function_guarantees f_g_pow); simpl.
        rewrite <- (hacspec_function_guarantees f_g_pow).

        rewrite (hacspec_function_guarantees2 f_pow (bind_both _ _)); simpl.
        rewrite <- (hacspec_function_guarantees2 f_pow).

        eapply both_eq_trans ; [ | apply (proj2 both_equivalence_is_pure_eq (hacspec_function_guarantees2 f_prod _ _)) ].

        apply both_eq_reflexivity.
    - apply both_eq_reflexivity.
    -
      rewrite f_or_zkp_b2_equation_1.
      rewrite f_or_zkp_r2_equation_1.
      rewrite f_or_zkp_y_equation_1.
      rewrite f_or_zkp_d2_equation_1.

      destruct (is_pure b).
      +
        rewrite both_eq_guarantees ; simpl ; subst y0 ; simpl ; rewrite !Build_t_OrZKPCommit_equation_1 ; simpl ; rewrite <- both_eq_guarantees.

        eapply both_eq_trans ; [ | apply both_eq_symmetry ; apply (proj2 both_equivalence_is_pure_eq (hacspec_function_guarantees2 f_prod _ _)) ].

        rewrite (hacspec_function_guarantees2 f_pow); simpl.
        rewrite <- (hacspec_function_guarantees2 f_pow).

        rewrite (hacspec_function_guarantees2 f_pow (f_div _ _)); simpl.
        rewrite (hacspec_function_guarantees2 f_div); simpl.
        rewrite <- (hacspec_function_guarantees2 f_div).
        rewrite <- (hacspec_function_guarantees2 f_pow).

        eapply both_eq_trans ; [ | apply (proj2 both_equivalence_is_pure_eq (hacspec_function_guarantees2 f_prod _ _)) ].

        eapply both_eq_trans.
        2:{
          apply both_eq_symmetry.
          let H_in := fresh in
          set (H_in := f_prod _ _) ; pattern (f_div (f_prod (f_pow h j) f_g) f_g) in H_in ; subst H_in.
          apply both_eq_fun_ext.
          apply div_prod_cancel.
        }
        eapply both_eq_trans ; [ | apply both_eq_symmetry ; apply prod_pow_pow ].
        apply both_eq_fun_ext.
        eapply both_eq_trans ; [ | apply both_eq_symmetry ; apply add_sub_cancel2 ].
        apply both_eq_reflexivity.
      +
        rewrite both_eq_guarantees ; simpl ; subst y0 ; simpl ; rewrite !Build_t_OrZKPCommit_equation_1 ; simpl ; rewrite <- both_eq_guarantees.

        eapply both_eq_trans ; [ | apply both_eq_symmetry ; apply (proj2 both_equivalence_is_pure_eq (hacspec_function_guarantees2 f_prod _ _)) ].

        rewrite (hacspec_function_guarantees2 f_pow); simpl.
        rewrite <- (hacspec_function_guarantees2 f_pow).

        rewrite (hacspec_function_guarantees2 f_pow (f_div _ _)); simpl.
        rewrite (hacspec_function_guarantees2 f_div); simpl.
        rewrite <- (hacspec_function_guarantees2 f_div).
        rewrite <- (hacspec_function_guarantees2 f_pow).

        eapply both_eq_trans ; [ | apply (proj2 both_equivalence_is_pure_eq (hacspec_function_guarantees2 f_prod _ _)) ].

        eapply both_eq_trans.
        2:{
          apply both_eq_symmetry.
          let H_in := fresh in
          set (H_in := f_prod _ _) ; pattern (f_div (f_prod (f_pow h j) f_g) f_g) in H_in ; subst H_in.
          apply both_eq_fun_ext.
          apply div_prod_cancel.
        }
        apply both_eq_fun_ext2.
        {
          apply both_eq_reflexivity.
        }
        apply both_eq_reflexivity.
    - apply both_eq_reflexivity.
  Qed.

  Lemma schnorr_zkp_correct :
    forall x h z, schnorr_zkp_validate h (schnorr_zkp x h z) = ret_both (true : 'bool).
  Admitted.

  Module HacspecGP : GroupParam.
    Open Scope group_scope.
    Definition hacspec_group_type : Type := both f_group_type.
    HB.instance Definition _ : FinGroup hacspec_group_type := _.
    Definition gT : finGroupType := HacspecGP_hacspec_group_type__canonical__fingroup_FinGroup.
    Definition ζ : {set gT} := [set : gT].
    Definition g :  gT := f_g.
    Lemma g_gen : ζ = <[g]>.
    Proof.
      intros.
      unfold ζ, g.
      (* apply Zp_cycle. *)
    Admitted.

    Lemma prime_order : prime #[g].
    Proof.
      unfold g.
    Admitted.

  End HacspecGP.

  (* Theorem schnorr_com_binding : *)
  (*   forall LA A, *)
  (*     ValidPackage LA [interface *)
  (*                        #val #[ SOUNDNESS ] :  → 'bool *)
  (*       ] A_export A → *)
  (*     fdisjoint LA (Sigma_to_Com_locs :|: KEY_locs) → *)
  (*     AdvantageE (Com_Binding ∘ Sigma_to_Com ∘ KEY) (Special_Soundness_f) A <= 0. *)
  (* Proof. *)
  (*   intros LA A VA Hdisj. *)
  (*   eapply Order.le_trans. *)
  (*   1: apply Advantage_triangle. *)
  (*   instantiate (1 := Special_Soundness_t). *)
  (*   rewrite (commitment_binding LA A VA Hdisj). *)
  (*   setoid_rewrite (extractor_success LA A VA). *)
  (*   now setoid_rewrite GRing.isNmodule.add0r. *)
  (* Qed. *)

  (* Module Type HacspecSigmaProtocolParams. *)

End OVN_proofs.

(* Lemma vote_hiding (i j : pid) m: *)
(*   i != j → *)
(*   ∀ LA A ϵ_DDH, *)
(*     ValidPackage LA [interface #val #[ Exec i ] : 'bool → 'public] A_export A → *)
(*     fdisjoint Sigma1.MyAlg.Sigma_locs DDH.DDH_locs → *)
(*     fdisjoint LA DDH.DDH_locs → *)
(*     fdisjoint LA (P_i_locs i) → *)
(*     fdisjoint LA combined_locations → *)
(*     (∀ D, DDH.ϵ_DDH D <= ϵ_DDH) → *)
(*     AdvantageE (Exec_i_realised true m i j) (Exec_i_realised false m i j) A <= ϵ_DDH + ϵ_DDH. *)
