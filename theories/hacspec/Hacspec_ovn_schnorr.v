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
From OVN Require Import Hacspec_ovn_sigma_setup.

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

(** * Instantiate Schnorr proof *)

Module OVN_schnorr_proof (HGPA : HacspecGroupParamAxiom).
  Module Schnorr := Schnorr HGPA.HacspecGroup.

  Import Schnorr.MyParam.
  Import Schnorr.MyAlg.

  Import Schnorr.Sigma.Oracle.
  Import Schnorr.Sigma.

  Include HGPA.
  Export HGPA.

  Transparent schnorr_zkp.

  (* Transparent OVN.schnorr_zkp. *)
  Transparent run.

  (* Function mapping between results, to define what equal output means *)
  Definition schnorr_run_post_cond :
    tgt (RUN, (choiceStatement × choiceWitness, choiceTranscript))
    → t_SchnorrZKPCommit → Prop.
  Proof.
    simpl.
    intros [[[l1 l2] l3] l4] [[r1 r2] r3] ; cbn in *.
    refine (((otf l2) = r1) /\ (WitnessToField (otf l3) = r2) /\ (WitnessToField (otf l4) = r3)).
  Defined.

  (* Running Schnorr is equal to running OVN Schnorr implementation *)
 Lemma schnorr_run_eq  (pre : precond) :
    forall (b : Witness) c,
      Some c = lookup_op RUN_interactive (RUN, ((chProd choiceStatement choiceWitness), choiceTranscript)) ->
      ⊢ ⦃ pre ⦄
        c (fto (HacspecGroup.g ^+ b), fto b)
        ≈
        r ← sample uniform (2^32) ;;
        is_state (schnorr_zkp (ret_both (Hacspec_Lib_Pre.repr _ (Z.of_nat (nat_of_ord r)))) (ret_both ((HacspecGroup.g ^+ b))) (ret_both (WitnessToField b)))
          ⦃ fun '(x,_) '(y,_) => schnorr_run_post_cond x y  ⦄.
  Proof.
    intros.

    (* Unfold lhs *)
    cbn in H.
    destruct choice_type_eqP ; [ | discriminate ].
    destruct choice_type_eqP ; [ | discriminate ].
    rewrite cast_fun_K in H.
    clear e e1.
    inversion_clear H.
    rewrite !otf_fto; unfold R; rewrite eqxx; unfold assertD.

    (* Unfold rhs *)
    unfold schnorr_zkp.

    (* Equate randomness *)
    eapply rsymmetry ;
    eapply r_uniform_bij with (f := fun x => fto (FieldToWitness(is_pure (f_random_field_elem (t_Field := _) (ret_both (Hacspec_Lib_Pre.repr _ (Z.of_nat (nat_of_ord x)))))))) ; [ apply randomness_sample_is_bijective | intros ] ;
    eapply rsymmetry.

    apply better_r_put_lhs.

    (* Unfold definintions triple *)
    eapply (Misc.r_transR_both).
    {
      apply both_equivalence_is_pure_eq.
      repeat unfold let_both at 1.
      Transparent lift1_both.
      Transparent Build_t_SchnorrZKPCommit.
      simpl.
      apply Misc.prod_both_pure_eta_3.
    }

    (* Pull out definition of f_hash from triple *)
    eapply (Misc.r_transR_both).
    {
      symmetry.

      set (r := prod_b (_, _, _)).
      set (f_hash _) in r.
      pattern b0 in r.
      subst r.

      apply (bind_both_eta _ b0).
    }
    hnf.
    simpl.

    (* Equate hash with random oracle (Fiat-Shamir heuristic) *)
    eapply (hash_is_psudorandom i_random _ (fun x => WitnessToField (otf x)) _ _ _ _ [:: _; _; _]).
    intros.

    (* Read location *)
    apply getr_set_lhs.

    (* Make rhs pure *)
    set (ret _) ;
    set (prod_b (_,_,_)) ;
    apply (Misc.make_pure (x := r) (y := b0)) ;
    subst r b0.

    (* Show equality of return values *)
    apply r_ret.
    intros ; repeat split.
    * rewrite! otf_fto.
      (* Field isomorphism property *)
      apply conversion_is_true.
    * rewrite! otf_fto.
      (* Field isomorphism properties *)
      rewrite rmorphD.
      rewrite WitnessToFieldCancel.
      rewrite rmorphM.

      (* Equality up to `ret_both (is_pure _)` *)
      now Misc.push_down_sides.
  Qed.
End OVN_schnorr_proof.
