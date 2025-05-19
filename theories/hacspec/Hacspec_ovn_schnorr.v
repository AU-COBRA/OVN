(* begin details: Imports *)
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
From OVN Require Import Hacspec_ovn_group_and_field.
From OVN Require Import Hacspec_ovn_sigma_setup.

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

(* From mathcomp Require Import ring. *)
(* end details *)

(** * Instantiate Schnorr proof *)

Module OVN_schnorr_proof (HOP : HacspecOvnParameter) (HOGaFP : HacspecOvnGroupAndFieldParameter HOP) (HOGaFE : HacspecOvnGroupAndFieldExtra HOP HOGaFP) (HGPA : HacspecGroupParamAxiom HOP HOGaFP HOGaFE).
  Module Schnorr := Schnorr HGPA.GaFP.HacspecGroup.

  Import Schnorr.MyParam.
  Import Schnorr.MyAlg.

  Import Schnorr.Sigma.Oracle.
  Import Schnorr.Sigma.

  (* Include HGPA. *)
  (* Export HGPA. *)

  Import HOGaFE.GroupAndField.OVN.
  Import HGPA.GaFP.

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

  Lemma hacspec_run_valid :
    ValidPackage Sigma_locs (fset [::])
      [interface #val #[RUN] : chRelation → chTranscript ]
      [fmap (RUN,
           mkdef (choiceStatement × choiceWitness) choiceTranscript
             (λ '(h, x),
          #assert R (otf h) (otf x) ;;
          (
        r ← sample (uniform (H := Witness_pos) i_witness) ;;
        '(u,e,z) ← is_state (schnorr_zkp (ret_both (WitnessToField (otf r : 'Z_q))) (ret_both (otf h : v_G)) (ret_both (WitnessToField (otf x) : f_Z))) ;;
        ret ((h : choiceStatement, fto (u : Statement), fto (FieldToWitness e),fto (FieldToWitness z)) : choiceTranscript))
      ))].
  Proof.
    ssprove_valid.
    match goal with
    | [ |- context [ is_state ?b ] ] =>
        apply valid_scheme ; rewrite <- fset0E ; apply (ChoiceEquality.is_valid_code (both_prog_valid b))
    end.
  Qed.

  (* The packaged version for running the hacspec code *)
  Definition hacspec_run :
    package Sigma_locs
        [interface]
        [interface
          #val #[ RUN ] : chRelation → chTranscript
        ] :=
    {package _ #with hacspec_run_valid}.

  (* Adversary gets no advantage by running hacspec version *)
  Lemma hacspec_vs_RUN_interactive :
    ∀ LA A,
      ValidPackage LA [interface
                         #val #[ RUN ] : chRelation → chTranscript
        ] A_export A →
      fdisjoint LA Sigma_locs →
      AdvantageE hacspec_run RUN_interactive A = 0%R.
  Proof.
    intros.
    rewrite Advantage_sym.
    apply: eq_rel_perf_ind_ignore.
    2: apply hacspec_run.
    1: eapply valid_package_inject_export ; [ | apply RUN_interactive ] ; solve_in_fset.
    1: rewrite fsetUid ; apply fsubsetxx.
    2: apply H.
    2,3: apply H0.

    unfold eq_up_to_inv.
    simplify_eq_rel inp_unit.
    destruct inp_unit as [h xi].

    intros.

    inversion_clear H.
    apply r_assertD_same.
    intros.

    unfold R in e.
    apply (ssrbool.elimT eqP) in e.
    rewrite <- (fto_otf h).
    rewrite e. clear e.
    clear h.

    (* Unfold rhs *)
    unfold schnorr_zkp.

    (* Equate randomness *)
    eapply r_uniform_bij with (f := id) ; [ now apply inv_bij | intros ].
    (* apply better_r_put_lhs. *)
    simpl.

    rewrite bind_assoc.
    unfold let_both at 1.
    unfold let_both at 1.
    set (fun _ => let_both _ _).
    apply (@somewhat_let_substitutionR _ _ choiceTranscript _ _ (f_hash _) b).

    eapply r_transR.
    1:{
      set ([:: _; _; _]).
      eapply (HGPA.hash_is_psudorandom _ _ _ _ _ _ _ l).
      intros.
      unshelve instantiate (1 := (fun x0 => WitnessToField (otf x0))).
      simpl.

      rewrite bind_assoc.
      simpl.

      set (fun _ => _).
      apply better_r.
      eapply rpost_weaken_rule.
      1:{
        rewrite !bind_assoc.
        apply (somewhat_substitutionR).
        rewrite bind_rewrite.

        rewrite !bind_assoc.
        apply (somewhat_substitutionR).
        rewrite bind_rewrite.

        rewrite !bind_assoc.
        apply (somewhat_substitutionR).
        rewrite !bind_rewrite.

        now apply r_ret.
      }
      simpl. intros [] [] []. subst.
      reflexivity.
    }
    hnf.

    apply better_r_put_lhs.

    simpl.
    unfold i_random.
    simpl.
    unfold Schnorr.q.
    unfold q.

    eapply r_uniform_bij with (f := _).
    1: instantiate (1 := fun x => x) ; now apply inv_bij.
    intros.

    apply getr_set_lhs.
    apply r_ret.
    intros ? ? [? []].
    subst.

    split.
    2:{
      intros ? ?.
      rewrite get_set_heap_neq.
      1: apply H, H2.
      apply /eqP.
      red ; intros.
      subst.
      unfold Sigma_locs in H2.
      rewrite notin_fset in H2.

      unfold "\notin" in H2.
      unfold "\in" in H2.
      simpl in H2.
      rewrite eqxx in H2.
      easy.
    }

    repeat rewrite pair_equal_spec ; repeat split.

     * rewrite <- HGPA.conversion_is_true.
       rewrite FieldToWitnessCancel.
       reflexivity.
     * rewrite FieldToWitnessCancel.
       rewrite fto_otf.
       reflexivity.
     * rewrite <- FieldToWitnessCancel.
       (* Field isomorphism properties *)
       rewrite rmorphD.
       rewrite rmorphM.
       f_equal.
       f_equal.
       now Misc.push_down_sides.
  Qed.

End OVN_schnorr_proof.
