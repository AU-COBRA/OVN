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

From OVN Require Import Hacspec_ovn.
From OVN Require Import Hacspec_helpers.
From OVN Require Import Hacspec_ovn_group_and_field.
From OVN Require Import Hacspec_ovn_sigma_setup.
From OVN Require Import Hacspec_ovn_schnorr.
From OVN Require Import Hacspec_ovn_or.

Module OVN_proof (HOP : HacspecOvnParameter) (HOGaFP : HacspecOvnGroupAndFieldParameter HOP) (HOGaFE : HacspecOvnGroupAndFieldExtra HOP HOGaFP) (HGPA : HacspecGroupParamAxiom HOP HOGaFP HOGaFE).
  Module Schnorr_ZKP := OVN_schnorr_proof HOP HOGaFP HOGaFE HGPA.
  Module OR_ZKP := OVN_or_proof HOP HOGaFP HOGaFE HGPA.

  Definition r_bind_feq :
    forall {A B} (a b : raw_code A) (f g : A -> raw_code B) post,
      ⊢ ⦃ λ '(s₀, s₁), s₀ = s₁ ⦄ a ≈ b ⦃ Logic.eq ⦄
      → (∀ (a₀ : A), ⊢ ⦃ λ '(s₀, s₁), s₀ = s₁ ⦄ f a₀ ≈ g a₀ ⦃ post ⦄) →
      ⊢ ⦃ λ '(s₀, s₁), s₀ = s₁ ⦄ x ← a ;; f x ≈ x ← b ;; g x ⦃ post ⦄.
  Proof.
    intros.
    eapply r_bind with (mid := pre_to_post (λ '(s₀, s₁), s₀ = s₁)) ;
      [eapply rpost_weaken_rule ; [ apply H | now intros [] [] ? ]
      | intros ].
    apply rpre_hypothesis_rule ; intros ? ? [] ; eapply rpre_weaken_rule with (pre := (λ '(s₀, s₁), s₀ = s₁)) ; [ subst ; apply H0 | now simpl ; intros ? ? [] ].
  Qed.

  Definition somewhat_substitution : forall {A : choice_type} {B : choiceType} (b : both A) (f : A -> raw_code B) (c : raw_code B) pre,
      ⊢ ⦃ λ '(s₀, s₁), pre (s₀, s₁) ⦄ temp ← ret (is_pure b) ;; f temp ≈ c ⦃ λ '(b₀, s₀) '(b₁, s₁), b₀ = b₁ ∧ pre (s₀, s₁) ⦄ ->
      ⊢ ⦃ λ '(s₀, s₁), pre (s₀, s₁) ⦄ temp ← is_state b ;; f temp ≈ c ⦃ λ '(b₀, s₀) '(b₁, s₁), b₀ = b₁ ∧ pre (s₀, s₁) ⦄.
  Proof.
    clear ; intros ? ? ? ? ? ?.

    eapply r_transL.
    eapply r_bind.

    - apply r_nice_swap_rule ; [ easy | | apply p_eq ] ; now intros [] [] ; cbn.
    - intros.
      simpl.
      apply Misc.rpre_hypothesis_rule'.
      intros ? ? [[]].
      eapply rpre_weaken_rule.
      1: subst ; apply rreflexivity_rule.
      intros ? ? [].
      now subst.
  Qed.

  Definition somewhat_substitutionR : forall {A : choice_type} {B : choiceType} (b : both A) (f : A -> raw_code B) (c : raw_code B) pre,
      ⊢ ⦃ λ '(s₀, s₁), pre (s₀, s₁) ⦄ c ≈ temp ← ret (is_pure b) ;; f temp ⦃ λ '(b₀, s₀) '(b₁, s₁), b₀ = b₁ ∧ pre (s₀, s₁) ⦄ ->
      ⊢ ⦃ λ '(s₀, s₁), pre (s₀, s₁) ⦄ c ≈ temp ← is_state b ;; f temp ⦃ λ '(b₀, s₀) '(b₁, s₁), b₀ = b₁ ∧ pre (s₀, s₁) ⦄.
  Proof.
    clear ; intros ? ? ? ? ? ?.

    eapply r_transR.
    eapply r_bind.

    - apply r_nice_swap_rule ; [ easy | | apply p_eq ] ; now intros [] [] ; cbn.
    - intros.
      simpl.
      apply Misc.rpre_hypothesis_rule'.
      intros ? ? [[]].
      eapply rpre_weaken_rule.
      1: subst ; apply rreflexivity_rule.
      intros ? ? [].
      now subst.
  Qed.

  Lemma somewhat_let_substitution :
             forall {A C : choice_type} {B : choiceType} (f : C -> raw_code B) (c : raw_code B) (y : both A) (r : both A -> both C) pre,
               ⊢ ⦃ pre ⦄ b_temp ← is_state y ;; temp ← is_state (r (ret_both b_temp)) ;; f temp ≈ c ⦃ λ '(b₀, s₀) '(b₁, s₁), b₀ = b₁ ∧ pre (s₀, s₁) ⦄ ->
               ⊢ ⦃ pre ⦄ temp ← is_state (letb 'b := y in r ((b))) ;; f temp ≈ c ⦃ λ '(b₀, s₀) '(b₁, s₁), b₀ = b₁ ∧ pre (s₀, s₁) ⦄.
  Proof.
    intros.
    unfold let_both at 1.

    eapply r_transL.
    2:{ apply H. }
    rewrite <- bind_assoc.
    apply r_bind_feq.
    2:intros ; eapply rpost_weaken_rule ; [ apply rreflexivity_rule | now intros [] [] H0 ; inversion H0 ].

    pose (determ := (fun (y : both A) => both_deterministic y)).
    pose (y_det := both_deterministic y).

    pose (hd₀ := determ ).
    pose (hd₁ := deterministic_bind _ _ y_det (fun x => determ (ret_both x))).
    simpl in hd₁.

    eapply r_transL.
    1:{
      apply r_bind_feq.
      1:{
        apply r_nice_swap_rule ; [ easy | easy | ].
        epose p_eq.
        eapply rpost_weaken_rule.
        1: apply r0.
        1:now intros [] [] [[] ?].
      }
      intros.
      apply rreflexivity_rule.
    }
    simpl.

    apply both_pure_eq.
    now rewrite <- hacspec_function_guarantees.
  Qed.

  Lemma somewhat_let_substitutionR :
             forall {A C : choice_type} {B : choiceType} (f : C -> raw_code B) (c : raw_code B) (y : both A) (r : both A -> both C) pre,
               ⊢ ⦃ pre ⦄ c ≈ b_temp ← is_state y ;; temp ← is_state (r (ret_both b_temp)) ;; f temp ⦃ λ '(b₀, s₀) '(b₁, s₁), b₀ = b₁ ∧ pre (s₀, s₁) ⦄ ->
               ⊢ ⦃ pre ⦄ c ≈ temp ← is_state (letb 'b := y in r ((b))) ;; f temp ⦃ λ '(b₀, s₀) '(b₁, s₁), b₀ = b₁ ∧ pre (s₀, s₁) ⦄.
  Proof.
    intros.
    eapply r_transR.
    2:{ apply H. }
    rewrite <- bind_assoc.
    apply r_bind_feq.
    2:intros ; eapply rpost_weaken_rule ; [ apply rreflexivity_rule | now intros [] [] H0 ; inversion H0 ].

    pose (determ := (fun (y : both A) => both_deterministic y)).
    pose (y_det := both_deterministic y).

    pose (hd₀ := determ ).
    pose (hd₁ := deterministic_bind _ _ y_det (fun x => determ (ret_both x))).
    simpl in hd₁.

    eapply r_transL.
    1:{
      apply r_bind_feq.
      1:{
        apply r_nice_swap_rule ; [ easy | easy | ].
        epose p_eq.
        eapply rpost_weaken_rule.
        1: apply r0.
        1:now intros [] [] [[] ?].
      }
      intros.
      apply rreflexivity_rule.
    }
    simpl.

    apply both_pure_eq.
    now rewrite <- hacspec_function_guarantees.
  Qed.

  Ltac ssprove_valid_code :=
    rewrite <- fset0E
    ; ssprove_valid
    ; try match goal with
        | [ |- context [ is_state ?b ] ] =>
            apply (ChoiceEquality.is_valid_code (both_prog_valid b))
        end
    ; ssprove_valid'_2 ; apply (ChoiceEquality.is_valid_code (both_prog_valid _)).

  Ltac ssprove_same_head n :=
      apply (rsame_head_alt (L := fset0)) ; [ ssprove_valid_code | done | done | intros n ].

  Ltac ssprove_same_head_generic :=
      apply (rsame_head_alt (L := fset0)) ; [ ssprove_valid_code | done | done | intros ? ].

  Ltac ssprove_refl :=
      apply (r_reflexivity_alt (L := fset0)) ; [ ssprove_valid_code | done | done ].

  Ltac ssprove_sym :=
    apply r_nice_swap_rule ; [ easy | | apply p_eq ] ; now intros [] [] ; cbn.

  Ltac trim_is_interface :=
    setoid_rewrite filterm_set ; simpl ; fold chElement ;
    rewrite <- fset1E ;
    rewrite in_fset1 ;
    simpl ;
    rewrite eqxx ;
    rewrite filterm0 ;
    reflexivity.

  Ltac trimmed_package p :=
    match type of p with
    | package ?L ?I ?E =>
        assert (trimmed E p) by now unfold trimmed ; trim_is_interface
    end.

  Lemma fsubset_trans : forall (T : ordType) (a b c : {fset T}), a :<=: b -> b :<=: c -> a :<=: c.
  Proof.
    clear ; intros.
    apply /fsetUidPr.
    apply (ssrbool.elimT fsetUidPr) in H.
    apply (ssrbool.elimT fsetUidPr) in H0.
    rewrite <- H0 at 2.
    rewrite <- H.
    rewrite <- fsetUA.
    rewrite H0.
    reflexivity.
  Qed.

  Lemma trimmed_par :
    forall I1 I2 a b, Parable a b -> trimmed I1 a -> trimmed I2 b -> trimmed (I1 :|: I2) (par a b).
  Proof.
    intros.
    unfold trimmed.
    unfold trim.
    simpl.
    unfold par.

    rewrite filterm_union.
    1:{
      rewrite <- H0.
      rewrite <- H1.

      assert (forall (T : ordType) (S : Type) (a : {fmap T -> S}) (f g : T -> S -> bool),
            filterm f (filterm g a) = filterm (fun t s => f t s && g t s) a).
      {
        clear ; intros T S a f g.

        unfold filterm.
        simpl.
        apply eq_fmap.
        intros ?.
        cbn.
        f_equal.
        destruct a.
        simpl.
        clear i.
        induction fmval.
        - reflexivity.
        - cbn.
          destruct g ; simpl ; destruct f ; simpl;  now rewrite IHfmval.
      }

      rewrite H2.
      rewrite H2.
      f_equal.
      1:{
        apply eq_filterm.
        intros ? ?.
        destruct y as [? [? ?]].
        rewrite in_fsetU.
        set  (_ \in _).
        set  (_ \in _).
        now destruct b0.
      }
      1:{
        apply eq_filterm.
        intros ? ?.
        destruct y as [? [? ?]].
        rewrite in_fsetU.
        set  (_ \in _).
        set  (_ \in _).
        now destruct b1.
      }
    }
    {
      apply parable.
    }
  Qed.

  Lemma trimmed_link :
    forall E a b, trimmed E a -> trimmed E (a ∘ b).
  Proof.
    intros.
    unfold trimmed.
    rewrite <- link_trim_commut.
    rewrite H.
    done.
  Qed.

  Lemma parable_par_l :
    forall a b c, Parable a c -> Parable b c -> Parable (par a b) c.
  Proof.
    clear ; intros.
    unfold Parable.
    rewrite domm_union.
    rewrite fdisjointUl.
    rewrite H H0.
    reflexivity.
  Qed.

  Lemma parable_par_r :
    forall a b c, Parable c a -> Parable c b -> Parable c (par a b).
  Proof.
    clear ; intros.
    unfold Parable.
    rewrite domm_union.
    rewrite fdisjointUr.
    rewrite H H0.
    reflexivity.
  Qed.


  Ltac solve_Parable :=
    match goal with
    | [ |- context [ Parable (trim _ ?a) (trim _ ?b) ] ] =>
        apply parable_trim
        ; try (unfold idents
               ; rewrite <- !fset1E
               ; rewrite !imfset1
               ; now rewrite fdisjoint1s)
    | Ha : trimmed ?Ea ?a ,
        Hb : trimmed ?Eb ?b
      |- context [ Parable ?a ?b ] =>
        rewrite <- Ha ; rewrite <- Hb ; solve_Parable
    | Ha : trimmed ?Ea ?a ,
      Hb : trimmed ?Eb ?b
      |- context [ Parable ?a (?b ∘ ?c) ] =>
        rewrite <- Ha ;
        rewrite <- Hb ;
        erewrite !link_trim_commut ;
        solve_Parable
    | Ha : trimmed ?Ea ?a ,
        Hb : trimmed ?Eb ?b
      |- context [ Parable (?b ∘ ?c) ?a ] =>
        rewrite <- Ha ;
        rewrite <- Hb ;
        erewrite !link_trim_commut ;
        solve_Parable
    | |- context [ Parable ?a (par ?b ?c) ] =>
        apply parable_par_r ; solve_Parable
    | |- context [ Parable (par ?a ?b) ?c ] =>
        apply parable_par_l ; solve_Parable
    end.

  Ltac solve_trimmed :=
    match goal with
    | |- context [ trimmed ?E (par ?a ?b) ] =>
        apply trimmed_par ; [ solve_Parable | solve_trimmed.. ]
    | |- context [ trimmed ?E (?b ∘ ?c) ] =>
        apply trimmed_link ; solve_trimmed
    (* | |- context [ trimmed _ (?b ∘ ?c) ] => *)
    (*     assert (Hb : trimmed _ b) by solve_trimmed ; *)
    (*     rewrite <- Hb ; *)
    (*     rewrite link_trim_commut ; *)
    (*     solve_trimmed *)
    (* | [ |- context [ trimmed _ (par (trim _ ?a) (trim _ ?b ∘ ?c)) ] ] => *)
    (*     rewrite link_trim_commut ; *)
    (*     solve_trimmed *)
    (* | [ |- context [ trimmed _ (par ?a ?b) ] ] => *)
              (*     apply trimmed_par ; solve_Parable *)
    | _ => eassumption || shelve
    end.

  Ltac solve_valid_package :=
    match goal with
    | [ |- context [ ValidPackage ?L ?I ?E (pack ?a) ] ] =>
        apply a
    | [ |- context [ ValidPackage ?L ?I ?E (trim ?T ?a) ] ] =>
        apply valid_trim ; solve_valid_package
    (* | [ |- context [ ValidPackage ?L ?I ?E (?a ∘ ?b) ] ] => *)
    (*     apply valid_link ; solve_valid_package *)
    | [ |- context [ ValidPackage ?L ?I ?E (?a ∘ ?b) ] ] =>
        eapply valid_link_upto ; [ solve_valid_package | solve_valid_package | shelve | shelve ]
    (* | [ |- context [ ValidPackage ?L ?I ?E (par (trim _ ?a) (trim _ ?b)) ] ] => *)
    (*     apply valid_par ; [ *)
    (*       solve_Parable *)
    (*     | solve_valid_package | solve_valid_package ] *)
    | [ |- context [ ValidPackage ?L ?I ?E (par ?a ?b) ] ] =>
        eapply valid_par_upto ; [
          solve_Parable
        | solve_valid_package | solve_valid_package | shelve.. ]
    | [ |- context [ ValidPackage ?L ?I ?E (par (trim _ ?a) (trim _ ?b ∘ ?c)) ] ] =>
        rewrite link_trim_commut ;
        solve_valid_package
    | _ => idtac
    end.

  Ltac unfold_advantageE :=
    match goal with
    | [ |- context [ AdvantageE (?a ∘ ?b) (?a ∘ ?c) ] ] =>
        rewrite <- Advantage_link
    | [ |- context [ AdvantageE (par ?a (?b)) (par ?a (?c)) ?A ] ] =>
        erewrite (Advantage_par a b c A _ _ _ _ _)
        ; [
        | solve_valid_package | solve_valid_package | solve_valid_package
        |
        | solve_trimmed | solve_trimmed | solve_trimmed ]
    (* | [ |- context [ AdvantageE (par ?a (?b)) (par ?a (?c)) ?A ] ] => *)
    (*     pose 2%nat *)
    | _ => idtac
    end.


  Lemma bobble_sampleC :
    ∀
      {A : ord_choiceType}
      {C : _}
      (o : Op)
      (c : raw_code C)
      (v : raw_code A)
      (f : A -> Arit o -> raw_code C),
      ⊢ ⦃ λ '(h₀, h₁), h₀ = h₁ ⦄
        r ← sample o ;;
        a ← v ;;
        f a r ≈
        c ⦃ Logic.eq ⦄ <->
      ⊢ ⦃ λ '(h₀, h₁), h₀ = h₁ ⦄
        a ← v ;;
        r ← sample o ;;
        f a r ≈
        c ⦃ Logic.eq ⦄.
  Proof.
    intros.
    replace
      (a ← v ;; r ← sample o ;; f a r) with
      ('(a,r) ← (a ← v ;; r ← sample o ;; ret (a, r)) ;; f a r) by now rewrite bind_assoc.

    assert (H_eq : ⊢ ⦃ λ '(h₀, h₁), h₀ = h₁ ⦄
              x ← (a ← v ;;
                   r ← sample o ;;
                   ret (a, r)) ;;
            (let '(a, r) := x in f a r)
              ≈
              r ← sample o ;;
            a ← v ;;
            f a r
              ⦃ Logic.eq ⦄).
    {
      1:{
        eapply r_transR with (c₁ := '(a,r) ← _ ;; f a r).
        2: apply r_bind_feq ; [ apply rsamplerC | intros [] ].
        2: apply rreflexivity_rule.
        rewrite !bind_assoc.
        simpl.
        setoid_rewrite bind_assoc.
        simpl.
        apply rreflexivity_rule.
      }
    }

    split ; intros H ; (eapply r_transR ; [ apply H | clear H ])
                         ; [ | apply r_nice_swap_rule ; [ easy | easy | ] ] ; simpl ; apply H_eq.
  Qed.

  Lemma bobble_sample_uniform_putr :
    ∀
      {C : choiceType}
      {ℓ : Location}
      (o : nat) {Ho : Positive o}
      (c : raw_code C)
      (v : ℓ.π1)
      (f : Arit (uniform o) -> raw_code C),
      (forall (v : Arit (uniform o)), valid_code fset0 fset0 (f v)) ->
      ⊢ ⦃ λ '(h₀, h₁), h₀ = h₁ ⦄
        r ← sample uniform o ;;
        #put ℓ := v ;;
        f r ≈
        c ⦃ Logic.eq ⦄ ->
      ⊢ ⦃ λ '(h₀, h₁), h₀ = h₁ ⦄
        #put ℓ := v ;;
        r ← sample uniform o ;;
        f r ≈
        c ⦃ Logic.eq ⦄.
  Proof.
    intros ? ? ? ? ? ? ? ? H.
    eapply r_transR.
    1: apply H.
    apply better_r_put_lhs.
    apply r_uniform_bij with (f := id) ; [ now apply inv_bij | intros ].
    apply better_r_put_rhs.
    eapply rpost_weaken_rule.
    1:{
      set (pre := set_rhs _ _ _).
      refine (r_reflexivity_alt (L := fset0) pre _ _ _ _).
      1: rewrite <- fset0E ; apply (H0 _).
      all: easy.
    }
    now simpl ; intros [] [] [? [? [[? []] ?]]].
  Qed.

  (* Import Schnorr_ZKP. *)
  (* Import OR_ZKP. *)

  Include HGPA.

  From OVN Require Import OVN.

  Module OVN_GroupParam <: OVN.GroupParam.

    Definition n : nat := 55.
    Lemma n_pos : Positive n. Proof. easy. Qed.

    Include HGPA.GaFP.HacspecGroup.
  End OVN_GroupParam.

  Module OVN_Param <: OVNParam.
    Definition N : nat := 55.
    Lemma N_pos : Positive N. Proof. easy. Qed.
  End OVN_Param.

  Module OVN_proofs := OVN OVN_GroupParam OVN_Param.

  Module OVN_or <: OVN_proofs.CDSParams.
    Include OR_ZKP.proof_args.MyParam.
    Definition State : finType := 'unit.
    Instance State_pos : Positive #|State| := eq_ind_r [eta Positive] (erefl : Positive 1) card_unit.
  End OVN_or.

  Module OVN_old_proofs := OVN_proofs.OVN OVN_or OR_ZKP.proof_args.MyAlg.

  Import HOGaFE.GroupAndField.OVN.
  (* Import HOGaFE.GroupAndField. *)
  (* Import HOGaFE. *)
  Import HGPA.GaFP.
  Import HGPA.GaFP.HacspecGroup.
  From Crypt Require Import choice_type Package Prelude.
  Import PackageNotation.


  Definition full_protocol_transcript : choice_type :=
    (* Round 1 *)
    nseq t_SchnorrZKPCommit OVN_Param.N (* schnorr_zkp *) ×
    nseq v_G OVN_Param.N × (* ddh_pk *)  (* g^{x_i} hiding x_i by DDH *)

    (* Round 2 *)
    nseq v_G OVN_Param.N × (* commit *)

    (* Round 3 *)
    nseq t_OrZKPCommit OVN_Param.N × (* or *)
    nseq v_G OVN_Param.N (* vote *)

    (* Round 4 - Check values *).

  Definition protocol_input : choice_type :=
    (* Round 1 *)
    'nat × (* i *)

    (* Round 2 *)
    nseq v_G OVN_Param.N × (* commit *)

    (* Round 3 *)
    nseq t_OrZKPCommit OVN_Param.N × (* or *)
    nseq v_G OVN_Param.N (* vote *)

    (* Round 4 - Check values *).

  (* Definition schnorr_zkp (x : full_protocol_transcript) := *)
  (*   let '(schnorr_zkp, ddh_pk, commit, or, vote) := x in *)
  (*   schnorr_zkp. *)

  Notation " 'chInputOvn' " :=
    (protocol_input)
    (in custom pack_type at level 2).

  Notation " 'chTranscriptOvn' " :=
    (full_protocol_transcript)
    (in custom pack_type at level 2).

  Notation " 'chRound1input' " :=
    (f_Z)
    (in custom pack_type at level 2).

  Notation " 'chRound1output' " :=
    (t_SchnorrZKPCommit × v_G)
    (in custom pack_type at level 2).

  Definition ROUND1 : nat := 12.

  Program Definition round1 (i : nat) (state : both t_OvnContractState) :
    package fset0
      [interface]
      [interface #val #[ ROUND1 ] : chRound1input → chRound1output]
    :=
    [package
        #def #[ ROUND1 ] (xi : chRound1input) : chRound1output
        {
          ri ← sample (uniform #|'Z_q|) ;;
          temp ← is_state (register_vote (ret_both ((i, xi, WitnessToField (otf ri)) : t_RegisterParam)) state) ;;
          match temp : t_Result (v_A × t_OvnContractState) t_ParseError with
          | Result_Ok_case (_ , new_state) =>
              zkp_i ← is_state (A := t_SchnorrZKPCommit) ((f_zkp_xis (ret_both (new_state : t_OvnContractState))).a[ ret_both (i : int32) ]) ;;
              g_pow_xi ← is_state ((f_g_pow_xis (ret_both (new_state : t_OvnContractState))).a[ ret_both (i : int32) ]) ;;
              ret (zkp_i , g_pow_xi)
          | Result_Err_case _ => ret (chCanonical t_SchnorrZKPCommit, chCanonical _)
          end
        }
    ].
  Solve All Obligations with now intros ; destruct from_uint_size.
  Next Obligation.
    fold chElement.
    intros.
    rewrite <- fset0E.
    ssprove_valid_package.
    ssprove_valid.
    1: apply (ChoiceEquality.is_valid_code (both_prog_valid _)).
    ssprove_valid'_2 ;  apply (ChoiceEquality.is_valid_code (both_prog_valid _)).
  Qed.
  Fail Next Obligation.

  Import OVN_old_proofs. (* 'public_key *)
  Program Definition round1_by_old (i : nat) (xi : f_Z) (state : both t_OvnContractState) :
    package fset0
      [interface #val #[ INIT ] : 'unit → 'public_key]
      [interface #val #[ ROUND1 ] : 'unit → chRound1output]
    :=
    [package
        #def #[ ROUND1 ] (_ : 'unit) : chRound1output
        {
          #import {sig #[ INIT ] : 'unit → 'public_key } as init ;;
          '(y,(s,m,c,r)) ← init Datatypes.tt ;;
          ret ((otf m : v_G, WitnessToField (otf c) : f_Z, WitnessToField (otf r) : f_Z) (* z, c, u *),otf y : v_G)
        }
    ].
  Solve All Obligations with now intros ; destruct from_uint_size.
  Next Obligation.
    fold chElement.
    intros.
    ssprove_valid_package.
    ssprove_valid.
    destruct x0 as [].
    destruct s0 as [[[]]].
    ssprove_valid.
  Qed.
  Fail Next Obligation.

  Notation " 'chRound2input' " :=
    (f_Z)
    (in custom pack_type at level 2).

  Notation " 'chRound2output' " :=
    (f_Z)
    (in custom pack_type at level 2).

  Definition ROUND2 : nat := 15 + OVN_Param.N.

  Program Definition round2 (i : nat) (vi : bool) (state : both t_OvnContractState) :
    package fset0
      [interface]
      [interface #val #[ ROUND2 ] : chRound2input → chRound2output]
    :=
    [package
        #def #[ ROUND2 ] (xi : chRound2input) : chRound2output
        {
          temp ← is_state (commit_to_vote (ret_both ((i, xi, is_pure f_field_zero, is_pure f_field_zero, is_pure f_field_zero, vi) : t_CastVoteParam)) state) ;;
          match temp : t_Result (v_A × t_OvnContractState) t_ParseError with
          | Result_Ok_case (_ , new_state) =>
              is_state (A := f_Z) ((f_commit_vis (ret_both (new_state : t_OvnContractState))).a[ ret_both (i : int32) ])
          | Result_Err_case _ => ret (chCanonical _)
          end
        }
    ].
  Solve All Obligations with now intros ; destruct from_uint_size.
  Next Obligation.
    fold chElement.
    intros.
    rewrite <- fset0E.
    ssprove_valid_package.
    (* destruct x as xi. *)
    ssprove_valid.
    1: apply (ChoiceEquality.is_valid_code (both_prog_valid _)).
    ssprove_valid'_2 ;  apply (ChoiceEquality.is_valid_code (both_prog_valid _)).
  Qed.
  Fail Next Obligation.

  Notation " 'chRound3input' " :=
    (f_Z × (f_Z × f_Z × f_Z))
    (in custom pack_type at level 2).

  Notation " 'chRound3output' " :=
    (v_G × t_OrZKPCommit)
    (in custom pack_type at level 2).

  Definition ROUND3 : nat := 15 + 2 * OVN_Param.N.

  Import OR_ZKP.proof_args.Sigma.

  Program Definition simple_round3 (i : nat) (vi : bool) (state : both t_OvnContractState) :
    package fset0
      [interface]
      [interface #val #[ ROUND3 ] : chRound3input → chRound3output]
    :=
    [package
        #def #[ ROUND3 ] ('(xi, (w,r,d)) : chRound3input) : chRound3output
        {
          #import {sig #[ OR_ZKP.proof_args.Sigma.RUN ] : chRelation → chTranscript } as RUN_OR ;;

          temp ← is_state (cast_vote (ret_both ((i, xi, w, r, d, vi) : t_CastVoteParam)) state) ;;
          match temp : t_Result (v_A × t_OvnContractState) t_ParseError with
          | Result_Ok_case (_ , new_state) =>
              vote_i ← is_state (A := v_G) ((f_g_pow_xi_yi_vis (ret_both (new_state : t_OvnContractState))).a[ ret_both (i : int32) ]) ;;
              or_zkp_i ← is_state (A := t_OrZKPCommit) ((f_zkp_vis (ret_both (new_state : t_OvnContractState))).a[ ret_both (i : int32) ]) ;;
              ret (vote_i, or_zkp_i)
          | Result_Err_case _ => ret (chCanonical _, chCanonical _)
          end
        }
    ].
  Solve All Obligations with now intros ; destruct from_uint_size.
  Next Obligation.
    fold chElement.
    intros.
    ssprove_valid_package.
    destruct x as [xi [[w r] d]].
    ssprove_valid.
    1: apply valid_scheme ; rewrite <- fset0E ; apply (ChoiceEquality.is_valid_code (both_prog_valid _)).
    ssprove_valid'_2 ;  apply valid_scheme ; rewrite <- fset0E ; apply (ChoiceEquality.is_valid_code (both_prog_valid _)).
  Qed.
  Fail Next Obligation.

  Import DDH.
  Module DDHParams <: DDH.DDHParams.
    Definition Space := 'Z_q : finType.
    Definition Space_pos : Positive #|Space|.
    Proof.
      apply /card_gt0P. exists 0%R. auto.
    Qed.
  End DDHParams.
  Module DDH := DDH.DDH DDHParams HGPA.GaFP.HacspecGroup.

  Notation " 'MBS_ass_input' " :=
    (f_Z × v_G)
    (in custom pack_type at level 2).

  Notation " 'MBS_ass_output' " :=
    (v_G)
    (in custom pack_type at level 2).

  Definition ASS := 101%nat.

  Program Definition real_assumption_pkg (vi : bool) :
    package (fset [::])
      [interface]
      [interface #val #[ ASS ] : MBS_ass_input → MBS_ass_output ]
    :=
    [package
        #def #[ ASS ] ('(xi, g_pow_yi) : MBS_ass_input) : MBS_ass_output
        {
          (* is_state (solve_lift f_prod (f_pow (ret_both g_pow_yi) (ret_both (xi))) (f_g_pow (if vi then f_field_one else f_field_zero))) *)

          (* letb g_pow_xi_yi_vi := *) is_state (compute_group_element_for_vote (ret_both xi) (ret_both (vi : 'bool)) (ret_both g_pow_yi)) (* in *)
        }
    ].
  Next Obligation.
    intros.
    ssprove_valid.
    destruct x as [xi g_pow_yi].
    ssprove_valid.
    1: apply valid_scheme ; rewrite <- fset0E ; apply (ChoiceEquality.is_valid_code (both_prog_valid _)).
  Qed.
  Fail Next Obligation.

  Program Definition maximum_ballot_secrecy_assumption_pkg (vi : bool) :
    package (fset [::])
      [interface]
      [interface #val #[ ASS ] : MBS_ass_input → MBS_ass_output ]
    :=
    [package
       #def #[ ASS ] ('(_, g_pow_yi) : MBS_ass_input) : MBS_ass_output
        {
          xi ← sample (uniform #|'Z_q|) ;;
          if g_pow_yi == (g ^+ (0%R : 'Z_q))%g
          then fail
          else is_state (solve_lift f_prod (f_pow (ret_both g_pow_yi) (ret_both (WitnessToField (otf xi)))) (f_g_pow (if vi then f_field_one else f_field_zero)))
        }
    ].
  Next Obligation.
    intros.
    ssprove_valid.
    destruct x as [xi g_pow_yi].
    ssprove_valid.
    1: apply valid_scheme ; rewrite <- fset0E ; apply (ChoiceEquality.is_valid_code (both_prog_valid _)).
  Qed.
  Fail Next Obligation.

  Lemma cyclic_group_to_exponent :
    forall x,
    ∃ i : nat, x = g ^+ i.
  Proof.
    intros.
    apply (ssrbool.elimT (cycleP HacspecGroup.g x)).
    {
      unfold HacspecGroup.gT in x.
      unfold HacspecGroup.g.
      setoid_rewrite <- HOGaFE.v_G_g_gen.
      simpl.
      apply in_setT.
    }
  Qed.

  Lemma maximum_ballot_secrecy_assumption :
    (* forall g_pow_yi, *)
    (*   g_pow_yi <> g ^+ (0%R : 'Z_q) -> *)
    ∀ (LA : {fset Location}) (A : raw_package),
     ValidPackage LA [interface #val #[ ASS ] : MBS_ass_input → MBS_ass_output ] A_export A →
     (* fdisjoint LA OR_ZKP.proof_args.MyAlg.Sigma_locs → *)
     (* let prot := fun vi => (protocol ∘ (par (round1 i xi state) (par (round2 i xi vi state) (round3 i xi vi state ∘ OR_ZKP.hacspec_or_run)))) in *)
      AdvantageE
        (maximum_ballot_secrecy_assumption_pkg true)
        (maximum_ballot_secrecy_assumption_pkg false)
        A = 0%R.
  Proof.
    intros ? ? H1 .

    apply: eq_rel_perf_ind_ignore.
    1: apply fsubsetxx.
    2,3: rewrite <- fset0E ; apply fdisjoints0.

    simplify_eq_rel inp.
    clear hin.

    destruct inp as [xi' g_pow_yi].

    replace (g ^+ 0) with (g ^+ (0%R : 'Z_q)) by reflexivity.
    destruct (_ == _%g) eqn:H.
    {
      apply (r_reflexivity_alt (L := fset0)).
      1: ssprove_valid.
      1, 2: easy.
    }
    apply (ssrbool.elimF eqP) in H.

    assert (g_pow_split : exists (yi : v_Z), g_pow_yi = g ^+ FieldToWitness yi /\ FieldToWitness yi <> 0%R).
    {
      destruct (cyclic_group_to_exponent g_pow_yi).

      exists (WitnessToField (inord (x %% (Zp_trunc q).+2))).
      rewrite FieldToWitnessCancel.

      subst.
      split.
      2: red ; intros ; apply H ; setoid_rewrite <- H0.

      all: rewrite inordK ; [ | easy].
      all: rewrite !trunc_pow.
      all: done.
    }

    destruct g_pow_split as [yi [? ?]] ; subst.

    assert (yi_is_unit : FieldToWitness yi \is a GRing.unit).
    {
      clear -H2.
      apply rmorph_unit. rewrite unitfE. apply /eqP.

      red ; intros.
      apply H2.
      rewrite H.
      now rewrite rmorph0.
    }

    eapply (r_uniform_bij) with (f := _) ; [ | intros xi ].
    1: shelve.

    epose (OVN_old_proofs.vote_hiding_bij ((fto (FieldToWitness yi * (otf xi))%R) : OVN_proofs.secret) true).

    eapply f_equal with (f := otf) in e.
    rewrite !OVN_old_proofs.Hord in e.
    rewrite !otf_fto in e.

    rewrite <- bind_ret at 1.
    rewrite <- bind_ret.

    apply somewhat_substitution.
    apply somewhat_substitutionR.

    apply r_ret.
    intros.
    split ; [ clear H | easy ].

    Misc.push_down_sides.
    rewrite !(proj1 both_equivalence_is_pure_eq (HOGaFE.pow_base _)).

    rewrite <- pow_witness_to_field.
    rewrite <- expgM.

    rewrite <- (WitnessToFieldCancel (is_pure f_field_one)).
    rewrite <- (WitnessToFieldCancel (is_pure f_field_zero)).
    Misc.push_down_sides.
    rewrite <- !pow_witness_to_field.

    rewrite rmorph1. rewrite rmorph0.

    unfold "*"%g in e.
    simpl in e.
    unfold setoid_lower2, F, U, sg_prod in e ; simpl in e.
    rewrite !trunc_pow in e.

    setoid_rewrite e.

    f_equal.
    f_equal.
    f_equal.
    f_equal.

    rewrite expgD.
    rewrite !trunc_pow.
    rewrite <- expgD.
    rewrite <- expgM.

    replace (g ^+ (FieldToWitness yi * otf xi + 1)%N) with (g ^+ (nat_of_ord (FieldToWitness yi * otf xi + 1)%R)).
    2:{
      simpl.
      rewrite !trunc_pow.
      rewrite !expgD.
      rewrite !trunc_pow.
      rewrite !expgM.
      reflexivity.
    }

    Unshelve.
    3:{
      intros x.
      apply (fto).
      cbn.

      refine ((FieldToWitness yi * otf x + 1%R) / (FieldToWitness yi))%R.
    }
    2:{
      eapply (Bijective (g := fun x => fto ((FieldToWitness yi * otf x - 1) / FieldToWitness yi)%R)).
      1:{
        intros xi.
        rewrite otf_fto.

        rewrite (mulrC (FieldToWitness yi * otf xi + 1)%R).
        rewrite mulrA.
        rewrite mulrV.
        2: apply yi_is_unit.
        rewrite mul1r.
        rewrite <- addrA.
        rewrite addrN.
        rewrite addr0.
        rewrite (mulrC _ (otf xi)).
        rewrite <- mulrA.
        rewrite mulrV.
        2: apply yi_is_unit.
        rewrite mulr1.
        rewrite fto_otf.
        reflexivity.
      }
      {
        intros xi.
        rewrite otf_fto.

        rewrite (mulrC (FieldToWitness yi * otf xi - 1)%R).
        rewrite mulrA.
        rewrite mulrV.
        2: apply yi_is_unit.
        rewrite mul1r.
        rewrite <- addrA.
        rewrite addNr.
        rewrite addr0.
        rewrite (mulrC _ (otf xi)).
        rewrite <- mulrA.
        rewrite mulrV.
        2: apply yi_is_unit.
        rewrite mulr1.
        rewrite fto_otf.
        reflexivity.
      }
    }

    hnf.
    rewrite otf_fto.

    replace (g ^+ (FieldToWitness yi * ((FieldToWitness yi * otf xi + 1) / FieldToWitness yi)%R)) with
      (g ^+ (FieldToWitness yi * ((FieldToWitness yi * otf xi + 1) / FieldToWitness yi))%R).
    2:{
      simpl.
      rewrite !trunc_pow.
      reflexivity.
    }

    f_equal.
    Set Printing Coercions.
    f_equal.

    From mathcomp Require Import ring.
    Fail field.

    rewrite (mulrC (FieldToWitness yi * otf xi + 1)%R).
    rewrite mulrA.
    rewrite mulrV.
    2: apply yi_is_unit.
    rewrite mul1r.
    reflexivity.
  Qed.

  (* Definition i nseq v_G (is_pure (n)) *)

  (* The packaged version for running the hacspec code *)

  Import OR_ZKP.proof_args.Sigma.

  (* Notation " 'chR3inp' " := *)
  (*   (chProd (chProd (chProd  f_Z f_Z) f_Z) (chProd OR_ZKP.proof_args.MyAlg.choiceStatement OR_ZKP.proof_args.MyAlg.choiceWitness)) *)
  (*   (in custom pack_type at level 2). *)

  (* Program Definition hacspec_or_run : *)
  (*   package OR_ZKP.proof_args.MyAlg.Sigma_locs *)
  (*       [interface] *)
  (*       [interface *)
  (*         #val #[ OR_ZKP.proof_args.Sigma.RUN ] : chR3inp → chTranscript *)
  (*       ] := *)
  (*   [package #def #[ OR_ZKP.proof_args.Sigma.RUN ] ('((wr, rr, dr), b) : chR3inp) : chTranscript *)
  (*      { *)
  (*        #assert OR_ZKP.proof_args.MyParam.R (otf b.1) (otf b.2) ;; *)
  (*        v ← is_state (zkp_one_out_of_two *)
  (*                     (ret_both wr) *)
  (*                     (ret_both rr) *)
  (*                     (ret_both dr) *)
  (*                     (ret_both (snd (fst (otf (fst b))))) *)
  (*                     (ret_both (WitnessToField (fst (fst (otf (snd b)))))) *)
  (*                     (ret_both ((snd (otf (fst b)) == (snd (fst (otf (fst b))) ^+  (fst (fst (otf (snd b))))) * g)%g : 'bool))) ;; *)
  (*        ret (OR_ZKP.hacspec_ret_to_or_sigma_ret (otf b.1) v) *)
  (*      } *)
  (*   ]. *)
  (* (* begin hide *) *)
  (* Next Obligation. *)
  (*   intros. *)
  (*   eapply (valid_package_cons _ _ _ _ _ _ [] []). *)
  (*   - apply valid_empty_package. *)
  (*   - intros. *)
  (*     ssprove_valid. *)
  (*     destruct x as [[[wr rr] dr] [stm wit]]. *)
  (*     ssprove_valid. *)
  (*     set (zkp_one_out_of_two _ _ _ _ _ _). *)
  (*     apply valid_scheme. *)
  (*     rewrite <- fset0E. *)
  (*     apply (ChoiceEquality.is_valid_code (both_prog_valid b)). *)
  (*   - try (rewrite <- fset0E ; setoid_rewrite @imfset0 ; rewrite in_fset0 ; reflexivity). *)
  (* Qed. *)
  (* Fail Next Obligation. *)
  (* (* end hide *) *)

  (* Program Definition hacspec_or_run_sample : *)
  (*   package OR_ZKP.proof_args.MyAlg.Sigma_locs *)
  (*       [interface] *)
  (*       [interface *)
  (*         #val #[ OR_ZKP.proof_args.Sigma.RUN ] : chR3inp → chTranscript *)
  (*       ] := *)
  (*   [package #def #[ OR_ZKP.proof_args.Sigma.RUN ] ('(_, b) : chR3inp) : chTranscript *)
  (*      { *)
  (*        #assert OR_ZKP.proof_args.MyParam.R (otf b.1) (otf b.2) ;; *)
  (*        wr ← sample uniform #|'Z_q| ;; *)
  (*        dr ← sample uniform #|'Z_q| ;; *)
  (*        rr ← sample uniform #|'Z_q| ;; *)
  (*        v ← is_state (zkp_one_out_of_two *)
  (*                     (ret_both (WitnessToField (otf wr))) *)
  (*                     (ret_both (WitnessToField (otf rr))) *)
  (*                     (ret_both (WitnessToField (otf dr))) *)
  (*                     (ret_both (snd (fst (otf (fst b))))) *)
  (*                     (ret_both (WitnessToField (fst (fst (otf (snd b)))))) *)
  (*                     (ret_both ((snd (otf (fst b)) == (snd (fst (otf (fst b))) ^+  (fst (fst (otf (snd b))))) * g)%g : 'bool))) ;; *)
  (*        ret (OR_ZKP.hacspec_ret_to_or_sigma_ret (otf b.1) v) *)
  (*      } *)
  (*   ]. *)
  (* (* begin hide *) *)
  (* Next Obligation. *)
  (*   intros. *)
  (*   eapply (valid_package_cons _ _ _ _ _ _ [] []). *)
  (*   - apply valid_empty_package. *)
  (*   - intros. *)
  (*     ssprove_valid. *)
  (*     destruct x as [[[wr rr] dr] [stm wit]]. *)
  (*     ssprove_valid. *)
  (*     set (zkp_one_out_of_two _ _ _ _ _ _). *)
  (*     apply valid_scheme. *)
  (*     rewrite <- fset0E. *)
  (*     apply (ChoiceEquality.is_valid_code (both_prog_valid b)). *)
  (*   - try (rewrite <- fset0E ; setoid_rewrite @imfset0 ; rewrite in_fset0 ; reflexivity). *)
  (* Qed. *)
  (* Fail Next Obligation. *)
  (* (* end hide *) *)

  (* Lemma protocol_is_real_protocol_temp : *)
  (*   ∀ (LA : {fset Location}) (A : raw_package), *)
  (*    ValidPackage LA [interface #val #[ OR_ZKP.proof_args.Sigma.RUN ] : chR3inp → chTranscript ] A_export A → *)
  (*    fdisjoint LA OR_ZKP.proof_args.MyAlg.Sigma_locs → *)
  (*    (* forall vi, *) *)
  (*     AdvantageE *)
  (*       (hacspec_or_run) *)
  (*       (hacspec_or_run_sample) *)
  (*       A = 0%R. *)
  (* Proof. *)
  (*   intros. *)
  (*   apply: eq_rel_perf_ind_ignore. *)
  (*   1: apply fsubsetxx. *)
  (*   2,3: apply H0. *)

  (*   unfold eq_up_to_inv. *)
  (*   simplify_eq_rel inp_unit. *)
  (*   destruct inp_unit as [[[wr dr] rr] [stm wit]]. *)
  (*   simpl. *)
  (* Qed. *)

  (* Lemma protocol_is_real_protocol : *)
  (*   forall (i : nat) state, *)
  (*   ∀ (LA : {fset Location}) (A : raw_package), *)
  (*    ValidPackage LA [interface #val #[ PROTOCOL ] : 'unit → chProtocolOutput ] A_export A → *)
  (*    fdisjoint LA OR_ZKP.proof_args.MyAlg.Sigma_locs → *)
  (*    forall vi, *)
  (*     AdvantageE *)
  (*       (real_protocol_insance i vi state) *)
  (*       (real_protocol i vi state) *)
  (*       A = 0%R. *)
  (* Proof. *)
  (*   intros. *)
  (*   apply: eq_rel_perf_ind_ignore. *)
  (*   1: apply fsubsetxx. *)
  (*   2,3: apply fdisjoints0. *)
  (* Qed. *)

  Program Definition round3 (i : nat) (vi : bool) (state : both t_OvnContractState) :
    package fset0
      [interface
         #val #[ OR_ZKP.proof_args.Sigma.RUN ] : chRelation → chTranscript
       ; #val #[ ASS ] : MBS_ass_input → MBS_ass_output
       (* ; #val #[ DDH.SAMPLE ] : 'unit → 'group × 'group × 'group *)
      ]
      [interface #val #[ ROUND3 ] : chRound3input → chRound3output]
    :=
    [package
        #def #[ ROUND3 ] ('(xi, (w,r,d)) : chRound3input) : chRound3output
        {
          #import {sig #[ OR_ZKP.proof_args.Sigma.RUN ] : chRelation → chTranscript } as RUN_OR ;;
          #import {sig #[ ASS ] : MBS_ass_input → MBS_ass_output } as ASS1 ;;

          let cast_vote :=
            fun (params : both t_CastVoteParam) (state : both (t_OvnContractState)) =>
              g_pow_yi ← is_state (compute_g_pow_yi (cast_int (WS2 := U32) (f_cvp_i params)) (f_g_pow_xis state)) ;;
              let g_pow_yixi := (g_pow_yi : gT) ^+ (FieldToWitness xi) in
              zkp_vi ← RUN_OR
                (fto (g ^+ FieldToWitness xi,
                     (g_pow_yi : gT), (* g_pow_yi = h *)
                     g_pow_yixi * g ^+ vi),
                  fto ( FieldToWitness xi , vi , (g_pow_yi : gT) ))%g ;;
              let zkp_vi := OR_ZKP.or_sigma_ret_to_hacspec_ret zkp_vi in
              g_pow_xi_yi_vi ← ASS1 (xi, g_pow_yi) ;;
              let g_pow_xi_yi_vi := ret_both g_pow_xi_yi_vi in
              is_state (
              letb cast_vote_state_ret := f_clone state in
              letb cast_vote_state_ret := Build_t_OvnContractState[cast_vote_state_ret] (f_g_pow_xi_yi_vis := update_at_usize (f_g_pow_xi_yi_vis cast_vote_state_ret) (cast_int (WS2 := U32) (f_cvp_i params)) g_pow_xi_yi_vi) in
              letb cast_vote_state_ret := Build_t_OvnContractState[cast_vote_state_ret] (f_zkp_vis := update_at_usize (f_zkp_vis cast_vote_state_ret) (cast_int (WS2 := U32) (f_cvp_i params)) (ret_both zkp_vi)) in
              Result_Ok (prod_b (f_accept,cast_vote_state_ret)) : both (t_Result (v_A × t_OvnContractState) t_ParseError)) in


          temp ← (cast_vote (ret_both ((i, xi, w, r, d, vi) : t_CastVoteParam)) state) ;;
          match temp : t_Result (v_A × t_OvnContractState) t_ParseError with
          | Result_Ok_case (_ , new_state) =>
              vote_i ← is_state (A := v_G) ((f_g_pow_xi_yi_vis (ret_both (new_state : t_OvnContractState))).a[ ret_both (i : int32) ]) ;;
              or_zkp_i ← is_state (A := t_OrZKPCommit) ((f_zkp_vis (ret_both (new_state : t_OvnContractState))).a[ ret_both (i : int32) ]) ;;
              ret (vote_i, or_zkp_i)
          | Result_Err_case _ => ret (chCanonical _, chCanonical _)
          end
        }
    ].
  Solve All Obligations with now intros ; destruct from_uint_size.
  Solve All Obligations with now intros ; simpl ; destruct (Z.to_nat _).
  Next Obligation.
    intros.
    ssprove_valid_package.
    destruct x as [xi [[w r] d]].
    ssprove_valid.
    1: apply valid_scheme ; rewrite <- fset0E ; apply (ChoiceEquality.is_valid_code (both_prog_valid _)).
    all: ssprove_valid'_2 ;  apply valid_scheme ; rewrite <- fset0E ; apply (ChoiceEquality.is_valid_code (both_prog_valid _)).
  Qed.
  Fail Next Obligation.

  Notation " 'chRound3shellInput' " :=
    ('unit)
    (in custom pack_type at level 2).

  Definition ROUND3_SHELL : nat := 100 + 2 * OVN_Param.N.
  
  Program Definition round3_shell (i : nat) (vi : bool) (state : both t_OvnContractState) :
    package fset0
      [interface #val #[ ROUND3 ] : chRound3input → chRound3output]
      [interface #val #[ ROUND3_SHELL ] : chRound3shellInput → chRound3output]
    :=
    [package
        #def #[ ROUND3_SHELL ] (_ : chRound3shellInput) : chRound3output
        {
          #import {sig #[ ROUND3 ] : chRound3input → chRound3output } as round3 ;;
          xi ← sample (uniform #|'Z_q|) ;; let xi := WitnessToField (otf xi) in
          w ← sample (uniform #|'Z_q|) ;; let w := WitnessToField (otf w) in
          r ← sample (uniform #|'Z_q|) ;; let r := WitnessToField (otf r) in
          d ← sample (uniform #|'Z_q|) ;; let d := WitnessToField (otf d) in
          round3 (xi, (w,r,d))
        }
    ].
  Solve All Obligations with now intros ; destruct from_uint_size.
  Fail Next Obligation.

  Notation " 'chProtocolOutput' " :=
    ((t_SchnorrZKPCommit × v_G) × f_Z × (v_G × t_OrZKPCommit))
    (in custom pack_type at level 2).

  Definition PROTOCOL : nat := 15 + 3 * OVN_Param.N.

  Program Definition protocol :
    package fset0
      [interface
         #val #[ ROUND1 ] : chRound1input → chRound1output ;
         #val #[ ROUND2 ] : chRound2input → chRound2output ;
         #val #[ ROUND3 ] : chRound3input → chRound3output
      ]
      [interface #val #[ PROTOCOL ] : 'unit → chProtocolOutput]
    :=
    [package
        #def #[ PROTOCOL ] (_ : 'unit) : chProtocolOutput
        {
          #import {sig #[ ROUND1 ] : chRound1input → chRound1output } as R1 ;;
          #import {sig #[ ROUND2 ] : chRound2input → chRound2output } as R2 ;;
          #import {sig #[ ROUND3 ] : chRound3input → chRound3output } as R3 ;;

          xi ← sample (uniform #|'Z_q|) ;; let xi := WitnessToField (otf xi) in
          round_1 ← R1 xi ;;
          (* TODO: allow modification of state *)

          round_2 ← R2 xi ;;
          (* TODO: allow modification of state *)

          w ← sample (uniform #|'Z_q|) ;;
          r ← sample (uniform #|'Z_q|) ;;
          d ← sample (uniform #|'Z_q|) ;;
          (* TODO: allow modification of state *)
          round_3 ← R3 (xi, (WitnessToField (otf w), WitnessToField (otf r), WitnessToField (otf d))) ;;
          (* TODO: allow modification of state *)

          ret ((round_1, round_2), round_3)
        }
    ].
  Solve All Obligations with now intros ; destruct from_uint_size.
  Fail Next Obligation.

  Program Definition real_protocol (i : nat) (vi : bool) (state : both t_OvnContractState) :
    package fset0
      [interface]
      [interface #val #[ PROTOCOL ] : 'unit → chProtocolOutput]
    :=
    [package
        #def #[ PROTOCOL ] (_ : 'unit) : chProtocolOutput
        {
          xi ← sample (uniform #|'Z_q|) ;; let xi := WitnessToField (otf xi) in
          ri ← sample (uniform #|'Z_q|) ;; let ri := WitnessToField (otf ri) in
          w ← sample (uniform #|'Z_q|) ;; let w := WitnessToField (otf w) in
          r ← sample (uniform #|'Z_q|) ;; let r := WitnessToField (otf r) in
          d ← sample (uniform #|'Z_q|) ;; let d := WitnessToField (otf d) in

          temp ← is_state (register_vote (ret_both ((i, xi, ri) : t_RegisterParam)) state) ;;
          round_1 ← match temp : t_Result (v_A × t_OvnContractState) t_ParseError with
          | Result_Ok_case (_ , new_state) =>
              zkp_i ← is_state (A := t_SchnorrZKPCommit) ((f_zkp_xis (ret_both (new_state : t_OvnContractState))).a[ ret_both (i : int32) ]) ;;
              g_pow_xi ← is_state ((f_g_pow_xis (ret_both (new_state : t_OvnContractState))).a[ ret_both (i : int32) ]) ;;
              ret (zkp_i , g_pow_xi)
          | Result_Err_case _ => ret (chCanonical t_SchnorrZKPCommit, chCanonical _)
          end ;;
          (* TODO: allow modification of state *)

          temp ← is_state (commit_to_vote (ret_both ((i, xi, is_pure f_field_zero, is_pure f_field_zero, is_pure f_field_zero, vi) : t_CastVoteParam)) state) ;;
          round_2 ← match temp : t_Result (v_A × t_OvnContractState) t_ParseError with
          | Result_Ok_case (_ , new_state) =>
              is_state (A := f_Z) ((f_commit_vis (ret_both (new_state : t_OvnContractState))).a[ ret_both (i : int32) ])
          | Result_Err_case _ => ret (chCanonical _)
            end ;;

          temp ← is_state (cast_vote (ret_both ((i, xi, w, r, d, vi) : t_CastVoteParam)) state) ;;
          round_3 ←
          match temp : t_Result (v_A × t_OvnContractState) t_ParseError with
          | Result_Ok_case (_ , new_state) =>
              vote_i ← is_state (A := v_G) ((f_g_pow_xi_yi_vis (ret_both (new_state : t_OvnContractState))).a[ ret_both (i : int32) ]) ;;
              or_zkp_i ← is_state (A := t_OrZKPCommit) ((f_zkp_vis (ret_both (new_state : t_OvnContractState))).a[ ret_both (i : int32) ]) ;;
              ret (vote_i, or_zkp_i)
          | Result_Err_case _ => ret (chCanonical _, chCanonical _)
          end ;;


          ret ((round_1, round_2), round_3)
        }
    ].
  Solve All Obligations with now intros ; destruct from_uint_size.
  Next Obligation.
    intros.
    ssprove_valid_package.
    ssprove_valid.
    1: apply valid_scheme ; rewrite <- fset0E ; apply (ChoiceEquality.is_valid_code (both_prog_valid _)).
    all: ssprove_valid'_2 ;  apply valid_scheme ; rewrite <- fset0E ; apply (ChoiceEquality.is_valid_code (both_prog_valid _)).
  Qed.
  Fail Next Obligation.

  Program Definition real_round1 (i : nat) (state : both t_OvnContractState) :
    package fset0
      [interface]
      [interface #val #[ ROUND1 ] : chRound1input → chRound1output]
    :=
    [package
        #def #[ ROUND1 ] (xi : chRound1input) : chRound1output
        {
          ri ← sample (uniform #|'Z_q|) ;; let ri := WitnessToField (otf ri) in
          temp ← is_state (register_vote (ret_both ((i, xi, ri) : t_RegisterParam)) state) ;;
          match temp : t_Result (v_A × t_OvnContractState) t_ParseError with
          | Result_Ok_case (_ , new_state) =>
              zkp_i ← is_state (A := t_SchnorrZKPCommit) ((f_zkp_xis (ret_both (new_state : t_OvnContractState))).a[ ret_both (i : int32) ]) ;;
              g_pow_xi ← is_state ((f_g_pow_xis (ret_both (new_state : t_OvnContractState))).a[ ret_both (i : int32) ]) ;;
              ret (zkp_i , g_pow_xi)
          | Result_Err_case _ => ret (chCanonical t_SchnorrZKPCommit, chCanonical _)
          end
          (* TODO: allow modification of state *)
        }
    ].
  Solve All Obligations with now intros ; destruct from_uint_size.
  Next Obligation.
    intros.
    ssprove_valid_package.
    ssprove_valid.
    1: apply valid_scheme ; rewrite <- fset0E ; apply (ChoiceEquality.is_valid_code (both_prog_valid _)).
    all: ssprove_valid'_2 ;  apply valid_scheme ; rewrite <- fset0E ; apply (ChoiceEquality.is_valid_code (both_prog_valid _)).
  Qed.
  Fail Next Obligation.

  Program Definition real_round2 (i : nat) (vi : bool) (state : both t_OvnContractState) :
    package fset0
      [interface]
      [interface #val #[ ROUND2 ] : chRound2input → chRound2output]
    :=
    [package
        #def #[ ROUND2 ] (xi : chRound2input) : chRound2output
        {
          temp ← is_state (commit_to_vote (ret_both ((i, xi, is_pure f_field_zero, is_pure f_field_zero, is_pure f_field_zero, vi) : t_CastVoteParam)) state) ;;
          match temp : t_Result (v_A × t_OvnContractState) t_ParseError with
          | Result_Ok_case (_ , new_state) =>
              is_state (A := f_Z) ((f_commit_vis (ret_both (new_state : t_OvnContractState))).a[ ret_both (i : int32) ])
          | Result_Err_case _ => ret (chCanonical _)
            end
          (* TODO: allow modification of state *)
        }
    ].
  Solve All Obligations with now intros ; destruct from_uint_size.
  Next Obligation.
    intros.
    ssprove_valid_package.
    (* ssprove_valid. *)
    (* destruct x as xi. *)
    ssprove_valid.
    1: apply valid_scheme ; rewrite <- fset0E ; apply (ChoiceEquality.is_valid_code (both_prog_valid _)).
    all: ssprove_valid'_2 ;  apply valid_scheme ; rewrite <- fset0E ; apply (ChoiceEquality.is_valid_code (both_prog_valid _)).
  Qed.
  Fail Next Obligation.

  Program Definition real_round3 (i : nat) (vi : bool) (state : both t_OvnContractState) :
    package fset0
      [interface]
      [interface #val #[ ROUND3 ] : chRound3input → chRound3output]
    :=
    [package
        #def #[ ROUND3 ] ('(xi, (w,r,d)) : chRound3input) : chRound3output
        {
          temp ← is_state (cast_vote (ret_both ((i, xi, w, r, d, vi) : t_CastVoteParam)) state) ;;
          match temp : t_Result (v_A × t_OvnContractState) t_ParseError with
          | Result_Ok_case (_ , new_state) =>
              vote_i ← is_state (A := v_G) ((f_g_pow_xi_yi_vis (ret_both (new_state : t_OvnContractState))).a[ ret_both (i : int32) ]) ;;
              or_zkp_i ← is_state (A := t_OrZKPCommit) ((f_zkp_vis (ret_both (new_state : t_OvnContractState))).a[ ret_both (i : int32) ]) ;;
              ret (vote_i, or_zkp_i)
          | Result_Err_case _ => ret (chCanonical _, chCanonical _)
          end
          (* TODO: allow modification of state *)
        }
    ].
  Solve All Obligations with now intros ; destruct from_uint_size.
  Next Obligation.
    intros.
    ssprove_valid_package.
    ssprove_valid.
    destruct x as [xi [[w r] d]].
    ssprove_valid.
    1: apply valid_scheme ; rewrite <- fset0E ; apply (ChoiceEquality.is_valid_code (both_prog_valid _)).
    all: ssprove_valid'_2 ;  apply valid_scheme ; rewrite <- fset0E ; apply (ChoiceEquality.is_valid_code (both_prog_valid _)).
  Qed.
  Fail Next Obligation.

  Program Definition real_protocol_insance (i : nat) (vi : bool) state :
    package fset0
      [interface]
      [interface #val #[ PROTOCOL ] : 'unit → chProtocolOutput]
    :=
    {package
       (protocol ∘ (par (real_round1 i state) (par (real_round2 i vi state) (real_round3 i vi state))))
    }.
  Next Obligation.
    intros.
    trimmed_package (real_round1 i state).
    trimmed_package (real_round2 i vi state).
    trimmed_package (real_round3 i vi state).

    solve_valid_package.
    Unshelve.
    all: revgoals.
    6: try (apply fsubsetxx || solve_in_fset) .
    all: try (apply fsubsetxx || solve_in_fset) .
  Qed.
  Fail Next Obligation.

  Lemma protocol_is_real_protocol :
    forall (i : nat) state,
    ∀ (LA : {fset Location}) (A : raw_package),
     ValidPackage LA [interface #val #[ PROTOCOL ] : 'unit → chProtocolOutput ] A_export A →
     fdisjoint LA OR_ZKP.proof_args.MyAlg.Sigma_locs →
     forall vi,
      AdvantageE
        (real_protocol_insance i vi state)
        (real_protocol i vi state)
        A = 0%R.
  Proof.
    intros.
    apply: eq_rel_perf_ind_ignore.
    1: apply fsubsetxx.
    2,3: apply fdisjoints0.

    Opaque cast_vote.

    unfold eq_up_to_inv.
    simplify_eq_rel inp_unit.

    choice_type_eqP_handle.
    choice_type_eqP_handle.
    simpl.
    choice_type_eqP_handle.
    choice_type_eqP_handle.
    erewrite !cast_fun_K.
    simpl.

    apply (r_uniform_bij) with (f := fun x => x) ; [ now apply inv_bij | intros xi ].
    apply (r_uniform_bij) with (f := fun x => x) ; [ now apply inv_bij | intros ri ].



    eapply r_transL.
    1:{
      apply r_nice_swap_rule ; [ easy | easy | ].
      apply r_bind_feq ; [ apply rreflexivity_rule | intros ].
      do 3 (eapply bobble_sampleC ; apply (r_uniform_bij) with (f := fun x => x) ; [ now apply inv_bij | intros ? ]).
      apply rreflexivity_rule.
    }
    hnf.

    eapply r_transL.
    1:{
      apply r_nice_swap_rule ; [ easy | easy | ].
      do 3 (eapply bobble_sampleC ; apply (r_uniform_bij) with (f := fun x => x) ; [ now apply inv_bij | intros ? ]).
      apply rreflexivity_rule.
    }
    hnf.

    apply (r_uniform_bij) with (f := fun x => x) ; [ now apply inv_bij | intros w ].
    apply (r_uniform_bij) with (f := fun x => x) ; [ now apply inv_bij | intros r ].
    apply (r_uniform_bij) with (f := fun x => x) ; [ now apply inv_bij | intros d ].
    repeat (rewrite !bind_assoc || ssprove_same_head_generic || rewrite !bind_rewrite).
    now apply r_ret.
  Admitted. (* Qed. *) (* Semi slow? 24.3 secs *)
  Fail Next Obligation.

  Notation " 'SHVZK_chRelation' " :=
    (chProd OR_ZKP.proof_args.MyAlg.choiceStatement OR_ZKP.proof_args.MyAlg.choiceWitness)
      (in custom pack_type at level 2).

  Notation " 'SHVZK_chTranscript' " :=
    (OR_ZKP.proof_args.MyAlg.choiceTranscript)
      (in custom pack_type at level 2).

  Program Definition protocol_mid i vi state :
    package OR_ZKP.proof_args.MyAlg.Sigma_locs
      [interface]
      [interface #val #[ PROTOCOL ] : 'unit → chProtocolOutput]
    :=
    {package (protocol ∘ (par
                            (round1 i state)
                            (par
                               (round2 i vi state)
                               (round3_shell i vi state ∘
                                  (round3 i vi state ∘
                                     (par
                                        (maximum_ballot_secrecy_assumption_pkg vi)
                                        OR_ZKP.hacspec_or_run))))))}.
  Next Obligation.
    intros.

    trimmed_package (round1 i state).
    trimmed_package (round2 i vi state).
    trimmed_package (round3 i vi state).
    trimmed_package (round3_shell i vi state).
    trimmed_package (maximum_ballot_secrecy_assumption_pkg vi).
    trimmed_package (OR_ZKP.hacspec_or_run).

    solve_valid_package.

    Unshelve.
    all: revgoals.
    all: try rewrite <- fset0E.
    all: try rewrite !fset0U.
    all: try rewrite !fsetU0.
    1,6,15,11,9,8,5: apply fsubsetxx || solve_in_fset.
    all: try apply fsubsetxx || solve_in_fset.
    rewrite <- !fset_cat.
    simpl.
    apply fsubsetxx.
    solve_in_fset.
  Qed.

  Definition r_bind_feq_alt :
    forall {A B} (a b : raw_code A) (f g : A -> raw_code B) pre post,
      ⊢ ⦃ pre ⦄ a ≈ b ⦃ pre_to_post pre ⦄
      → (∀ (a₀ : A), ⊢ ⦃ pre ⦄ f a₀ ≈ g a₀ ⦃ post ⦄) →
      ⊢ ⦃ pre ⦄ x ← a ;; f x ≈ x ← b ;; g x ⦃ post ⦄.
  Proof.
    intros.
    eapply r_bind with (mid := pre_to_post pre)
    ; [eapply rpost_weaken_rule ; [ apply H | now intros [] [] ? ]
      | intros ].
    apply rpre_hypothesis_rule ; intros ? ? [] ; eapply rpre_weaken_rule with (pre := pre)
    ; [ subst ; apply H0 | now simpl ; intros ? ? [] ].
  Qed.

  Lemma round1_adv :
    forall (i : nat) state,
    ∀ (LA : {fset Location}) (A : raw_package),
      ValidPackage LA [interface #val #[ROUND1] : chRound1input → chRound1output ] A_export A →
      fdisjoint LA fset0 →
      AdvantageE (pack (round1 i state)) (pack (real_round1 i state)) A = 0%R.
  Proof.
    intros.
    {
      apply: eq_rel_perf_ind_eq.
      2,3: apply fdisjoints0.

      unfold eq_up_to_inv.
      simplify_eq_rel inp_unit.
      fold chElement.

      apply (r_uniform_bij) with (f := fun x => x) ; [ now apply inv_bij | intros ri ].
      eapply r_bind_feq ; [ apply rreflexivity_rule | intros ].
      destruct a₀.
      2: now simpl ; apply r_ret.
      destruct s.
      repeat (apply r_bind_feq ; [ apply rreflexivity_rule | intros ]).
      now apply r_ret.
    }
  Qed.

  Lemma round2_adv :
    forall (i : nat) vi state,
    ∀ (LA : {fset Location}) (A : raw_package),
      ValidPackage LA [interface #val #[ROUND2] : chRound2input → chRound2output ] A_export A →
      fdisjoint LA fset0 →
      AdvantageE (pack (round2 i vi state)) (pack (real_round2 i vi state)) A = 0%R.
  Proof.
    intros.
    {
      apply: eq_rel_perf_ind_eq.
      2,3: apply fdisjoints0.

      unfold eq_up_to_inv.
      simplify_eq_rel inp. fold chElement.
      (* destruct inp as xi. *)
      repeat (apply r_bind_feq ; [ apply rreflexivity_rule | intros ]).
      destruct a₀.
      2: now apply r_ret.
      destruct s.
      repeat (apply r_bind_feq ; [ apply rreflexivity_rule | intros ]).
      now apply r_ret.
    }
  Qed.

  Lemma inj_mulg : forall (x : gT), injective (mulg x).
  Proof.
    unfold injective.
    intros.
    assert (is_true (1 < (Zp_trunc q).+2)%N) by easy.
    apply (prod_swap_iff (x * x1) (x2) x (Ordinal (m := 1) H0 : 'Z_q)) in H.
    rewrite <- H.
    simpl.
    rewrite mulgA.
    rewrite mulVg.
    rewrite mul1g.
    reflexivity.
  Qed.

  Corollary inj_mulg_g : injective (mulg g).
  Proof. apply inj_mulg. Qed.

  Lemma div_not_one_if_diff : forall (a b : both v_G), (is_pure a : gT) <> is_pure b -> (is_pure (div a b) <> g ^+ 0)%g.
  Proof.
    clear ; intros.
    unfold div at 1.
    simpl.
    red ; intros ; apply H ; clear H.
    rewrite hacspec_function_guarantees2 in H0.
    apply /eqP.
    rewrite eq_mulgV1.
    apply /eqP.
    rewrite <- (expg0 g).
    rewrite <- H0.
    Misc.push_down_sides.
    reflexivity.
  Qed.
  
  Lemma round3_adv :
    forall (i : nat) vi state,
    ∀ (LA : {fset Location}) (A : raw_package),
      ValidPackage LA [interface #val #[ROUND3] : chRound3shellInput → chRound3output ] A_export A →
      fdisjoint LA OR_ZKP.proof_args.MyAlg.Sigma_locs →
      AdvantageE ((round3_shell i vi state) ∘ (round3 i vi state ∘ (par (real_assumption_pkg vi) OR_ZKP.hacspec_or_run))) ((round3_shell i vi state) ∘ (real_round3 i vi state)) A = 0%R.
  Proof.
    intros.
    {
      trimmed_package (real_assumption_pkg vi).
      trimmed_package (OR_ZKP.hacspec_or_run).
      trimmed_package (round3 i vi state).
      trimmed_package (real_round3 i vi state).
      trimmed_package (round3_shell i vi state).

      apply: eq_rel_perf_ind_eq.
      1:{ solve_valid_package.
          Unshelve.
          all: revgoals.
          all: try rewrite <- fset0E.
          all: try rewrite !fset0U.
          all: try rewrite !fsetU0.
          7, 3, 1: try apply fsubsetxx || solve_in_fset.
          all: try apply fsubsetxx || solve_in_fset.
          all: shelve.
      }
      1:{
        solve_valid_package.
        Unshelve.
        all: try apply fsubsetxx || solve_in_fset.
        all: shelve.
      }

      2: apply H.
      2: apply H0.
      2: apply fdisjoints0.

      unfold eq_up_to_inv.
      simplify_eq_rel inp_unit. (* xi. *)

      fold chElement.

      choice_type_eqP_handle.
      choice_type_eqP_handle.
      erewrite !cast_fun_K.

      (* unlink all code *)
      eapply r_transL.
      1:{
        apply (r_uniform_bij) with (f := fun x => x) ; [ now apply inv_bij | intros ? ].
        apply (r_uniform_bij) with (f := fun x => x) ; [ now apply inv_bij | intros ? ].
        apply (r_uniform_bij) with (f := fun x => x) ; [ now apply inv_bij | intros ? ].
        apply (r_uniform_bij) with (f := fun x => x) ; [ now apply inv_bij | intros ? ].

        rewrite code_link_bind.
        rewrite bind_assoc.
        rewrite code_link_bind.
        rewrite bind_assoc.

        apply r_bind_feq.
        {
          erewrite !(code_link_scheme _ _ (is_state _)).
          2: ssprove_valid_code.
          apply rreflexivity_rule.
        }
        intros.

        simpl.
        choice_type_eqP_handle.
        choice_type_eqP_handle.
        choice_type_eqP_handle.
        erewrite !cast_fun_K.
        rewrite bind_assoc.
        replace (OR_ZKP.proof_args.MyParam.R _ _) with true
          by now rewrite !otf_fto ; unfold OR_ZKP.proof_args.MyParam.R ; rewrite !eqxx.
        simpl.
        apply (r_uniform_bij) with (f := fun x => x) ; [ now apply inv_bij | intros ? ].
        apply (r_uniform_bij) with (f := fun x => x) ; [ now apply inv_bij | intros ? ].
        apply (r_uniform_bij) with (f := fun x => x) ; [ now apply inv_bij | intros ? ].
        apply r_bind_feq ; [ apply rreflexivity_rule | intros ].
        choice_type_eqP_handle.
        erewrite !cast_fun_K.
        apply r_bind_feq ; [ apply rreflexivity_rule | intros ].
        instantiate (1 := (fun v => match v with inl (_ , x) => vote_i ← _ ;; or_zkp_i ← _ ;; ret _ | inr x => _ end)).
        hnf.
        destruct a₀1.
        2: now apply r_ret ; intros ; subst.
        destruct s.
        erewrite !(code_link_scheme).
        2: ssprove_valid_code.
        rewrite bind_ret.
        apply r_bind_feq ; [ apply rreflexivity_rule | intros ].
        apply r_bind_feq ; [ apply rreflexivity_rule | intros ].
        now apply r_ret ; intros ; subst.
      }
      hnf.

      (* Bobble all randomness to the top *)
      eapply r_transL.
      1:{
        apply (r_uniform_bij) with (f := fun x => x) ; [ now apply inv_bij | intros ? ].
        apply (r_uniform_bij) with (f := fun x => x) ; [ now apply inv_bij | intros ? ].
        apply (r_uniform_bij) with (f := fun x => x) ; [ now apply inv_bij | intros ? ].
        apply (r_uniform_bij) with (f := fun x => x) ; [ now apply inv_bij | intros ? ].

        apply r_nice_swap_rule ; [ easy | easy | ].
        do 3 (eapply bobble_sampleC ; apply (r_uniform_bij) with (f := fun x => x) ; [ now apply inv_bij | intros ? ]).

        apply rreflexivity_rule.
      }
      hnf.

      apply (r_uniform_bij) with (f := fun x => x) ; [ now apply inv_bij | intros xi ].

      apply r_const_sample_L ; [ apply LosslessOp_uniform | intros w' ].
      apply r_const_sample_L ; [ apply LosslessOp_uniform | intros r' ].
      apply r_const_sample_L ; [ apply LosslessOp_uniform | intros d' ].

      apply (r_uniform_bij) with (f := fun x => x) ; [ now apply inv_bij | intros w ].
      apply (r_uniform_bij) with (f := fun x => x) ; [ now apply inv_bij | intros r ].
      apply (r_uniform_bij) with (f := fun x => x) ; [ now apply inv_bij | intros d ].

      unfold cast_vote at 1.

      rewrite !bind_assoc.
      rewrite bind_rewrite.
      rewrite !bind_assoc.
      rewrite !bind_rewrite.
      rewrite bind_assoc.
      apply somewhat_let_substitutionR.

      do 2 replace (f_cvp_i _) with (ret_both (i : int32)) by now apply both_eq.

      set (pre := fun _ => _).
      apply better_r.
      apply somewhat_substitution.
      apply somewhat_substitutionR.
      rewrite !bind_rewrite.
      (* ssprove_same_head_generic. *)
      subst pre.
      hnf.
      set (a := compute_g_pow_yi _ _).

      apply somewhat_let_substitutionR.
      rewrite bind_assoc.

      rewrite !otf_fto.
      rewrite !WitnessToFieldCancel.
      rewrite !FieldToWitnessCancel.

      replace (f_cvp_xi _) with (ret_both (WitnessToField (otf xi))) by now apply both_eq.

      replace (f_cvp_zkp_random_w _) with (ret_both (WitnessToField (otf w))) by now apply both_eq.
      replace (f_cvp_zkp_random_r _) with (ret_both (WitnessToField (otf r))) by now apply both_eq.
      replace (f_cvp_zkp_random_d _) with (ret_both (WitnessToField (otf d))) by now apply both_eq.
      replace (f_cvp_vote _) with (ret_both (vi : 'bool)) by now apply both_eq.

      replace (_ == _) with (vi : 'bool).
      2:{
        symmetry.
        destruct vi.
        1:{
          simpl.
          rewrite expg1.
          rewrite eqxx.
          reflexivity.
        }
        {
          rewrite expg0.
          apply (ssrbool.introF eqP).
          red ; intros.
          apply generator_is_not_one.
          apply both_equivalence_is_pure_eq.
          eapply inj_mulg.
          apply H6.
        }
      }

      set (pre := fun _ => _).
      apply better_r.
      apply somewhat_substitutionR.
      apply (somewhat_substitution (zkp_one_out_of_two  _ _ _ _ _ _) _ _ pre).
      rewrite !bind_rewrite.
      (* ssprove_same_head_generic. *)
      subst pre.
      hnf.
      set (a0 := (zkp_one_out_of_two  _ _ _ _ _ _)).

      (* rewrite bind_rewrite. *)

      apply somewhat_let_substitutionR.

      rewrite !bind_assoc.

      ssprove_same_head_generic.

      erewrite !(code_link_scheme).
      2: ssprove_valid_code.

      unfold f_branch.

      rewrite OR_ZKP.ret_cancel.
      1:{
        apply r_bind_feq ; [ apply rreflexivity_rule | intros ].
        destruct a₀.
        2: now apply r_ret.
        simpl.
        destruct s.
        rewrite bind_ret.
        destruct s0.
        apply r_bind_feq ; [ apply rreflexivity_rule | intros ].
        apply r_bind_feq ; [ apply rreflexivity_rule | intros ].
        apply r_ret.
        easy.
      }
      1:{
        simpl.
        subst a0.
        destruct vi.
        {
          simpl.
          unfold zkp_one_out_of_two at 1, Build_t_OrZKPCommit at 1 2 ;
            repeat unfold let_both at 1 ;
            simpl.
          rewrite <- conversion_is_true.
          rewrite FieldToWitnessCancel.
          reflexivity.
        }
        {
          simpl.
          unfold zkp_one_out_of_two at 1, Build_t_OrZKPCommit at 1 2 ;
            repeat unfold let_both at 1 ;
            simpl.
          rewrite <- conversion_is_true.
          rewrite FieldToWitnessCancel.
          reflexivity.
        }
      }
      1:{
        simpl.
        subst a0.
        destruct vi.
        {
          simpl.
          unfold zkp_one_out_of_two at 1, Build_t_OrZKPCommit at 1 2 ;
            repeat unfold let_both at 1 ;
            simpl.
          rewrite pow_witness_to_field.
          rewrite expg1.
          Misc.push_down_sides.
          reflexivity.
        }
        {
          simpl.
          unfold zkp_one_out_of_two at 1, Build_t_OrZKPCommit at 1 2 ;
            repeat unfold let_both at 1 ;
            simpl.
          rewrite pow_witness_to_field.
          rewrite expg0.
          rewrite mulg1.
          Misc.push_down_sides.
          reflexivity.
        }
      }
    }
  Admitted. (* Qed. *) (* Slow *)

  Lemma protocol_ass_adv :
    forall (i : nat) state,
    ∀ (LA : {fset Location}) (A : raw_package),
     ValidPackage LA [interface #val #[ PROTOCOL ] : 'unit → chProtocolOutput ] A_export A →
     fdisjoint LA OR_ZKP.proof_args.MyAlg.Sigma_locs →
     forall vi,
      AdvantageE
        (protocol ∘ (par
                       (round1 i state)
                       (par
                          (round2 i vi state)
                          ((round3_shell i vi state) ∘
                             (round3 i vi state ∘
                                (par
                                   (real_assumption_pkg vi)
                                   OR_ZKP.hacspec_or_run))))))
        (protocol_mid i vi state)
        A = 0%R.

  Lemma protocol_rounds_adv :
    forall (i : nat) state,
    ∀ (LA : {fset Location}) (A : raw_package),
     ValidPackage LA [interface #val #[ PROTOCOL ] : 'unit → chProtocolOutput ] A_export A →
     fdisjoint LA OR_ZKP.proof_args.MyAlg.Sigma_locs →
     forall vi,
      AdvantageE
        (protocol_mid i vi state)
        (real_protocol_insance i vi state)
        A = 0%R.
  Proof.
    intros.

    trimmed_package (round1 i state).
    trimmed_package (real_round1 i state).
    trimmed_package (round2 i vi state).
    trimmed_package (real_round2 i vi state).
    trimmed_package (round3 i vi state).
    trimmed_package (real_round3 i vi state).
    trimmed_package (maximum_ballot_secrecy_assumption_pkg vi).
    trimmed_package (OR_ZKP.hacspec_or_run).

    unfold protocol_mid.
    unfold real_protocol_insance.
    unfold pack.

    unfold_advantageE.

    epose ({package par (pack (real_round2 i vi state)) (pack (real_round3 i vi state)) #with _} : package _ _ _).

    apply (AdvantageE_le_0 _ _ _ ).
    eapply Order.le_trans ; [ apply Advantage_triangle with
        (R :=
           (par (pack (round1 i state))
              (par (pack (real_round2 i vi state))
                 (pack (real_round3 i vi state))))) | ].

    replace (AdvantageE _ _ _) with (@GRing.zero R) ; [
        replace (AdvantageE _ _ _) with (@GRing.zero R) ; [ rewrite add0r ; easy | symmetry ] |
        symmetry ].
    1:{
      rewrite <- !(par_commut (par (real_round2 i vi state) _)).
      2,3: solve_Parable.

      erewrite (Advantage_par).
      2: rewrite <- fsetUid ; apply p.
      2,3,4: solve_valid_package.
      3,4,5: solve_trimmed.
      2:{
        clear.
        unfold flat.

        intros n u1 u2.
        now do 2 (let H := fresh in
                  intros H
                  ; rewrite <- fset1E in H
                  ; rewrite in_fset1 in H
                  ; apply (ssrbool.elimT eqP) in H
                  ; inversion H ; subst).
      }
      {
        apply: eq_rel_perf_ind_ignore.

        1: apply round1.
        1: apply real_round1.
        1: apply fsubsetxx.
        2:{
          solve_valid_package.
          1: apply H.
          epose (trimmed_ID [interface #val #[ROUND1] : chRound2output → chRound1output ]).
          solve_valid_package.
          Unshelve.
          all: revgoals.
          all: try rewrite <- fset0E.
          all: try rewrite !fset0U.
          all: try rewrite !fsetU0.
          4: apply fsubsetxx || solve_in_fset.
          18:{
            apply valid_ID.
            {
              clear.
              unfold flat.

              intros n u1 u2.
              now do 2 (let H := fresh in
                        intros H
                        ; rewrite <- fset1E in H
                        ; rewrite in_fset1 in H
                        ; apply (ssrbool.elimT eqP) in H
                        ; inversion H ; subst).
            }
          }
          12, 10, 9: apply fsubsetxx || solve_in_fset.
          all: try (apply fsubsetxx || solve_in_fset).
          1: rewrite !fset0U ; (apply fsubsetxx || solve_in_fset).
        }
        2,3: apply fdisjoints0.

        unfold eq_up_to_inv.
        simplify_eq_rel inp_unit.

        apply (r_uniform_bij) with (f := fun x => x) ; [ now apply inv_bij | intros ri ].
        fold chElement.
        eapply r_bind_feq_alt.
        1:{
          eapply r_reflexivity_alt ; [ ssprove_valid_code | easy | easy ].
        }
        intros.
        destruct a₀.
        2: now simpl ; apply r_ret.
        destruct s.
        rewrite bind_assoc.
        apply r_bind_feq_alt.
        rewrite bind_assoc.
        apply r_bind_feq_alt.



        eapply (proj1 (bobble_sampleC _ _ _ _)).
        apply (r_uniform_bij) with (f := fun x => x) ; [ now apply inv_bij | intros r ].
        eapply (proj1 (bobble_sampleC _ _ _ _)).
        apply (r_uniform_bij) with (f := fun x => x) ; [ now apply inv_bij | intros d ].
        apply rreflexivity_rule.
      }
      hnf.



      }
    }
    {
      unfold_advantageE.
      erewrite (Advantage_par).
      6, 7, 8: solve_trimmed.
      2: solve_valid_package.
      2, 3: eapply valid_par_upto ; [
          solve_Parable
        | solve_valid_package | solve_valid_package | shelve.. ].
      2: eapply valid_par_upto ; [
          solve_Parable
        | solve_valid_package | solve_valid_package | shelve.. ].
      2:{
        clear.
        unfold flat.

        intros n u1 u2.
        rewrite !in_fsetU.
        now do 2 (let H := fresh in
                  intros H
                  ; apply (ssrbool.elimT ssrbool.orP) in H
                  ; destruct H
                  ; rewrite <- fset1E in H
                  ; rewrite in_fset1 in H
                  ; apply (ssrbool.elimT eqP) in H
                  ; inversion H ; subst).
      }

      apply (AdvantageE_le_0 _ _ _ ).
      eapply Order.le_trans ; [ apply Advantage_triangle with
          (R := (par (pack (round2 i vi state))
                   (pack (real_round3 i vi state)))) | ].

      replace (AdvantageE _ _ _) with (@GRing.zero R) ; [
          replace (AdvantageE _ _ _) with (@GRing.zero R) ; [ rewrite add0r ; easy | symmetry ] |
          symmetry ].
      1:{
        rewrite <- !(par_commut (real_round3 i vi state)).
        2,3: solve_Parable.

        erewrite (Advantage_par).
        2,3,4: solve_valid_package.
        3,4,5: assumption.
        2:{
          clear.
          unfold flat.

          intros n u1 u2.
          now do 2 (let H := fresh in
                    intros H
                    ; rewrite <- fset1E in H
                    ; rewrite in_fset1 in H
                    ; apply (ssrbool.elimT eqP) in H
                    ; inversion H ; subst).
        }

        admit.
      }

      unfold_advantageE.
      erewrite (Advantage_par).
      6, 7, 8: solve_trimmed.
      2, 3, 4: solve_valid_package.
      2: eapply valid_par_upto ; [
          solve_Parable
        | solve_valid_package | solve_valid_package | shelve.. ].
      2:{
        clear.
        unfold flat.

        intros n u1 u2.
        now do 2 (let H := fresh in
                  intros H
                  ; rewrite <- fset1E in H
                  ; rewrite in_fset1 in H
                  ; apply (ssrbool.elimT eqP) in H
                  ; inversion H ; subst).
      }

      admit.
    }

    apply: eq_rel_perf_ind_ignore.
    1: apply fsubsetxx || solve_in_fset.
    3: apply fdisjoints0.
    2: apply H0.

    unfold eq_up_to_inv.
    simplify_eq_rel inp_unit.

    choice_type_eqP_handle.
    choice_type_eqP_handle.
    simpl.
    choice_type_eqP_handle.
    choice_type_eqP_handle.
    erewrite !cast_fun_K.
    simpl.

    apply (r_uniform_bij) with (f := fun x => x) ; [ now apply inv_bij | intros xi ].
    apply (r_uniform_bij) with (f := fun x => x) ; [ now apply inv_bij | intros ri ].

    fold chElement.

    rewrite bind_assoc.

    rewrite <- bind_assoc.
    eapply r_transR.
    1:{
      eapply (proj1 (bobble_sampleC _ _ _ _)).
      apply (r_uniform_bij) with (f := fun x => x) ; [ now apply inv_bij | intros w ].
      eapply (proj1 (bobble_sampleC _ _ _ _)).
      apply (r_uniform_bij) with (f := fun x => x) ; [ now apply inv_bij | intros r ].
      eapply (proj1 (bobble_sampleC _ _ _ _)).
      apply (r_uniform_bij) with (f := fun x => x) ; [ now apply inv_bij | intros d ].
      apply rreflexivity_rule.
    }
    hnf.

    rewrite bind_assoc.
    progress repeat ssprove_same_head_generic.


    eapply r_transR.
    1:{
      eapply (proj1 (bobble_sampleC _ _ _ _)).
      apply (r_uniform_bij) with (f := fun x => x) ; [ now apply inv_bij | intros w ].
      eapply (proj1 (bobble_sampleC _ _ _ _)).
      apply (r_uniform_bij) with (f := fun x => x) ; [ now apply inv_bij | intros r ].
      eapply (proj1 (bobble_sampleC _ _ _ _)).
      apply (r_uniform_bij) with (f := fun x => x) ; [ now apply inv_bij | intros d ].
      apply rreflexivity_rule.
    }
    hnf.

    progress repeat ssprove_same_head_generic.

    eapply r_transL.
    1:{
      Unshelve.
      2:{
        eapply (
            x ← sample uniform #|pred_of_simpl (pred_of_argType 'Z_q)| ;;
            x0 ← sample uniform #|pred_of_simpl (pred_of_argType 'Z_q)| ;;
            x1 ← sample uniform #|pred_of_simpl (pred_of_argType 'Z_q)| ;;
            x ← sample uniform #|pred_of_simpl (pred_of_argType 'Z_q)| ;;
            x0 ← sample uniform #|pred_of_simpl (pred_of_argType 'Z_q)| ;;
            x1 ← sample uniform #|pred_of_simpl (pred_of_argType 'Z_q)| ;;
            _).
      }

      apply r_nice_swap_rule ; [ easy | easy | ].
      apply (r_uniform_bij) with (f := fun x => x) ; [ now apply inv_bij | intros w ].
      apply (r_uniform_bij) with (f := fun x => x) ; [ now apply inv_bij | intros r ].
      apply (r_uniform_bij) with (f := fun x => x) ; [ now apply inv_bij | intros d ].

      eapply r_transL.
      1:{
        apply r_nice_swap_rule ; [ easy | easy | ].

        apply r_bind_feq ; [ apply rreflexivity_rule | intros ? ].


        rewrite code_link_bind.
        rewrite bind_assoc.
        rewrite code_link_bind.
        rewrite bind_assoc.

        simpl.

        choice_type_eqP_handle.
        choice_type_eqP_handle.
        erewrite !cast_fun_K.
        unfold assertD.
        simpl.
        choice_type_eqP_handle.
        erewrite !cast_fun_K.

        apply r_bind_feq ; [ apply rreflexivity_rule | intros ? ].

        rewrite !otf_fto.
        replace (OR_ZKP.proof_args.MyParam.R _ _) with true by now unfold OR_ZKP.proof_args.MyParam.R ; rewrite !eqxx.

        apply (r_uniform_bij) with (f := fun x => x) ; [ now apply inv_bij | intros w_ ].
        apply (r_uniform_bij) with (f := fun x => x) ; [ now apply inv_bij | intros r_ ].
        apply (r_uniform_bij) with (f := fun x => x) ; [ now apply inv_bij | intros d_ ].
        fold @bind.

        rewrite !bind_assoc.
        rewrite !FieldToWitnessCancel.
        simpl.

        apply bobble_sampleC.

        apply (r_uniform_bij) with (f := fun x => x) ; [ now apply inv_bij | intros ? ].
        apply r_bind_feq ; [ apply rreflexivity_rule | intros ? ].

        eapply r_bind_feq.
        {
          apply r_bind_feq ; [ apply rreflexivity_rule | intros ? ].
          rewrite code_link_bind.
          erewrite !(code_link_scheme _ _ (is_state _)).
          1:{
            apply r_bind_feq ; [ apply rreflexivity_rule | intros ? ].
            simpl.
            apply rreflexivity_rule.
          }
          ssprove_valid_code.
        }
        intros ?.

        instantiate (1 := (fun v => match v with inl (_ , x) => vote_i ← _ ;; or_zkp_i ← _ ;; ret _ | inr x => _ end)).
        hnf.

        destruct a₀2 as [[] | ] ; [ | apply rreflexivity_rule].
        rewrite code_link_bind.
        rewrite code_link_bind.
        rewrite bind_assoc.
        rewrite bind_assoc.
        erewrite !(code_link_scheme _ _ (is_state _)).
        2: ssprove_valid_code.

        apply r_bind_feq ; [ apply rreflexivity_rule | intros ? ].
        rewrite bind_assoc.
        rewrite code_link_bind.
        rewrite bind_assoc.
        erewrite !(code_link_scheme _ _ (is_state _)).
        2: ssprove_valid_code.

        rewrite bind_rewrite.
        erewrite !(code_link_scheme _ _ (is_state _)).
        2: ssprove_valid_code.
        rewrite bind_rewrite.

        rewrite code_link_bind.
        rewrite bind_assoc.

        set (par _ _).
        erewrite (code_link_scheme _ _ (is_state (array_index (as_nseq (n_seq_array_or_seq (f_zkp_vis (ret_both _)) round3_obligation_2)) (ret_both (Z_to_int (Z.of_N (N.of_nat i)))))) f).
        2: ssprove_valid_code.
        apply r_bind_feq ; [ apply rreflexivity_rule | intros ? ].
        rewrite bind_rewrite.
        apply rreflexivity_rule.
      }
      hnf.

      eapply r_transL.
      1:{
        apply r_bind_feq ; [ apply rreflexivity_rule | intros ? ].
        apply r_nice_swap_rule ; [ easy | easy | ].
        apply bobble_sampleC.
        apply (r_uniform_bij) with (f := fun x => x) ; [ now apply inv_bij | intros w_ ].
        apply bobble_sampleC.
        apply (r_uniform_bij) with (f := fun x => x) ; [ now apply inv_bij | intros r_ ].
        apply bobble_sampleC.
        apply (r_uniform_bij) with (f := fun x => x) ; [ now apply inv_bij | intros d_ ].
        apply bobble_sampleC.
        apply (r_uniform_bij) with (f := fun x => x) ; [ now apply inv_bij | intros a_ ].
        apply rreflexivity_rule.
      }
      hnf.

      apply bobble_sampleC.
      apply (r_uniform_bij) with (f := fun x => x) ; [ now apply inv_bij | intros w_ ].
      apply bobble_sampleC.
      apply (r_uniform_bij) with (f := fun x => x) ; [ now apply inv_bij | intros r_ ].
      apply bobble_sampleC.
      apply (r_uniform_bij) with (f := fun x => x) ; [ now apply inv_bij | intros d_ ].
      apply bobble_sampleC.
      apply (r_uniform_bij) with (f := fun x => x) ; [ now apply inv_bij | intros a_ ].
      apply rreflexivity_rule.
    }
    hnf.

    eapply r_transL.
    1:{


    erewrite !(code_link_scheme _ _ (is_state _)).
    2: ssprove_valid_code.
    rewrite !bind_assoc.


    apply (r_uniform_bij) with (f := fun x => x) ; [ now apply inv_bij | intros w ].
    apply (r_uniform_bij) with (f := fun x => x) ; [ now apply inv_bij | intros r ].
    apply (r_uniform_bij) with (f := fun x => x) ; [ now apply inv_bij | intros d ].

    rewrite bind_assoc.
    rewrite bind_assoc.
    progress repeat ssprove_same_head_generic.

    rewrite code_link_bind.
    rewrite bind_assoc.

    erewrite !(code_link_scheme _ _ (is_state _)).
    2: ssprove_valid_code.
    rewrite !bind_assoc.
    simpl.
    rewrite !bind_assoc.

    unfold prod_to_prod at 1.
    simpl.

    setoid_rewrite bind_assoc.

    apply somewhat_let_substitutionR.

    progress repeat ssprove_same_head_generic.

    repeat ssprove_same_head_generic.
    simpl.
    erewrite !bind_assoc.

    choice_type_eqP_handle.
    choice_type_eqP_handle.
    erewrite !cast_fun_K.

    unfold prod_to_prod at 1.
    simpl.

    (* unfold ControlFlow_Continue. *)
    (* repeat unfold lift1_both at 1. *)

    setoid_rewrite bind_assoc.

    apply somewhat_let_substitutionR.

    do 2 replace (f_cvp_i _) with (ret_both (i : int32)) by now apply both_eq.

    ssprove_same_head g_pow_yi.

    apply (r_uniform_bij) with (f := fun x => x) ; [ now apply inv_bij | intros w ].
    apply (r_uniform_bij) with (f := fun x => x) ; [ now apply inv_bij | intros r ].
    apply (r_uniform_bij) with (f := fun x => x) ; [ now apply inv_bij | intros d ].

    rewrite !bind_assoc.

    apply somewhat_let_substitutionR.

    destruct x.

    erewrite bind_assoc.


    ≈

    eapply r_transL.
    1:{
      apply r_nice_swap_rule ; [ easy | easy | ].
      eapply bobble_sampleC.
      apply rreflexivity_rule.
    }

    (* eapply r_transL. *)
    (* 1:{ *)
    (*   apply r_uniform_triple. *)
    (*   intros. *)
    (*   apply rreflexivity_rule. *)
    (* } *)


    epose bobble_sampleC.




  Qed.


  Import OR_ZKP.proof_args.MyAlg.
  (* Import OR_ZKP.proof_args.MyParam. *)
  Import OR_ZKP.proof_args.Sigma.

  Notation " 'SHVZK_chInput' " :=
    (chProd (chProd OR_ZKP.proof_args.MyAlg.choiceStatement OR_ZKP.proof_args.MyAlg.choiceWitness) OR_ZKP.proof_args.MyAlg.choiceChallenge)
      (in custom pack_type at level 2).

  Definition SHVZK_ideal_aux : package (fset [::]) [interface #val #[ OR_ZKP.proof_args.Sigma.TRANSCRIPT ] : SHVZK_chInput → SHVZK_chTranscript ] [interface #val #[OR_ZKP.proof_args.Sigma.RUN] : SHVZK_chRelation → SHVZK_chTranscript ]
    :=
    [package
        #def #[ OR_ZKP.proof_args.Sigma.RUN ] (hw : SHVZK_chRelation) : SHVZK_chTranscript
        {
          #import {sig #[ OR_ZKP.proof_args.Sigma.TRANSCRIPT ] : SHVZK_chInput → SHVZK_chTranscript } as SHVZK ;;
          e ← sample uniform #|OR_ZKP.proof_args.MyParam.Challenge| ;;
          t ← SHVZK (hw, e) ;;
          ret t
        }
    ].

  Lemma maximum_ballot_secrecy_helper :
    forall (i : nat) state,
    ∀ (LA : {fset Location}) (A : raw_package),
     ValidPackage LA [interface #val #[ PROTOCOL ] : 'unit → chProtocolOutput ] A_export A →
     fdisjoint LA OR_ZKP.proof_args.MyAlg.Sigma_locs →
     forall vi,
      AdvantageE
        (protocol ∘ (par (round1 i state) (par (round2 i vi state) (round3 i vi state ∘ (par (maximum_ballot_secrecy_assumption_pkg vi) OR_ZKP.hacspec_or_run)))))
        (protocol ∘ (par (round1 i state) (par (round2 i vi state) (round3 i vi state ∘ (par (maximum_ballot_secrecy_assumption_pkg vi) (SHVZK_ideal_aux ∘ SHVZK_ideal))))))
      A = 0%R.
  Proof.
    intros.

    trimmed_package (round1 i state).
    trimmed_package (round2 i vi state).
    trimmed_package (round3 i vi state).

    rewrite <- H1.
    rewrite <- H2.
    rewrite <- H3.
    (* rewrite !link_trim_commut. *)

    unfold_advantageE.
    unfold_advantageE.
    2,3: ssprove_valid ; try (apply fsubsetxx || solve_in_fset).
    Unshelve.
    all: revgoals.
    all: try (apply fsubsetxx || solve_in_fset) .
    all: revgoals.

    2:{
      clear.
      unfold flat.

      intros n u1 u2.
      rewrite !in_fsetU.
      now do 2 (let H := fresh in
                intros H
                ; apply (ssrbool.elimT ssrbool.orP) in H
                ; destruct H
                ; rewrite <- fset1E in H
                ; rewrite in_fset1 in H
                ; apply (ssrbool.elimT eqP) in H
                ; inversion H ; subst).
    }

    unfold_advantageE.
    2,3: ssprove_valid ; try (apply fsubsetxx || solve_in_fset).
    Unshelve.
    all: revgoals.
    all: try (apply fsubsetxx || solve_in_fset) .
    all: revgoals.

    2:{
      clear.
      unfold flat.

      intros n u1 u2.
      now do 2 (let H := fresh in
                intros H
                ; rewrite <- fset1E in H
                ; rewrite in_fset1 in H
                ; apply (ssrbool.elimT eqP) in H
                ; inversion H ; subst).
    }

    unfold_advantageE.

    trimmed_package (maximum_ballot_secrecy_assumption_pkg vi).
    trimmed_package (OR_ZKP.hacspec_or_run).
    trimmed_package (SHVZK_ideal_aux).

    rewrite <- H4.
    rewrite <- H5.
    rewrite <- H6.
    rewrite !link_trim_commut.

    unfold_advantageE.

    2:{
      clear.
      unfold flat.

      intros n u1 u2.
      now do 2 (let H := fresh in
                intros H
                ; rewrite <- fset1E in H
                ; rewrite in_fset1 in H
                ; apply (ssrbool.elimT eqP) in H
                ; inversion H ; subst).
    }

    rewrite <- (trimmed_ID ([interface #val #[ROUND2] : chRound3input → chRound2output ]
                             :|: [interface #val #[ROUND3] : chRound3input → chRound3output ])).
    rewrite <- (trimmed_ID ([interface #val #[ROUND3] : chRound3input → chRound3output ])).
    rewrite <- (trimmed_ID ([interface #val #[RUN] : SHVZK_chRelation → SHVZK_chTranscript ])).

    apply (AdvantageE_le_0 _ _ _ ).
    eapply Order.le_trans ; [ apply Advantage_triangle with (R := (SHVZK_real_aux ∘ SHVZK_real)) | ].

    replace (AdvantageE _ _ _) with (@GRing.zero R) ; [ | symmetry ].
    2:{
      rewrite H5.
      rewrite (OR_ZKP.run_interactive_or_shvzk LA _ _ _) ; [ done | .. ].
      2: assumption.
      1:{
        solve_valid_package.

        all: try rewrite H1.
        all: try rewrite H2.
        all: try rewrite H3.
        all: try rewrite H4.
        all: try rewrite H5.
        all: try rewrite H6.
        all: try rewrite trimmed_ID.

        all: try (rewrite <- fset0E , fset0U).
        1: apply H.
        2: apply valid_ID.
        3: apply valid_ID.
        4: apply valid_ID.

        1:{
          unfold idents.
          rewrite <- !fset1E.
          rewrite imfsetU.
          rewrite !imfset1.
          rewrite fdisjoint1s.
          rewrite in_fset.
          easy.
        }
        {
          clear.
          unfold flat.

          intros n u1 u2.
          rewrite !in_fsetU.
          now do 2 (let H := fresh in
                    intros H
                    ; apply (ssrbool.elimT ssrbool.orP) in H
                    ; destruct H
                    ; rewrite <- fset1E in H
                    ; rewrite in_fset1 in H
                    ; apply (ssrbool.elimT eqP) in H
                    ; inversion H ; subst).
        }
        {
          clear.
          unfold flat.

          intros n u1 u2.
          now do 2 (let H := fresh in
                    intros H
                    ; rewrite <- fset1E in H
                    ; rewrite in_fset1 in H
                    ; apply (ssrbool.elimT eqP) in H
                    ; inversion H ; subst).
        }
        {
          clear.
          unfold flat.

          intros n u1 u2.
          now do 2 (let H := fresh in
                    intros H
                    ; rewrite <- fset1E in H
                    ; rewrite in_fset1 in H
                    ; apply (ssrbool.elimT eqP) in H
                    ; inversion H ; subst).
        }

        Unshelve.
        all: revgoals.
        all: try (apply fsubsetxx || solve_in_fset) .
      }
    }
    rewrite add0r.

    rewrite <- link_trim_commut.
    rewrite H6.

    rewrite <- Advantage_link.

    Check OR_ZKP.shvzk_success.
    erewrite (OR_ZKP.shvzk_success LA _ ) ; [ easy | .. ].
    2: assumption.
    1:{
      solve_valid_package.

      all: try rewrite H1.
      all: try rewrite H2.
      all: try rewrite H3.
      all: try rewrite H4.
      all: try rewrite H5.
      all: try rewrite H6.
      all: try rewrite trimmed_ID.

      all: try (rewrite <- fset0E , fset0U).
      1: apply H.
      2: apply valid_ID.
      3: apply valid_ID.
      4: apply valid_ID.

      1:{
        unfold idents.
        rewrite <- !fset1E.
        rewrite imfsetU.
        rewrite !imfset1.
        rewrite fdisjoint1s.
        rewrite in_fset.
        easy.
      }
      {
        clear.
        unfold flat.

        intros n u1 u2.
        rewrite !in_fsetU.
        now do 2 (let H := fresh in
                  intros H
                  ; apply (ssrbool.elimT ssrbool.orP) in H
                  ; destruct H
                  ; rewrite <- fset1E in H
                  ; rewrite in_fset1 in H
                  ; apply (ssrbool.elimT eqP) in H
                  ; inversion H ; subst).
      }
      {
        clear.
        unfold flat.

        intros n u1 u2.
        now do 2 (let H := fresh in
                  intros H
                  ; rewrite <- fset1E in H
                  ; rewrite in_fset1 in H
                  ; apply (ssrbool.elimT eqP) in H
                  ; inversion H ; subst).
      }
      {
        clear.
        unfold flat.

        intros n u1 u2.
        now do 2 (let H := fresh in
                  intros H
                  ; rewrite <- fset1E in H
                  ; rewrite in_fset1 in H
                  ; apply (ssrbool.elimT eqP) in H
                  ; inversion H ; subst).
      }
      Unshelve.
      all: revgoals.
      all: try (apply fsubsetxx || solve_in_fset).
    }
  Qed.

  Lemma maximum_ballot_secrecy :
    forall (i : nat) state,
    ∀ (LA : {fset Location}) (A : raw_package),
     ValidPackage LA [interface #val #[ PROTOCOL ] : 'unit → chProtocolOutput ] A_export A →
     fdisjoint LA OR_ZKP.proof_args.MyAlg.Sigma_locs →
     let prot := fun vi => (protocol ∘ (par (round1 i state) (par (round2 i vi state) (round3 i vi state ∘ (par (maximum_ballot_secrecy_assumption_pkg vi) OR_ZKP.hacspec_or_run))))) in
      AdvantageE
        (prot true)
        (prot false)
      A = 0%R.
  Proof.
    intros.

    subst prot ; hnf.

    apply (AdvantageE_le_0 _ _ _ ).
    eapply Order.le_trans ; [ eapply Advantage_triangle with (R := (protocol
        ∘ par (round1 i state)
            (par (round2 i true state) (round3 i true state ∘ (par (maximum_ballot_secrecy_assumption_pkg true) (SHVZK_ideal_aux ∘ SHVZK_ideal)))))) | ].

    rewrite (maximum_ballot_secrecy_helper i state LA A H H0 true) ; rewrite add0r.

    rewrite Advantage_sym.
    eapply Order.le_trans ; [ apply Advantage_triangle with (R := (protocol
                                                                     ∘ par (round1 i state)
                                                                     (par (round2 i false state) (round3 i false state ∘ (par (maximum_ballot_secrecy_assumption_pkg false) (SHVZK_ideal_aux ∘ SHVZK_ideal)))))) | ].
    rewrite (maximum_ballot_secrecy_helper i state LA A H H0 false) ; rewrite add0r.
    rewrite Advantage_sym.

    trimmed_package (round1 i state).
    trimmed_package (round2 i true state).
    trimmed_package (round3 i true state).
    trimmed_package (round2 i false state).
    trimmed_package (round3 i false state).

    trimmed_package (maximum_ballot_secrecy_assumption_pkg true).
    trimmed_package (maximum_ballot_secrecy_assumption_pkg false).

    trimmed_package (SHVZK_ideal_aux).

    rewrite <- H1.
    rewrite <- H2.
    rewrite <- H3.
    rewrite <- H4.
    rewrite <- H5.
    rewrite <- H6.
    rewrite <- H7.
    rewrite <- H8.

    erewrite !link_trim_commut.

    unfold_advantageE.
    unfold_advantageE.

    2:{
      clear.
      unfold flat.

      intros n u1 u2.
      rewrite !in_fsetU.
      now do 2 (let H := fresh in
                intros H
                ; apply (ssrbool.elimT ssrbool.orP) in H
                ; destruct H
                ; rewrite <- fset1E in H
                ; rewrite in_fset1 in H
                ; apply (ssrbool.elimT eqP) in H
                ; inversion H ; subst).
    }

    replace (AdvantageE _ _ _) with (@GRing.zero R) ; [ easy | symmetry ].

    apply: eq_rel_perf_ind_ignore.
    all: fold chElement.

    1, 2: solve_valid_package.
    4,5: apply H0.
    3:{
      rewrite <- trimmed_ID ; solve_valid_package.
      1: apply H.
      2: apply valid_ID.
      1:{
        unfold idents.
        rewrite <- !fset1E.
        rewrite imfsetU.
        rewrite !imfset1.
        rewrite fdisjoint1s.
        rewrite in_fset.
        easy.
      }
      {
        clear.
        unfold flat.

        intros n u1 u2.
        rewrite !in_fsetU.
        now do 2 (let H := fresh in
                  intros H
                  ; apply (ssrbool.elimT ssrbool.orP) in H
                  ; destruct H
                  ; rewrite <- fset1E in H
                  ; rewrite in_fset1 in H
                  ; apply (ssrbool.elimT eqP) in H
                  ; inversion H ; subst).
      }
    }
    1: apply fsubsetxx || solve_in_fset.

    Unshelve.
    all: revgoals.
    all: try (apply fsubsetxx || solve_in_fset) .

    erewrite <- !link_trim_commut.

    erewrite H2.
    erewrite H3.
    erewrite H4.
    erewrite H5.
    erewrite H6.
    erewrite H7.
    erewrite H8.

    rewrite <- fset0E ; rewrite fset0U.

    {
      clear H.
      unfold eq_up_to_inv.

      (* simplify_eq_rel inp. *) (* TODO: Does not work? *)
      intros.
      unfold get_op_default.

      rewrite in_fset in H.
      rewrite <- !fset1E in H.
      simpl in H.

      apply (ssrbool.elimT ssrbool.orP) in H ; simpl in H.
      destruct H.
      {
        apply (ssrbool.elimT eqP) in H.
        inversion H ; subst.
        clear H.

        simpl.

        choice_type_eqP_handle.
        choice_type_eqP_handle.

        destruct x as [xi [[w r] d]].
        unfold cast_fun.
        simpl.

        unfold eq_rect_r.
        simpl.
        fold chElement.

        (* DDH assumption *)
        unfold commit_to_vote at 1 2.

        rewrite <- bind_ret at 1.
        rewrite <- bind_ret.

        rewrite !bind_assoc ;rewrite !bind_rewrite ; fold chElement.
        rewrite !bind_assoc ;rewrite !bind_rewrite ; fold chElement.
        rewrite !bind_assoc.

        do 2 replace (f_cvp_i _) with (ret_both (i : int32)) by now apply both_eq.
        do 2 replace (f_cvp_xi _) with (ret_both (xi)) by now apply both_eq.

        replace (f_cvp_vote _) with (ret_both (true : 'bool)) by now apply both_eq.
        replace (f_cvp_vote _) with (ret_both (false : 'bool)) by now apply both_eq.

        ssprove_same_head x0. (* f_accept *)
        rewrite !bind_assoc.

        apply somewhat_substitution.
        apply somewhat_substitutionR.
        rewrite !bind_rewrite.
        rewrite !bind_assoc.
        apply somewhat_substitution.
        apply somewhat_substitutionR.
        rewrite !bind_rewrite.
        rewrite !bind_assoc.
        apply somewhat_substitution.
        apply somewhat_substitutionR.
        rewrite !bind_rewrite.
        rewrite !bind_assoc.
        apply somewhat_substitution.
        apply somewhat_substitutionR.
        rewrite !bind_rewrite.
        rewrite !bind_assoc.
        apply somewhat_substitution.
        apply somewhat_substitutionR.
        rewrite !bind_rewrite.
        rewrite !bind_assoc.
        rewrite !bind_rewrite.
        rewrite !bind_assoc.

        (* bind commit_to *)
        set (pre := fun _ => _).
        eapply r_bind with (mid := pre_to_post pre).
        {
          unfold commit_to at 1 2.

          admit. (* DDH assumption / commit hiding *)
        }
        intros.
        apply rpre_hypothesis_rule
        ; intros ? ? []
        ; apply rpre_weaken_rule with (pre := pre) ; [ | now intros ? ? [] ; subst ]
        ; subst ; clear H1 ; subst pre.

        simpl.
        ssprove_refl.
      }
      {
        apply (ssrbool.elimT ssrbool.orP) in H ; simpl in H.
        destruct H ; [ | easy].
        apply (ssrbool.elimT eqP) in H.
        inversion H ; subst.
        clear H.

        destruct x as [xi [[w r] d]].

        simpl.

        choice_type_eqP_handle.
        choice_type_eqP_handle.
        simpl.

        erewrite !cast_fun_K.

        erewrite !code_link_bind.
        setoid_rewrite bind_assoc.

        erewrite !(code_link_scheme _ _ (is_state (compute_g_pow_yi _ _))).
        2, 3: ssprove_valid_code.

        do 2 replace (f_cvp_i _) with (ret_both (i : int32)) by now apply both_eq.

        ssprove_same_head g_pow_yi.

        simpl.
        choice_type_eqP_handle.
        choice_type_eqP_handle.
        erewrite !cast_fun_K.
        choice_type_eqP_handle.
        erewrite !cast_fun_K.
        simpl.

        apply (r_uniform_bij) with (f := fun x => x) ; [ now apply inv_bij | intros xi2 ].

        do 2 replace (f_cvp_xi _) with (ret_both xi) by now apply both_eq.

        replace (f_cvp_vote _) with (ret_both (true : 'bool)) by now apply both_eq.
        replace (f_cvp_vote _) with (ret_both (false : 'bool)) by now apply both_eq.

        apply (r_uniform_bij) with (f := fun x => x) ; [ now apply inv_bij | intros ri ].

        unfold assertD.
        rewrite !otf_fto.

        replace (OR_ZKP.proof_args.MyParam.R _ _) with true by now unfold OR_ZKP.proof_args.MyParam.R ; rewrite !eqxx.
        replace (OR_ZKP.proof_args.MyParam.R _ _) with true by now unfold OR_ZKP.proof_args.MyParam.R ; rewrite !eqxx.

        simpl.
        apply (r_uniform_bij) with (f := fun x => x) ; [ now apply inv_bij | intros w0 ].
        apply (r_uniform_bij) with (f := fun x => x) ; [ now apply inv_bij | intros r0 ].
        apply (r_uniform_bij) with (f := fun x => x) ; [ now apply inv_bij | intros d0 ].

        (* ssprove_same_head x0. *)
        simpl.
        ssprove_code_simpl.
        ssprove_code_simpl_more.
        setoid_rewrite (code_link_scheme _ _ _).
        2, 3, 4, 5: ssprove_valid_code.

        set (pre := fun _ => _).
        eapply r_bind with (mid := pre_to_post pre).
        {

          rewrite <- bind_ret at 1.
          rewrite <- bind_ret.

          set (compute_group_element_for_vote _ _ _).
          set (compute_group_element_for_vote _ _ _).

          (* set (lift_both (f_prod _ _)). *)
          (* set (lift_both (f_prod _ _)). *)

          apply (somewhat_let_substitution  _ _ b _ pre).
          Misc.pattern_lhs_approx.
          set (let_both _ _ ).
          pattern b0 in b1.
          set (fun _ => _) in b1.
          refine (somewhat_let_substitutionR  _ H b0 y pre _).
          subst H b1 y b b0 ; hnf in *.

          eapply r_bind with (mid := pre_to_post pre).
          {
            unfold compute_group_element_for_vote at 1 2.

            (* DDH assumption, g^xi yi + vi hides xi and vi, for known g^yi *)
            replace (ifb _ then _ else _) with (f_field_one) by now apply both_eq ; destruct f_field_one as [[]].
            replace (ifb _ then _ else _) with (f_field_zero) by now apply both_eq ; destruct f_field_zero as [[]].

            eassert (DDH : 'unit → 'public × 'public × 'public) by admit.


            pose OVN_proofs.pid.
            unfold OVN_proofs.pid in c.
            unfold OVN_proofs.Pid in c.
            cbn in c.
            epose (OVN_old_proofs.vote_hiding (fto (inord i)) _ _ _ _ _ _ _ _ _ _ _ _).
            unfold Exec_i_realised in i0.
            unfold Exec_i in i0.
            simpl in i0.
            unfold Exec in i0.
            simpl in i0.


            (* eassert (exists (yi : v_Z), g ^+ FieldToWitness yi = g_pow_yi) by admit. (* TODO *) *)
            (* destruct H as [yi H]. *)
            (* rewrite <- H. *)

            (* pose OVN_proofs.secret. *)
            (* unfold OVN_proofs.secret in c. *)

            (* epose (OVN_old_proofs.vote_hiding_bij ((fto (FieldToWitness yi * FieldToWitness xi)%R) : OVN_proofs.secret) true). *)

            (* eapply f_equal with (f := otf) in e. *)
            (* rewrite !OVN_old_proofs.Hord in e. *)
            (* rewrite !otf_fto in e. *)

            (* rewrite <- bind_ret at 1. *)
            (* rewrite <- bind_ret. *)

            (* apply somewhat_substitution. *)
            (* apply somewhat_substitutionR. *)

            (* apply r_ret. *)
            (* intros. *)
            (* split ; [ clear H | easy ]. *)

            (* Misc.push_down_sides. *)
            (* rewrite !(proj1 both_equivalence_is_pure_eq (HOGaFE.pow_base _)). *)

            (* rewrite <- (WitnessToFieldCancel xi). *)
            (* rewrite <- pow_witness_to_field. *)
            (* rewrite <- expgM. *)

            (* rewrite <- (WitnessToFieldCancel (is_pure f_field_one)). *)
            (* rewrite <- (WitnessToFieldCancel (is_pure f_field_zero)). *)
            (* Misc.push_down_sides. *)
            (* rewrite <- !pow_witness_to_field. *)

            (* rewrite rmorph1. rewrite rmorph0. *)

            (* unfold "*"%g in e. *)
            (* simpl in e. *)
            (* unfold setoid_lower2, F, U, sg_prod in e ; simpl in e. *)
            (* rewrite !trunc_pow in e. *)

            (* rewrite <- (WitnessToFieldCancel xi). *)
            (* rewrite <- pow_witness_to_field. *)
            (* rewrite <- expgM. *)

            (* rewrite <- (WitnessToFieldCancel (is_pure f_field_one)). *)
            (* rewrite <- (WitnessToFieldCancel (is_pure f_field_zero)). *)
            (* Misc.push_down_sides. *)
            (* rewrite <- !pow_witness_to_field. *)

            (* unfold OVN_GroupParam.g in e. *)
            (* unfold g. *)
            (* rewrite rmorph1. rewrite rmorph0. *)

            (* setoid_rewrite e. *)

            (* f_equal. *)
            (* f_equal. *)
            (* f_equal. *)
            (* f_equal. *)

            (* rewrite expgD. *)
            (* rewrite !trunc_pow. *)
            (* rewrite <- expgD. *)




            (* (* FieldToWitness (is_pure (f_mul (ret_both yi) (ret_both xi))) *) *)
            (* (* c := yixi *) *)


            (* rewrite f_prod. *)

            (* (if v then fto (Zp_add (otf c) Zp1) else fto (Zp_add (otf c) (Zp_opp Zp1))) *)
            (* replace (g_) *)
            (* (* OVN/vote_hiding_bij *) *)

            admit.
          }
          intros.
          apply rpre_hypothesis_rule
          ; intros ? ? []
          ; apply rpre_weaken_rule with (pre := pre) ; [ | now intros ? ? [] ; subst ]
          ; subst ; clear H1 ; subst pre.


          Misc.pattern_lhs_approx.
          unfold let_both at 1.
          subst H.

          apply (somewhat_let_substitution).
          apply (somewhat_let_substitutionR).
          ssprove_same_head b_temp0.

          apply (somewhat_let_substitution).
          apply (somewhat_let_substitutionR).
          ssprove_same_head b_temp1.

          apply (somewhat_let_substitution).
          apply (somewhat_let_substitutionR).

          rewrite !otf_fto.

          set (pre := fun _ => _).
          eapply r_bind with (mid := pre_to_post pre).
          {
            (* DDH assumption, g^xi yi + vi hides xi and vi, for known g^yi *)

            apply (somewhat_substitution).
            apply (somewhat_substitutionR).
            simpl.

            ssprove_same_head tal.
            eapply r_bind with (mid := pre_to_post pre).
            {
              admit.
            }
            intros.
            apply rpre_hypothesis_rule
            ; intros ? ? []
            ; apply rpre_weaken_rule with (pre := pre) ; [ | now intros ? ? [] ; subst ]
            ; subst ; clear H1 ; subst pre.

            ssprove_refl.
          }
          intros.
          apply rpre_hypothesis_rule
          ; intros ? ? []
          ; apply rpre_weaken_rule with (pre := pre) ; [ | now intros ? ? [] ; subst ]
          ; subst ; clear H1 ; subst pre.

          ssprove_refl.
        }
        intros.
        apply rpre_hypothesis_rule
        ; intros ? ? []
        ; apply rpre_weaken_rule with (pre := pre) ; [ | now intros ? ? [] ; subst ]
        ; subst ; clear H1 ; subst pre.

        ssprove_refl.
      }
    }
  Qed.

End OVN_proof.
