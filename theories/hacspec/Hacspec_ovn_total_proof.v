Set Warnings "-ambiguous-paths,-notation-overridden,-notation-incompatible-format".
From mathcomp Require Import all_ssreflect fingroup.fingroup ssreflect.
Set Warnings "ambiguous-paths,notation-overridden,notation-incompatible-format".
From SSProve.Crypt Require Import choice_type Package Prelude.
Import PackageNotation.
From extructures Require Import ord fset.
Set Warnings "-ambiguous-paths".
From mathcomp Require Import word_ssrZ word.
Set Warnings "ambiguous-paths".
(* From Jasmin Require Import word. *)

Set Warnings "-notation-overridden".
From Coq Require Import ZArith.
Set Warnings "notation-overridden".
From Coq Require Import Strings.String.
Import List.ListNotations.
Open Scope list_scope.
Open Scope Z_scope.
Open Scope bool_scope.

From Hacspec Require Import ChoiceEquality.
From Hacspec Require Import LocationUtility.
From Hacspec Require Import Hacspec_Lib_Comparable.
Set Warnings "-notation-incompatible-prefix".
From Hacspec Require Import Hacspec_Lib_Pre.
From Hacspec Require Import Hacspec_Lib.
Set Warnings "notation-incompatible-prefix".

Open Scope hacspec_scope.
Import choice.Choice.Exports.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".
Set Primitive Projections.

Global Obligation Tactic := (* try timeout 8 *) solve_ssprove_obligations.

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

Set Warnings "-notation-incompatible-prefix".
From SSProve.Mon Require Import SPropBase.
Set Warnings "notation-incompatible-prefix".

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
From OVN Require Import Hacspec_helpers.
From OVN Require Import Hacspec_ovn_group_and_field.
From OVN Require Import Hacspec_ovn_sigma_setup.
From OVN Require Import Hacspec_ovn_schnorr.
From OVN Require Import Hacspec_ovn_or.

Module OVN_proof (HOP : HacspecOvnParameter) (HOGaFP : HacspecOvnGroupAndFieldParameter HOP) (HOGaFE : HacspecOvnGroupAndFieldExtra HOP HOGaFP) (HGPA : HacspecGroupParamAxiom HOP HOGaFP HOGaFE).
  Module Schnorr_ZKP := OVN_schnorr_proof HOP HOGaFP HOGaFE HGPA.
  Module OR_ZKP := OVN_or_proof HOP HOGaFP HOGaFE HGPA.

  Include HGPA.

  Module OVN_Param.
    Definition N : nat := is_pure HOP.n.
    Lemma N_pos : Positive N. Proof. apply HOP.n_pos. Qed.
  End OVN_Param.

  Import HOGaFE.GroupAndField.OVN.
  (* Import HOGaFE.GroupAndField. *)
  (* Import HOGaFE. *)
  Import HGPA.GaFP.
  Import HGPA.GaFP.HacspecGroup.
  Import choice_type Package Prelude.
  Import PackageNotation.

  Lemma cyclic_group_to_exponent :
    forall x,
    ∃ i : nat, x = g ^+ i /\ i < #[g].
  Proof.
    intros.

    assert (x \in <[g]>).
    {
      unfold HacspecGroup.gT in x.
      unfold HacspecGroup.g.
      setoid_rewrite <- HOGaFE.v_G_g_gen.
      simpl.
      apply in_setT.
    }

    (* destruct (ssrbool.elimT (cycleP HacspecGroup.g x) H). *)
    pose (cyclePmin H).
    destruct s ; subst.
    exists x0.
    easy.
  Qed.

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

  Ltac split_advantage O :=
    try apply (AdvantageE_le_0 _ _ _ ) ;
    eapply Order.le_trans ; [ apply Advantage_triangle with (R := O) | ] ;
    replace (AdvantageE _ _ _) with (@GRing.zero R) ; [
        replace (AdvantageE _ _ _) with (@GRing.zero R) ; [ rewrite add0r ; apply Order.POrderTheory.ge_refl | symmetry ] |
        symmetry ] ; revgoals.


  Lemma nseq_n_pos :
    forall A n,
      Positive n ->
      match
      nseq_ A n
    with
    | 'unit => True
    | chMap (chFin n0) C =>
        match pos n0 with
        | 0%N => False
        | _.+1 => C = A
        end
    | chMap 'nat C | chList C => C = A
    | _ => False
         end.
  Proof.
    intros.
    simpl.
    destruct n0.
    - done.
    - reflexivity.
  Defined.

  (** Should be hax library definitions *)

  Lemma array_update_eq2 : forall {n}, (Positive n) -> forall {A : choice_type} (b5 : both (nseq_ A n)) b (i : int32),
      (Z.to_nat (unsigned i) < n)%coq_nat ->
      is_pure (array_index
                 (update_at_usize b5 (ret_both i) b)
                 (ret_both i)) =
        is_pure b.
  Proof.
    intros n ? A.
    intros.

    unfold update_at_usize at 1.
    unfold lift3_both at 1.
    unfold array_index at 1.
    unfold lift2_both at 1 2.
    simpl.

    simpl in *.

    destruct n.
    1: discriminate.


    unfold Hacspec_Lib_Pre.array_upd.
    unfold array_upd_clause_1.
    unfold array_upd_clause_1_clause_1.

    unfold Hacspec_Lib_Pre.array_index at 1.

    destruct lt_dec.
    {
      unfold array_index_clause_2.
      destruct le_lt_dec ; [ easy | ].
      rewrite setmE.
      epose (proj1 (ord_ext
                      (Z.to_nat (unsigned i))
                      (Z.to_nat (unsigned i))) erefl).
      apply (ssrbool.introT eqP) in e.
      rewrite e.
      simpl.
      reflexivity.

      Unshelve.
      2,3: apply /ltP ; apply H0.
    }
    {
      contradiction.
    }
  Qed.

  Lemma array_update_eq : forall {A : choice_type} (b5 : both (nseq_ A (from_uint_size (is_pure n)))) b (i : int32),
      (Z.to_nat (unsigned i) < (from_uint_size (is_pure n)))%coq_nat ->
      is_pure (array_index
                 (update_at_usize b5 (ret_both i) b)
                 (ret_both i)) =
        is_pure b.
  Proof.
    intros A.
    intros.

    apply array_update_eq2.
    1:{ apply n_pos. }
    apply H.
  Qed.

  Lemma array_update_neq2 : forall {n}, (Positive n) -> forall {A : choice_type} (b5 : both (nseq_ A n)) b (i x : int32),
      (Z.to_nat (unsigned i) < n)%coq_nat ->
      (Z.to_nat (unsigned x) <> Z.to_nat (unsigned i)) ->
      is_pure (array_index
                 (update_at_usize b5 (ret_both i) b)
                 (ret_both x)) =
        is_pure (array_index b5 (ret_both x)).
  Proof.
    intros n ? A.
    intros.

    unfold update_at_usize at 1.
    unfold lift3_both at 1.
    unfold array_index at 1 2.
    unfold lift2_both at 1 2 3.
    simpl.

    destruct n.
    1: discriminate.

    unfold Hacspec_Lib_Pre.array_upd.
    unfold array_upd_clause_1.
    unfold array_upd_clause_1_clause_1.

    unfold Hacspec_Lib_Pre.array_index at 1 2.

    destruct lt_dec.
    {
      unfold array_index_clause_2.
      destruct le_lt_dec ; [ easy | ].
      {
        rewrite setmE.

        replace (_ == _) with false.
        {
          reflexivity.
        }
        symmetry.
        apply /eqP.
        red ; intros.
        apply ord_ext in H2.
        apply H1.
        easy.
      }
    }
    {
      contradiction.
    }
  Qed.

  Lemma array_update_neq : forall {A : choice_type} (b5 : both (nseq_ A (from_uint_size (is_pure n)))) b (i x : int32),
      (Z.to_nat (unsigned i) < (from_uint_size (is_pure n)))%coq_nat ->
      (Z.to_nat (unsigned x) <> Z.to_nat (unsigned i)) ->
      is_pure (array_index
                 (update_at_usize b5 (ret_both i) b)
                 (ret_both x)) =
        is_pure (array_index b5 (ret_both x)).
  Proof.
    intros.
    apply array_update_neq2.
    1: apply n_pos.
    all: assumption.
  Qed.

  Lemma n_seq_array_or_seq_simpl : forall {A : choice_type} {n : nat} (b5 : both (nseq_ A n.+1)),
      (n_seq_array_or_seq b5 (nseq_n_pos A n.+1 erefl)) = b5.
  Proof.
    intros.
    unfold nseq_n_pos.
    cbn.
    assert (positive_eqP {| pos := n0.+1; cond_pos := erefl |} _ (eqxx _) = erefl).
    {
      easy.
    }
    rewrite H.
    reflexivity.
  Qed.

  Lemma n_seq_array_or_seq_simpl_pos : forall {A : choice_type} {n : nat} (b5 : both (nseq_ A n)),
      (Positive n)%R ->
      match n as k return both (nseq_ A k) -> _ with
      | 0%nat => fun _ => False
      | S n0 => fun b5 => n_seq_array_or_seq b5 (nseq_n_pos A n0.+1 erefl) = b5
      end b5.
  Proof.
    intros.
    destruct n0.
    - discriminate.
    - apply (n_seq_array_or_seq_simpl b5).
  Defined.

  (* Lemma n_seq_array_or_seq_eq : forall {A : choice_type} (b5 : both (nseq_ A (from_uint_size (is_pure n)))) v, *)
  (*     (n_seq_array_or_seq b5 n_pos) = b5. *)
  (* Proof. *)
  (*   intros. *)
  (*   rewrite H. *)
  (*   now rewrite n_seq_array_or_seq_simpl. *)
  (* Qed. *)

  Lemma pos_pos : Positive (from_uint_size (is_pure n)).
  Proof. apply n_pos. Qed.

  (* Lemma strip_nseq_array_or_seq : *)
  (*   forall {WS : wsize} i b (b5 : both (nseq_ v_G (from_uint_size (is_pure n)))) x, *)
  (*     is_pure (array_index (update_at_usize b5 (ret_both i) b) x) = *)
  (* is_pure (array_index b5 x) -> *)
  (*   is_pure *)
  (*   (array_index *)
  (*      (n_seq_array_or_seq (update_at_usize b5 (ret_both i) b) *)
  (*         (HOGaFE.GroupAndField.OVN.compute_g_pow_yi_obligations_obligation_1 *)
  (*            (update_at_usize b5 (ret_both i) b))) x) = *)
  (* is_pure *)
  (*   (array_index (WS := WS) *)
  (*      (n_seq_array_or_seq b5 (HOGaFE.GroupAndField.OVN.compute_g_pow_yi_obligations_obligation_1 b5)) *)
  (*      x). *)
  (* Proof. *)
  (*   intros ? ? ? ? ? H_some. *)

  (*   epose proof (array_update_neq b5). *)
  (*   epose proof (pos_pos). *)

  (*   set (HOGaFE.GroupAndField.OVN.compute_g_pow_yi_obligations_obligation_1 _). *)
  (*   set (HOGaFE.GroupAndField.OVN.compute_g_pow_yi_obligations_obligation_1 b5). *)
  (*   assert (y0 = y). *)
  (*   { *)
  (*     subst y y0. *)
  (*     unfold HOGaFE.GroupAndField.OVN.compute_g_pow_yi_obligations_obligation_1. *)
  (*     cbn in *. *)
  (*     cbn. *)
  (*     clear -H0. *)
  (*     destruct is_pure. *)
  (*     cbn. *)
  (*     destruct toword. *)
  (*     - discriminate. *)
  (*     - simpl in *. *)
  (*       now destruct (Z.to_nat _). *)
  (*     - discriminate. *)
  (*   } *)
  (*   rewrite H1. *)
  (*   clear -H_some H H0. *)

  (*   subst y. *)
  (*   generalize dependent b5. *)
  (*   set (from_uint_size (is_pure _)). *)
  (*   simpl. *)
  (*   intros. *)

  (*   cbn in *. *)
  (*   epose proof (n_seq_array_or_seq_simpl_pos b5 H0). *)

  (*   set (update_at_usize _ _ _). *)
  (*   subst y. *)

  (*   generalize dependent (HOGaFE.GroupAndField.OVN.compute_g_pow_yi_obligations_obligation_1 b0). *)
  (*   destruct (is_pure n). *)
  (*   destruct toword. *)
  (*   - discriminate. *)
  (*   - intros. *)
  (*     cbn in H0, b5, H, b0, y |- *. *)
  (*     set (Z.to_nat _) in H1. *)
  (*     cbn in n0. *)
  (*     subst n0. *)

  (*     destruct (Z.to_nat _). *)
  (*     + discriminate. *)
  (*     + hnf in *. *)

  (*       rewrite <- (proof_irrelevance _ y _) in H1. *)
  (*       rewrite H1. *)

  (*       epose proof (n_seq_array_or_seq_simpl_pos b0 H0). *)
  (*       hnf in H2. *)
  (*       rewrite <- (proof_irrelevance _ y _) in H2. *)
  (*       rewrite H2. *)
  (*       clear H1 H2. *)
  (*       subst b0. *)

  (*       apply H_some. *)
  (*   - discriminate. *)
  (* Qed. *)

  Lemma compute_g_pow_yi_update_eq : forall (b5 : both (nseq_ v_G (from_uint_size (is_pure n)))) b (i : int32),
      (Z.to_nat (unsigned i) < from_uint_size (is_pure n))%coq_nat ->
      is_pure (compute_g_pow_yi
                 (ret_both i)
                 (update_at_usize b5 (ret_both i) b)) =
        is_pure (compute_g_pow_yi
                   (ret_both i)
                   b5
          ).
  Proof.
    intros.

    (* unfold update_at_usize at 1. *)
    (* unfold lift3_both at 1. *)
    unfold compute_g_pow_yi at 1 2.
    (* unfold lift2_both at 1 2. *)
    simpl.

    repeat unfold let_both at 1.
    set (fun _ => _).
    set (fun _ => _).
    set (fun _ => _).

    assert (forall (x : both int32), Z.to_nat (unsigned (is_pure x)) ≠ Z.to_nat (unsigned i) -> forall y, is_pure (y0 x y) = is_pure (y1 x y)).
    {
      intros.
      subst y0 y1.
      simpl.
      rewrite !(hacspec_function_guarantees2 f_prod y2).
      f_equal.
      f_equal.
      f_equal.
      f_equal.

      rewrite hacspec_function_guarantees.
      (* apply strip_nseq_array_or_seq. *)
      now rewrite array_update_neq.
    }

    (* TODO: fold stuff *)
    simpl.

    assert (
        forall {A B} {L : both (chList B)} {f g : both B -> both A -> both A} {a : both A},
        (forall (x : both _) y, is_pure x \in is_pure L -> is_pure (f x y) = is_pure (g x y)) ->
        is_pure (foldi_both_list L f a) =
              is_pure (foldi_both_list L g a)).
    {
      intros.
      unfold foldi_both_list at 1 2.
      simpl.

      destruct L as [[L_pure L_state] [L_valid_code L_valid_both] L_eq].
      simpl in *.
      clear -H1.

      rewrite !(hacspec_function_guarantees _ (lift_both _)).
      simpl.
      rewrite <- !(hacspec_function_guarantees).

      generalize dependent a.
      induction L_pure ; intros.
      - reflexivity.
      - simpl.
        rewrite IHL_pure.
        {
          rewrite !(hacspec_function_guarantees _ (lift_both _)).
          rewrite H1.
          {
            simpl.
            reflexivity.
          }
          simpl.
          rewrite in_cons.
          rewrite eqxx.
          reflexivity.
        }
        {
          intros.
          apply H1.
          rewrite in_cons.
          rewrite H ; apply /orP ; right ; reflexivity.
        }
    }

    rewrite !(hacspec_function_guarantees2 _ (foldi_both_list _ _ _)).
    erewrite !(H1 _ _ _ y0 y1) ; [ reflexivity | intros .. ].
    1:{
      eapply H0 ; red ; intros ; clear -H H2 H3.
      subst y.
      unfold Build_Range , prod_both at 1 in H2 ; simpl in H2.

      apply f_equal with (f := Z.of_nat) in H3.
      rewrite !Z2Nat.id in H3 ; [ | apply wunsigned_range.. ].
      apply f_equal with (f := wrepr U32) in H3.
      rewrite !wrepr_unsigned in H3.
      rewrite H3 in H2 ; clear H3.

      apply (ssrbool.elimT mapP) in H2.
      destruct H2.
      rewrite H1 in H H0 ; clear H1.

      rewrite mem_iota in H0.

      set (Z.to_nat (unsigned (is_pure (_ .+ _)))) in H0.
      set (Z.to_nat _) in H0.

      assert (n0 < n1)%N by easy.
      rewrite subnKC in H0.
      2: easy.

      clear -H0.

      apply (ssrbool.elimT andP) in H0.
      destruct H0.

      assert (x0 < n0)%N.
      2: easy.
      {
        unfold n0.
        setoid_rewrite wunsigned_repr.
        simpl.
        rewrite Zmod_small.
        {
          unfold urepr.
          simpl.
          rewrite Z2Nat.inj_add.
          {
            rewrite Z2Nat.inj_mod.
            {
              rewrite Nat2Z.id.
              rewrite Nat.mod_small.
              {
                easy.
              }
              {
                eapply Nat.lt_trans.
                1: apply /ltP ; apply H0.
                subst n1.
                apply Z2Nat.inj_lt.
                1: apply wunsigned_range.
                1: easy.
                apply wunsigned_range.
              }
            }
            {
              apply Zle_0_nat.
            }
            {
              easy.
            }
          }
          {
            now apply Z_mod_lt.
          }
          {
            easy.
          }
        }
        {
          split.
          {
            apply Z.add_nonneg_nonneg.
            2: easy.
            setoid_rewrite wunsigned_repr.
            now apply Z_mod_lt.
          }
          {
            unfold urepr.
            simpl.

            rewrite Zmod_small.
            2:{
              split.
              1: apply Zle_0_nat.
              apply Z.lt_trans with (Z.of_nat n1).
              2:{
                subst n1.
                rewrite Z2Nat.id ; apply wunsigned_range.
              }
              now apply Nat2Z.inj_lt.
            }

            eapply Z.lt_le_trans with (m := Z.of_nat n1.+1).
            1:{
              rewrite Nat2Z.inj_succ.
              unfold urepr.
              simpl "\val".
              apply Zsucc_lt_compat.
              apply Nat2Z.inj_lt.
              apply /ltP.
              assumption.
            }
            rewrite Nat2Z.inj_succ.
            apply Zlt_le_succ.
            rewrite Z2Nat.id ; apply wunsigned_range.
          }
        }
      }
    }
    1:{
      eapply H0 ; red ; intros ; clear -H H2 H3.
      subst y.
      unfold Build_Range , prod_both at 1 in H2 ; simpl in H2.

      apply f_equal with (f := Z.of_nat) in H3.
      rewrite !Z2Nat.id in H3 ; [ | apply wunsigned_range.. ].
      apply f_equal with (f := wrepr U32) in H3.
      rewrite !wrepr_unsigned in H3.
      rewrite H3 in H2 ; clear H3.

      apply (ssrbool.elimT mapP) in H2.
      destruct H2.
      rewrite H1 in H H0 ; clear H1.

      rewrite mem_iota in H0.

      simpl in H0.
      rewrite wunsigned_repr in H0.
      rewrite Zmod_small in H0. 2: easy.
      rewrite add0n in H0.
      setoid_rewrite subn0 in H0.
      clear -H0.

      rewrite wunsigned_repr in H0.
      rewrite Z2Nat.inj_mod in H0.
      2: apply Zle_0_nat.
      2: easy.
      rewrite Nat2Z.id in H0.
      set (Z.to_nat _) in H0.

      epose (Nat.Div0.mod_le x0 n0).
      apply (ssrbool.elimT ltP) in H0.
      epose proof (Nat.lt_le_trans _ _ _ H0 l).
      clear -H.
      easy.
    }
  Qed.

  (*** Solution *)

  (** DL *)

  Notation " 'chDLInput' " :=
    (f_Z)
    (in custom pack_type at level 2).

  Notation " 'chDLOutput' " :=
    (v_G)
    (in custom pack_type at level 2).

  Definition DL : nat := 101.
  Definition DL_GUESS : nat := 102.
  Definition DL_loc : Location := (option v_Z ; 1000%nat).

  Program Definition get_option' (A : choice_type) (n : nat) : code (fset [('option A ; n)]) [interface] A :=
    {code
       ox ← get ('option A; n) ;;
     match ox with
     | Some x => ret x
     | None => fail
     end
    }.
  Next Obligation.
    destruct v.
    - apply valid_ret.
    - apply valid_fail.
  Qed.
  Fail Next Obligation.

  Definition get_option (ℓ : Location) {A : choice_type} `(ℓ.π1 = 'option A) : code (fset [ℓ]) [interface] A.
    destruct ℓ.
    simpl in H.
    rewrite H.
    apply (get_option' A n0).
  Defined.

  Definition DL_game' :
    bool ->
    package
      (fset [DL_loc])
      [interface]
      [interface
         #val #[ DL ] : 'unit → chDLOutput ;
       #val #[ DL_GUESS ] : chDLInput → 'bool
      ]
    :=
    λ b,
      [package
        #def #[ DL ] (_ : 'unit) : chDLOutput
        {
          xi ← sample (uniform #|'Z_q|) ;; let xi := WitnessToField (otf xi) in
          #put DL_loc := some xi ;;
          ret (g ^+ FieldToWitness xi : v_G)
        } ;
        #def #[ DL_GUESS ] (xi : chDLInput) : 'bool
        {
          ax ← get_option DL_loc erefl ;;
          if b
          then ret false
          else ret (g ^+ FieldToWitness ax == g ^+ FieldToWitness xi)
        }
      ].

  Definition DL_game :
    loc_GamePair
      [interface
         #val #[ DL ] : 'unit → chDLOutput ;
         #val #[ DL_GUESS ] : chDLInput → 'bool
      ]
    := λ b, {locpackage DL_game' b}.
  Fail Next Obligation.

  (* (∀ D, DDH.ϵ_DDH D <= ϵ_DDH) *)
  Definition ϵ_DL := Advantage DL_game.

  (** DDH *)

  Notation " 'chDDHInput' " :=
    (f_Z)
    (in custom pack_type at level 2).

  Notation " 'chDDHOutput' " :=
    (v_G × v_G × v_G)
    (in custom pack_type at level 2).

  Definition DDH : nat := 1010.
  Definition DDH_GUESS : nat := 1020.
  Definition DDH_loc1 : Location := (option v_Z ; 1001%nat).
  Definition DDH_loc2 : Location := (option v_Z ; 1002%nat).

 Definition DDH_game :
    bool -> package
      (fset [DDH_loc1; DDH_loc2])
      [interface]
      [interface
         #val #[ DDH ] : 'unit → chDDHOutput
      ] :=
    fun b =>
      [package
        #def #[ DDH ] (_ : 'unit) : chDDHOutput
        {
          xi ← sample (uniform (H := Zq_pos) #|'Z_q|) ;; let xi := WitnessToField (otf xi) in
          #put DDH_loc1 := some xi ;;
          yi ← sample (uniform (H := Zq_pos) #|'Z_q|) ;; let yi := WitnessToField (otf yi) in
          #put DDH_loc2 := some yi ;;
          if b
          then (
              zi ← sample (uniform (H := Zq_pos) #|'Z_q|) ;; let zi := WitnessToField (otf zi) in
              @ret (v_G × v_G × v_G) ((g ^+ FieldToWitness xi : v_G, g ^+ FieldToWitness yi : v_G, g ^+ (FieldToWitness zi))))
          else @ret (v_G × v_G × v_G) ((g ^+ FieldToWitness xi : v_G, g ^+ FieldToWitness yi : v_G, g ^+ (FieldToWitness xi * FieldToWitness yi)))
        }
      ].

  (* (∀ D, DDH.ϵ_DDH D <= ϵ_DDH) *)
  Definition ϵ_DDH := Advantage DDH_game.

  (** Schnorr *) (* TODO: move to schnorr file *)
  Notation " 'schnorrInput' " :=
    (f_Z × v_G)
      (in custom pack_type at level 2).

  Notation " 'schnorrOutput' " :=
    (t_SchnorrZKPCommit)
      (in custom pack_type at level 2).

  Definition SCHNORR : nat := 212.

  Program Definition schnorr_real :
    package fset0
      [interface]
      [interface #val #[ SCHNORR ] : schnorrInput → schnorrOutput]
    :=
    [package
       #def #[ SCHNORR ] ('(xi, h) : schnorrInput) : schnorrOutput
       {
         #assert Schnorr_ZKP.Schnorr.MyParam.R h (FieldToWitness xi) ;;
         ri ← sample (uniform #|'Z_q|) ;; let ri := WitnessToField (otf ri) in
         is_state (schnorr_zkp (ret_both ri) (ret_both h) (ret_both xi))
       }
    ].
  Final Obligation.
    intros.
    ssprove_valid.
    destruct x as [xi h].
    ssprove_valid.
    1: apply valid_scheme ; rewrite <- fset0E ; apply (ChoiceEquality.is_valid_code (both_prog_valid _)).
  Qed.

  Notation " 'schnorrMidInp' " :=
    (Schnorr_ZKP.Schnorr.MyAlg.choiceStatement × Schnorr_ZKP.Schnorr.MyAlg.choiceWitness)
      (in custom pack_type at level 2).

  Notation " 'schnorrMidOut' " :=
    (Schnorr_ZKP.Schnorr.MyAlg.choiceTranscript)
    (in custom pack_type at level 2).

  Program Definition schnorr_mid :
    package fset0
      [interface #val #[ Schnorr_ZKP.Schnorr.Sigma.RUN ] : schnorrMidInp → schnorrMidOut ]
      [interface #val #[ SCHNORR ] : schnorrInput → schnorrOutput]
    :=
    [package
       #def #[ SCHNORR ] ('(xi, h) : schnorrInput) : schnorrOutput
       {
         #import {sig #[ Schnorr_ZKP.Schnorr.Sigma.RUN ] : schnorrMidInp → schnorrMidOut }
         as schnorr ;;
         '(_,u,e,z) ← schnorr (fto (h : gT), fto (FieldToWitness xi)) ;;
         ret (otf u : v_G, WitnessToField (otf e) : f_Z, WitnessToField (otf z) : f_Z)
       }
    ].
  Final Obligation.
    intros.
    ssprove_valid.
    destruct x as [xi h].
    ssprove_valid.
    destruct x as [[[? ?] ?] ?].
    ssprove_valid.
  Qed.

  Program Definition schnorr_ideal :
    package fset0
      [interface]
      [interface #val #[ SCHNORR ] : schnorrInput → schnorrOutput]
    :=
    [package
       #def #[ SCHNORR ] ('(xi, h) : schnorrInput) : schnorrOutput
       {
         c ← sample (uniform #|'Z_q|) ;;
         #assert Schnorr_ZKP.Schnorr.MyParam.R h (FieldToWitness xi) ;;
         z ← sample (uniform #|'Z_q|) ;;
         is_state (Build_t_SchnorrZKPCommit
                     (f_schnorr_zkp_u := ret_both ((g ^+ otf z * (h : gT) ^- otf c)%g))
                     (f_schnorr_zkp_c := ret_both (WitnessToField (otf c)))
                     (f_schnorr_zkp_z := ret_both (WitnessToField (otf z))))
       }
    ].
  Final Obligation.
    intros.
    ssprove_valid.
    destruct x as [xi h].
    ssprove_valid.
    1: apply valid_scheme ; rewrite <- fset0E ; apply (ChoiceEquality.is_valid_code (both_prog_valid _)).
  Qed.

  Program Definition schnorr_ideal_no_assert :
    package fset0
      [interface]
      [interface #val #[ SCHNORR ] : schnorrInput → schnorrOutput]
    :=
    [package
       #def #[ SCHNORR ] ('(xi, h) : schnorrInput) : schnorrOutput
       {
         c ← sample (uniform #|'Z_q|) ;;
         z ← sample (uniform #|'Z_q|) ;;
         is_state (Build_t_SchnorrZKPCommit
                     (f_schnorr_zkp_u := ret_both ((g ^+ otf z * (h : gT) ^- otf c)%g))
                     (f_schnorr_zkp_c := ret_both (WitnessToField (otf c)))
                     (f_schnorr_zkp_z := ret_both (WitnessToField (otf z))))
       }
    ].
  Final Obligation.
    intros.
    ssprove_valid.
    destruct x as [xi h].
    ssprove_valid.
    1: apply valid_scheme ; rewrite <- fset0E ; apply (ChoiceEquality.is_valid_code (both_prog_valid _)).
  Qed.

  Lemma schnorr_advantage :
    ∀ (LA : {fset Location}) (A : raw_package),
      ValidPackage LA [interface #val #[SCHNORR] : schnorrInput → schnorrOutput ] A_export A →
      LA :#: Schnorr_ZKP.Schnorr.MyAlg.Sigma_locs ->
      LA :#: Schnorr_ZKP.Schnorr.MyAlg.Simulator_locs ->
      (AdvantageE
        (schnorr_real)
        (schnorr_ideal) A = 0)%R.
  Proof.
    intros.
    split_advantage (pack schnorr_mid ∘ pack Schnorr_ZKP.hacspec_run).
    1:{
      apply: eq_rel_perf_ind_ignore.
      4: rewrite fset0U ; apply H0.
      3: apply fdisjoints0.
      1: apply fsubsetxx.

      unfold eq_up_to_inv.
      simplify_eq_rel inp_unit.
      destruct inp_unit as [xi h].
      simpl.

      repeat choice_type_eqP_handle.
      erewrite !cast_fun_K.
      fold chElement.

      eapply r_transR.
      1:{
        apply r_nice_swap_rule ; [ easy | easy | ].
        apply r_bind_assertD.
      }
      rewrite !otf_fto.
      apply r_assertD_same.
      intros.
      simpl.

      eapply r_uniform_bij with (f := _).
      1: instantiate (1 := fun x => x) ; now apply inv_bij.
      intros.

      rewrite bind_assoc.
      rewrite <- bind_ret at 1.
      rewrite !WitnessToFieldCancel.
      ssprove_same_head_generic.
      destruct a as [[? ?] ?].
      rewrite bind_rewrite.
      simpl.
      rewrite !otf_fto.
      rewrite !WitnessToFieldCancel.
      apply r_ret.
      easy.
    }
    split_advantage (pack schnorr_mid ∘ (pack Schnorr_ZKP.Schnorr.Sigma.RUN_interactive)).
    {
      unfold_advantageE.
      eapply Schnorr_ZKP.hacspec_vs_RUN_interactive.
      1:{
        solve_valid_package.
        apply H.
      }
      apply H0.
    }
    split_advantage (pack schnorr_mid ∘ (pack Schnorr_ZKP.Schnorr.Sigma.SHVZK_real_aux ∘ pack Schnorr_ZKP.Schnorr.Sigma.SHVZK_real)).
    {
      unfold_advantageE.
      eapply Schnorr_ZKP.Schnorr.Sigma.run_interactive_shvzk.
      3: apply H0.
      2:{
        solve_valid_package.
        apply H.
        Unshelve.
        all: try (apply fsubsetxx || solve_in_fset).
        refine fset0.
      }
      intros.
      unfold Schnorr_ZKP.Schnorr.MyAlg.choiceTranscript.
      refine ({code ret (chCanonical _)}).
    }
    split_advantage (pack schnorr_mid ∘ (pack Schnorr_ZKP.Schnorr.Sigma.SHVZK_real_aux ∘ pack Schnorr_ZKP.Schnorr.Sigma.SHVZK_ideal)).
    {
      unfold_advantageE.
      unfold_advantageE.

      eapply Schnorr_ZKP.Schnorr.schnorr_SHVZK with (LA := LA).
      2: apply H0.
      1:{
        solve_valid_package.
        apply H.
        Unshelve.
        all: try (apply fsubsetxx || solve_in_fset).
      }
    }
    {
      apply: eq_rel_perf_ind_ignore.
      3: rewrite !fset0U ; apply H1.
      3: apply fdisjoints0.
      1: apply fsubsetxx.

      unfold eq_up_to_inv.
      simplify_eq_rel inp_unit.
      destruct inp_unit as [xi h].
      simpl.

      repeat choice_type_eqP_handle.
      erewrite !cast_fun_K.
      fold chElement.

      simpl.

      eapply r_uniform_bij with (f := _).
      1: instantiate (1 := fun x => x) ; now apply inv_bij.
      intros.

      rewrite bind_assoc.
      eapply r_transL.
      1:{
        apply r_nice_swap_rule ; [ easy | easy | ].
        apply r_bind_assertD.
      }
      simpl.
      rewrite !otf_fto.

      apply r_assertD_same.
      intros.

      eapply r_uniform_bij with (f := _).
      1: instantiate (1 := fun x => x) ; now apply inv_bij.
      intros.

      rewrite otf_fto.
      now apply r_ret.
    }
  Qed.

  (** Commit *)

  Notation " 'chCommitInput' " :=
    (v_G)
    (in custom pack_type at level 2).

  Notation " 'chCommitOutput' " :=
    (f_Z)
    (in custom pack_type at level 2).

  Definition COMMIT : nat := 142.

  Program Definition commit_real :
    package fset0
      [interface]
      [interface
         #val #[ COMMIT ] : chCommitInput → chCommitOutput
      ]
    :=
    [package
        #def #[ COMMIT ] (vote_i : chCommitInput) : chCommitOutput
        {
          commit ← is_state (f_hash (t_Group := HOGaFE.GroupAndField.OVN.v_G_t_Group)
             (impl__into_vec
                (unsize
                   (box_new
                      (array_from_list [(ret_both vote_i)]))))) ;;
          ret (commit : v_Z)
        }
    ].
  Final Obligation.
    intros.
    ssprove_valid.
    1: apply valid_scheme ; rewrite <- fset0E ; apply (ChoiceEquality.is_valid_code (both_prog_valid _)).
  Qed.

  Program Definition commit_ideal :
    package fset0
      [interface]
      [interface
         #val #[ COMMIT ] : chCommitInput → chCommitOutput
      ]
    :=
    [package
        #def #[ COMMIT ] (_ : chCommitInput) : chCommitOutput
        {
          xi ← sample (uniform #|'Z_q|) ;; let xi := WitnessToField (otf xi) in
          ret (xi : v_Z)
        }
    ].
  Fail Final Obligation.

  (* hash_is_psudorandom / commit - game *)
  Definition Commit_game :
    loc_GamePair [interface
         #val #[ COMMIT ] : chCommitInput → chCommitOutput
      ] :=
    λ b,
      if b then {locpackage commit_real} else {locpackage commit_ideal}.

  (* (∀ D, DDH.ϵ_DDH D <= ϵ_DDH) *)
  Definition ϵ_COMMIT := Advantage Commit_game.


  (** GPowYiNotZero *)

  Notation " 'chGPowYiNotZeroInput' " :=
    ('unit)
    (in custom pack_type at level 2).

  Notation " 'chGPowYiNotZeroOutput' " :=
    (v_G)
    (in custom pack_type at level 2).

  Definition GPOWYINOTZERO : nat := 143.

  Local Obligation Tactic := idtac.

  Program Definition GPowYiNotZero_real i state :
    package fset0
      [interface]
      [interface
         #val #[ GPOWYINOTZERO ] : chGPowYiNotZeroInput → chGPowYiNotZeroOutput
      ]
    :=
    [package
        #def #[ GPOWYINOTZERO ] (_ : chGPowYiNotZeroInput) : chGPowYiNotZeroOutput
        {
          temp ← is_state (compute_g_pow_yi (ret_both (i : int32)) (f_g_pow_xis (ret_both state))) ;;
          ret (temp : v_G)
        }
    ].
  Final Obligation.
    intros.
    ssprove_valid.
    1: apply valid_scheme ; rewrite <- fset0E ; apply (ChoiceEquality.is_valid_code (both_prog_valid _)).
  Qed.

  Program Definition GPowYiNotZero_ideal (* i state *) :
    package fset0
      [interface]
      [interface
         #val #[ GPOWYINOTZERO ] : chGPowYiNotZeroInput → chGPowYiNotZeroOutput
      ]
    :=
    [package
        #def #[ GPOWYINOTZERO ] (_ : chGPowYiNotZeroInput) : chGPowYiNotZeroOutput
        {
          yi ← sample uniform #|'Z_q| ;;
          let yi := (WitnessToField (otf yi : 'Z_q) : v_Z) in
          ret (g ^+ (FieldToWitness yi))
          (* temp ← is_state (compute_g_pow_yi (ret_both (i : int32)) (f_g_pow_xis (ret_both state))) ;; *)
          (* #assert ((temp : gT) != g ^+ nat_of_ord (FieldToWitness (0%R))) ;; *)
          (* ret (temp : v_G) *)
        }
    ].
  (* Final Obligation. *)
  (*   intros. *)
  (*   ssprove_valid. *)
  (*   1: apply valid_scheme ; rewrite <- fset0E ; apply (ChoiceEquality.is_valid_code (both_prog_valid _)). *)
  (* Qed. *)
  Fail Next Obligation.

  (* GPowYiNotZero - game *)
  Definition GPowYiNotZero_game i state :
    loc_GamePair [interface
         #val #[ GPOWYINOTZERO ] : chGPowYiNotZeroInput → chGPowYiNotZeroOutput
      ] :=
    λ b,
      if b then {locpackage (GPowYiNotZero_real i state)} else {locpackage (GPowYiNotZero_ideal (* i state *))}.

  (* (∀ D, DDH.ϵ_DDH D <= ϵ_DDH) *)
  Definition ϵ_GPOWYINOTZERO i state := Advantage (GPowYiNotZero_game i state).

  (** CDS *)

  Notation " 'CDSoutput' " :=
    (t_OrZKPCommit)
    (in custom pack_type at level 2).
  (* (v_G × v_G × v_G × v_G × v_G × v_G × f_Z × f_Z × f_Z × f_Z × f_Z) *)

  Notation " 'CDSinput' " :=
    ((v_G × v_G × v_G) × (f_Z × 'bool))
    (in custom pack_type at level 2).

  Definition CDS : nat := 233.

  Program Definition cds_real :
    package fset0
      [interface]
      [interface #val #[ CDS ] : CDSinput → CDSoutput ]
    :=
    [package
       #def #[ CDS ] ('((x,h,y),(xi,vi)) : CDSinput) : CDSoutput
       {
         #assert OR_ZKP.proof_args.MyParam.R (x,h,y) (FieldToWitness xi, vi, h) ;;
          wr ← sample uniform #|'Z_q| ;;
          rr ← sample uniform #|'Z_q| ;;
          dr ← sample uniform #|'Z_q| ;;
          is_state (zkp_one_out_of_two
                      (ret_both (WitnessToField (otf wr : 'Z_q)))
                      (ret_both (WitnessToField (otf rr : 'Z_q)))
                      (ret_both (WitnessToField (otf dr : 'Z_q)))
                      (ret_both h)
                      (ret_both xi)
                      (ret_both (vi : 'bool)))
       }
    ].
  Final Obligation.
    intros.
    ssprove_valid.
    destruct x as [[[? ?] ?] [? ?]].
    ssprove_valid.
    1: apply valid_scheme ; rewrite <- fset0E ; apply (ChoiceEquality.is_valid_code (both_prog_valid _)).
  Qed.

  Program Definition cds_ideal :
    package fset0
      [interface]
      [interface #val #[ CDS ] : CDSinput → CDSoutput ]
    :=
    [package
       #def #[ CDS ] ('((x,h,y),(xi,vi)) : CDSinput) : CDSoutput
       {
         #assert OR_ZKP.proof_args.MyParam.R (x,h,y) (FieldToWitness xi, vi, h) ;;
         c ← sample uniform #|'Z_q| ;;

         d ← sample uniform #|'Z_q| ;;
         r ← sample uniform #|'Z_q| ;;
         r_other ← sample uniform #|'Z_q| ;;
         let d2 := otf d in
         let r2 := otf r in
         let r1 := otf r_other in
         let d1 := (otf c - d2)%R in
         let a1 := (g ^+ r1 * (x : gT) ^+ d1)%g in
         let b1 := ((h : gT) ^+ r1 * (y : gT) ^+ d1)%g in
         let a2 := (g ^+ r2 * (x : gT) ^+ d2)%g in
         let b2 := ((h : gT) ^+ r2 * ((y : gT) * invg g) ^+ d2)%g in

         ret ((x,y,
                a1,b1,a2,b2,
                WitnessToField (otf c),
                WitnessToField d1,WitnessToField d2,WitnessToField r1,WitnessToField r2)
             : t_OrZKPCommit)
       }
    ].
  Final Obligation.
    intros.
    ssprove_valid.
    destruct x as [[[? ?] ?] [? ?]].
    ssprove_valid.
  Qed.

  Program Definition cds_ideal_no_assert :
    package fset0
      [interface]
      [interface #val #[ CDS ] : CDSinput → CDSoutput ]
    :=
    [package
       #def #[ CDS ] ('((x,h,y),(xi,vi)) : CDSinput) : CDSoutput
       {
         c ← sample uniform #|'Z_q| ;;

         d ← sample uniform #|'Z_q| ;;
         r ← sample uniform #|'Z_q| ;;
         r_other ← sample uniform #|'Z_q| ;;
         let d2 := otf d in
         let r2 := otf r in
         let r1 := otf r_other in
         let d1 := (otf c - d2)%R in
         let a1 := (g ^+ r1 * (x : gT) ^+ d1)%g in
         let b1 := ((h : gT) ^+ r1 * (y : gT) ^+ d1)%g in
         let a2 := (g ^+ r2 * (x : gT) ^+ d2)%g in
         let b2 := ((h : gT) ^+ r2 * ((y : gT) * invg g) ^+ d2)%g in

         ret ((x,y,
                a1,b1,a2,b2,
                WitnessToField (otf c),
                WitnessToField d1,WitnessToField d2,WitnessToField r1,WitnessToField r2)
             : t_OrZKPCommit)
       }
    ].
  Final Obligation.
    intros.
    ssprove_valid.
    destruct x as [[[? ?] ?] [? ?]].
    ssprove_valid.
  Qed.

  Notation " 'CDSMidInp' " :=
    (OR_ZKP.proof_args.MyAlg.choiceStatement × OR_ZKP.proof_args.MyAlg.choiceWitness)
      (in custom pack_type at level 2).

  Notation " 'CDSMidOut' " :=
    (OR_ZKP.proof_args.MyAlg.choiceTranscript)
    (in custom pack_type at level 2).

  Program Definition cds_mid :
    package fset0
      [interface #val #[ OR_ZKP.proof_args.Sigma.RUN ] : CDSMidInp → CDSMidOut ]
      [interface #val #[ CDS ] : CDSinput → CDSoutput ]
    :=
    [package
       #def #[ CDS ] ('((x,h,y),(xi,vi)) : CDSinput) : CDSoutput
       {
         #import {sig #[ OR_ZKP.proof_args.Sigma.RUN ] : CDSMidInp → CDSMidOut }
         as cds ;;
         temp ← cds (fto (x : gT, h : gT, y : gT), fto (FieldToWitness xi, vi, h : gT)) ;;
         ret (OR_ZKP.or_sigma_ret_to_hacspec_ret temp)
       }
    ].
  Final Obligation.
    intros.
    ssprove_valid.
    destruct x as [[[? ?] ?] [? ?]].
    ssprove_valid.
  Qed.

  Lemma cds_advantage :
    ∀ (LA : {fset Location}) (A : raw_package),
      ValidPackage LA [interface #val #[CDS] : CDSinput → CDSoutput ] A_export A ->
      LA :#: OR_ZKP.proof_args.MyAlg.Sigma_locs ->
      LA :#: OR_ZKP.proof_args.MyAlg.Simulator_locs ->
      (AdvantageE
        (cds_real)
        (cds_ideal) A = 0)%R.
  Proof.
    intros.
    split_advantage (cds_mid ∘ OR_ZKP.hacspec_or_run).
    {
      apply: eq_rel_perf_ind_ignore.
      4: rewrite fset0U ; apply H0.
      3: apply fdisjoints0.
      1: apply fsubsetxx.

      unfold eq_up_to_inv.
      simplify_eq_rel inp_unit.

      destruct (inp_unit) as [[[x h] y] [xi vi]].
      intros.

      simpl.

      repeat choice_type_eqP_handle.
      erewrite !cast_fun_K.
      fold chElement.


      eapply r_transR.
      1:{
        apply r_nice_swap_rule ; [ easy | easy | ].
        apply r_bind_assertD.
      }
      simpl.
      rewrite !otf_fto.

      apply r_assertD_same.
      intros.

      ssprove_sync=> ?.
      ssprove_sync=> ?.
      ssprove_sync=> ?.
      rewrite bind_assoc.
      rewrite WitnessToFieldCancel.

      replace (_ == _) with vi.
      2:{
        simpl.

        unfold OR_ZKP.proof_args.MyParam.R in e.
        apply (ssrbool.elimT andP) in e ; destruct e.
        apply (ssrbool.elimT andP) in H2 ; destruct H2.

        apply (ssrbool.elimT eqP) in H2.
        apply (ssrbool.elimT eqP) in H3.
        apply (ssrbool.elimT eqP) in H4.
        subst.

        destruct vi.
        - rewrite eqxx.
          reflexivity.
        - rewrite expg0.
          symmetry.
          apply /eqP.
          red ; intros.
          apply prod_swap_iff in H2.
          rewrite mulg1 in H2.
          rewrite mulVg in H2.
          apply generator_is_not_one.
          apply both_equivalence_is_pure_eq.
          easy.
      }
      rewrite <- bind_ret at 1.

      simpl.

      set (zkp_one_out_of_two _ _ _ _ _ _).

      apply (somewhat_substitution b).
      apply (somewhat_substitutionR b).
      rewrite !bind_rewrite.
      apply r_ret.
      intros.
      split ; [ | easy ].
      subst b.

      setoid_rewrite OR_ZKP.ret_cancel.
      2:{
        unfold zkp_one_out_of_two at 1.
        unfold Build_t_OrZKPCommit at 1 2.
        repeat unfold let_both at 1.

        unfold OR_ZKP.proof_args.MyParam.R in e.
        apply (ssrbool.elimT andP) in e ; destruct e.
        apply (ssrbool.elimT andP) in H3 ; destruct H3.

        apply (ssrbool.elimT eqP) in H3.
        apply (ssrbool.elimT eqP) in H4.
        apply (ssrbool.elimT eqP) in H5.
        subst.

        simpl.
        destruct vi.
        + simpl.
          rewrite <- conversion_is_true.
          reflexivity.
        + simpl.
          rewrite <- conversion_is_true.
          reflexivity.
      }
      2:{
        unfold zkp_one_out_of_two at 1.
        unfold Build_t_OrZKPCommit at 1 2.
        repeat unfold let_both at 1.

        unfold OR_ZKP.proof_args.MyParam.R in e.
        apply (ssrbool.elimT andP) in e ; destruct e.
        apply (ssrbool.elimT andP) in H3 ; destruct H3.

        apply (ssrbool.elimT eqP) in H3.
        apply (ssrbool.elimT eqP) in H4.
        apply (ssrbool.elimT eqP) in H5.
        subst.

        simpl.
        destruct vi.
        + simpl.
          rewrite pow_witness_to_field.
          rewrite WitnessToFieldCancel.
          rewrite expg1.
          Misc.push_down_sides.
          reflexivity.
        + simpl.
          rewrite pow_witness_to_field.
          rewrite WitnessToFieldCancel.
          rewrite expg0. rewrite mulg1.
          Misc.push_down_sides.
          reflexivity.
      }
      reflexivity.
    }

    split_advantage (cds_mid ∘ (OR_ZKP.proof_args.Sigma.SHVZK_real_aux ∘ OR_ZKP.proof_args.Sigma.SHVZK_real)).
    {
      unfold_advantageE.
      eapply OR_ZKP.run_interactive_or_shvzk.
      1: unshelve solve_valid_package.
      4: apply H.
      3: apply H0.
      1,2: solve_in_fset.
    }

    split_advantage (cds_mid ∘ (OR_ZKP.proof_args.Sigma.SHVZK_real_aux ∘ OR_ZKP.proof_args.Sigma.SHVZK_ideal)).
    {
      unfold_advantageE.
      unfold_advantageE.
      apply OR_ZKP.shvzk_success with (LA := LA).
      2: apply H0.
      solve_valid_package.
      apply H.

      Unshelve.
      all: revgoals.
      all: try (apply fsubsetxx || solve_in_fset).
    }

    {
      apply: eq_rel_perf_ind_ignore.
      3: rewrite !fset0U ; apply H1.
      3: apply fdisjoints0.
      1: apply fsubsetxx.

      unfold eq_up_to_inv.
      simplify_eq_rel inp_unit.

      destruct (inp_unit) as [[[x h] y] [xi vi]].
      intros.

      simpl.

      repeat choice_type_eqP_handle.
      erewrite !cast_fun_K.
      fold chElement.

      simpl.

      set (OR_ZKP.proof_args.MyParam.R _ _).
      eapply r_transL with (c₀ := #assert b ;; _).
      1:{
        apply r_nice_swap_rule ; [ easy | easy | ].
        destruct b.
        + simpl.
          apply rreflexivity_rule.
        + eapply r_const_sample_L ; [ apply LosslessOp_uniform | intros ].
          rewrite bind_assoc.
          apply r_bind_assertD.
      }
      subst b.
      rewrite !otf_fto.

      apply r_assertD_same.
      intros.

      ssprove_sync=> ?.
      setoid_rewrite bind_rewrite.
      unfold OR_ZKP.or_sigma_ret_to_hacspec_ret.
      rewrite !otf_fto.
      setoid_rewrite otf_fto.
      setoid_rewrite otf_fto.

      ssprove_sync=> d.
      ssprove_sync=> r_other.
      ssprove_sync=> r.
      now apply r_ret.
    }
  Qed. (* Fail Timeout 5 Qed. Admitted. (* 216.817 secs *) *)

  (** DL_ *)

  Theorem N_lt_succ_l : forall {a b},
      (a.+1 < b)%N -> (a < b)%N.
  Proof. easy. Qed.

  Fixpoint inv_helper (i : nat) `{H : (i < (Zp_trunc q).+2)%N} (h : gT) : Datatypes.option 'Z_q :=
    let oi : 'Z_q := Ordinal (m := i) (n := (S (S (Zp_trunc q)))) H in
    if g ^+ oi == h
    then Some oi
    else
      match i as k return (k < (Zp_trunc q).+2)%N -> Datatypes.option 'Z_q with
      | 0%nat => fun _ => None
      | S n => fun H' => inv_helper n (H := N_lt_succ_l H') h
      end H.

  Lemma always_find_smaller_power :
    forall (i x : nat) H H0, (x <= i)%N -> inv_helper i (H := H) (g ^+ x) = Some (Ordinal (m := x) (n := (S (S (Zp_trunc q)))) H0).
  Proof.
    clear ; intros.
    induction i.
    {
      destruct x ; [ | easy ].
      simpl.
      rewrite eqxx.
      f_equal.
      apply ord_ext.
      reflexivity.
    }
    {
      simpl.
      rewrite eq_expg_mod_order.

      destruct (i.+1 == x) eqn:x_is_Si.
      {
        apply (ssrbool.elimT eqP) in x_is_Si.
        subst.
        rewrite eqxx.
        f_equal.
        apply ord_ext.
        reflexivity.
      }
      {
        rewrite !modn_small.
        3:{
          simpl.
          rewrite order_ge1 in H.
          apply H.
        }
        2:{
          rewrite order_ge1 in H.
          eapply leq_ltn_trans ; [ apply H0 | ].
          rewrite order_ge1.
          easy.
        }

        rewrite x_is_Si.

        apply IHi.
        easy.
      }
    }
  Qed.

  Lemma q_sub_1_lt_q : is_true (q.-1 < (Zp_trunc q).+2)%N.
  Proof. unfold Zp_trunc. easy. Qed.

  Lemma Zq_lt_q : forall x : 'Z_q, is_true (x < (Zp_trunc q).+2)%N.
  Proof. unfold Zp_trunc. easy. Qed.

  Corollary always_find_smaller_power_q : forall (x : nat) H0,
      inv_helper q.-1 (H := q_sub_1_lt_q) (g ^+ x) =
        Some (Ordinal (m := x) (n := (S (S (Zp_trunc q)))) H0).
  Proof.
    intros.
    apply always_find_smaller_power.
    rewrite order_ge1 in H0. easy.
  Qed.

  Lemma inv_helper_is_not_none : forall h, inv_helper (H := q_sub_1_lt_q) q.-1 h <> None.
  Proof.
    intros.
    red ; intros.
    destruct (cyclic_group_to_exponent h) as [? []] ; subst.
    apply isSome_none in H.
    unshelve erewrite always_find_smaller_power_q in H.
    - rewrite order_ge1. unfold q. easy.
    - easy.
  Defined.

  (* inv_helper_is_not_none h v eqrefl *)
  Definition inv (h : gT) : 'Z_q.
  Proof.
    intros.
    epose proof (inv_helper_is_not_none h).
    destruct (inv_helper _ _) in H.
    {
      apply o.
    }
    {
      contradiction.
    }
  Defined.

  Theorem inv_is_exponent : forall (x : 'Z_q), inv (g ^+ x) = x.
  Proof.
    intros.
    unfold inv.
    unshelve epose proof (always_find_smaller_power_q x (Zq_lt_q x)).
    set (inv_helper_is_not_none (g ^+ x)).
    set (inv_helper _ _) in *.

    generalize dependent n0.
    intros.

    destruct o eqn:no.
    2: contradiction.
    subst o.
    inversion H.
    subst.
    destruct x.
    apply ord_ext.
    reflexivity.
  Qed.

  Theorem inv_is_inv : forall h, g ^+ inv h = h.
  Proof.
    intros.
    destruct (cyclic_group_to_exponent h) as [? []] ; subst.
    unshelve epose proof (inv_is_exponent (Ordinal (m := x) (n := (S (S (Zp_trunc q)))) _)).
    {
      rewrite order_ge1. unfold q. easy.
    }
    rewrite H.
    reflexivity.
  Qed.

  Notation " 'chSingleProtocolTranscript' " :=
    ((t_SchnorrZKPCommit × v_G) × (v_Z) × (t_OrZKPCommit × v_G))
    (in custom pack_type at level 2).

  Definition FULL_PROTOCOL_INTERFACE : nat := 102.
  Definition SECOND_STEP : nat := 103.

  Program Definition full_protocol_interface (state : t_OvnContractState) (i : nat) (vi : 'bool) :
    package (fset [DL_loc])
      [interface
         #val #[ DL ] : 'unit → chDLOutput
       ; #val #[ DL_GUESS ] : chDLInput → 'bool
       ; #val #[ SCHNORR ] : schnorrInput → schnorrOutput
       ; #val #[ GPOWYINOTZERO ] : chGPowYiNotZeroInput → chGPowYiNotZeroOutput
       ; #val #[ COMMIT ] : chCommitInput → chCommitOutput
       ; #val #[ CDS ] : CDSinput → CDSoutput
      ]
      [interface
         #val #[ FULL_PROTOCOL_INTERFACE ] : 'unit → chSingleProtocolTranscript
      ] :=
    {package [fmap (FULL_PROTOCOL_INTERFACE, ('unit; (((t_SchnorrZKPCommit × v_G) × (v_Z) × (t_OrZKPCommit × v_G)) ; fun (_ : 'unit) => _)))]}.
  Next Obligation.
    intros.
    refine (
          #import {sig #[ DL ] : 'unit → chDLOutput }
          as dl ;;
          #import {sig #[ SCHNORR ] : schnorrInput → schnorrOutput }
          as schnorr ;;
          #import {sig #[ GPOWYINOTZERO ] : chGPowYiNotZeroInput → chGPowYiNotZeroOutput }
          as g_pow_yi_nz ;;
          #import {sig #[ COMMIT ] : chCommitInput → chCommitOutput }
          as commit_to ;;
          #import {sig #[ CDS ] : CDSinput → CDSoutput }
          as CDS ;;
          g_pow_xi ← dl Datatypes.tt ;;
          xi ← get_option DL_loc erefl ;;
          zkp_i ← schnorr (xi, g_pow_xi) ;;
          g_pow_yi ← g_pow_yi_nz Datatypes.tt ;;
          (* g_pow_xy ← ddh _ ;; *)
          g_pow_xy ← @ret v_G ((g_pow_yi : gT) ^+ (FieldToWitness xi)) ;;

          (* (WitnessToField (FieldToWitness xi * (inv g_pow_yi)))%R *)
          vote_i ← ret ((g_pow_xy : gT) * (g^+(if vi then 1 else 0)%R : v_G))%g ;;
          commit ← commit_to vote_i ;;
          cds_i ← CDS ((g_pow_xi, g_pow_yi, vote_i), (xi, vi)) ;;
          ret (((zkp_i, g_pow_xi, commit : f_Z, (cds_i : t_OrZKPCommit, vote_i))) : (((t_SchnorrZKPCommit × v_G) × v_Z) × (t_OrZKPCommit × v_G))%pack)
      ).
  Defined.
  Final Obligation.
    intros.
    unfold full_protocol_interface_obligation_1.
    fold chElement.
    eapply (valid_package_cons _ _ _ _ _ _ [] []).
    - apply valid_empty_package.
    - intros.
      ssprove_valid.
      eapply valid_injectMap.
      2: apply prog_valid.
      + solve_in_fset.
    - try (rewrite <- fset0E ; setoid_rewrite @imfset0 ; rewrite in_fset0 ; reflexivity).
  Qed.
  Fail Next Obligation.

  Program Definition full_protocol_interface_step1 (state : t_OvnContractState) (i : nat) (vi : 'bool) :
    package (fset [DL_loc])
      [interface
         #val #[ DL ] : 'unit → chDLOutput
       ; #val #[ SCHNORR ] : schnorrInput → schnorrOutput
       ; #val #[ GPOWYINOTZERO ] : chGPowYiNotZeroInput → chGPowYiNotZeroOutput
       ; #val #[ COMMIT ] : chCommitInput → chCommitOutput
       ; #val #[ CDS ] : CDSinput → CDSoutput
      ]
      [interface
         #val #[ FULL_PROTOCOL_INTERFACE ] : 'unit → chSingleProtocolTranscript
      ] := {package [fmap (FULL_PROTOCOL_INTERFACE, ('unit; (((t_SchnorrZKPCommit × v_G) × (v_Z) × (t_OrZKPCommit × v_G)) ; fun (_ : 'unit) => _)))]}.
  Next Obligation.
    intros.
    refine (
          #import {sig #[ DL ] : 'unit → chDLOutput }
          as dl ;;
          #import {sig #[ SCHNORR ] : schnorrInput → schnorrOutput }
          as schnorr ;;
          #import {sig #[ GPOWYINOTZERO ] : chGPowYiNotZeroInput → chGPowYiNotZeroOutput }
          as g_pow_yi_nz ;;
          #import {sig #[ COMMIT ] : chCommitInput → chCommitOutput }
          as commit_to ;;
          #import {sig #[ CDS ] : CDSinput → CDSoutput }
          as CDS ;;
          g_pow_xi ← dl Datatypes.tt ;;
          xi ← get_option DL_loc erefl ;;
          zkp_i ← schnorr (xi, g_pow_xi) ;;
          g_pow_yi ← g_pow_yi_nz Datatypes.tt ;;
          g_pow_xy ← @ret v_G ((g_pow_yi : gT) ^+ (FieldToWitness xi)) ;;
          (* g_pow_xy ← dl (WitnessToField (FieldToWitness xi * (inv g_pow_yi)))%R ;; *)
          vote_i ← ret ((g_pow_xy : gT) * g^+(if vi then 1 else 0)%R)%g ;;
          commit ← commit_to vote_i ;;
          cds_i ← CDS ((g_pow_xi, g_pow_yi, vote_i), (xi, vi)) ;;
          ret (((zkp_i, g_pow_xi, commit, (cds_i : t_OrZKPCommit, vote_i))) : (((t_SchnorrZKPCommit × v_G) × v_Z) × (t_OrZKPCommit × v_G))%pack)
      ).
  Defined.
  Final Obligation.
    intros.
    unfold full_protocol_interface_step1_obligation_1.
    fold chElement.
    eapply (valid_package_cons _ _ _ _ _ _ [] []).
    - apply valid_empty_package.
    - intros.
      ssprove_valid.
      eapply valid_injectMap.
      2: apply prog_valid.
      + solve_in_fset.
    - try (rewrite <- fset0E ; setoid_rewrite @imfset0 ; rewrite in_fset0 ; reflexivity).
  Qed.

  Program Definition full_protocol_interface_step2 (state : t_OvnContractState) (i : nat) (vi : 'bool) :
    package (fset [DL_loc])
      [interface
         #val #[ DL ] : 'unit → chDLOutput
       ; #val #[ SCHNORR ] : schnorrInput → schnorrOutput
       ; #val #[ GPOWYINOTZERO ] : chGPowYiNotZeroInput → chGPowYiNotZeroOutput
       ; #val #[ COMMIT ] : chCommitInput → chCommitOutput
       ; #val #[ CDS ] : CDSinput → CDSoutput
      ]
      [interface
         #val #[ FULL_PROTOCOL_INTERFACE ] : 'unit → chSingleProtocolTranscript
      ] :=
    {package [fmap (FULL_PROTOCOL_INTERFACE, ('unit; (((t_SchnorrZKPCommit × v_G) × (v_Z) × (t_OrZKPCommit × v_G)) ; fun (_ : 'unit) => _)))]}.
  Next Obligation.
    intros.
    refine (
          #import {sig #[ DL ] : 'unit → chDLOutput }
          as dl ;;
          #import {sig #[ SCHNORR ] : schnorrInput → schnorrOutput }
          as schnorr ;;
          #import {sig #[ GPOWYINOTZERO ] : chGPowYiNotZeroInput → chGPowYiNotZeroOutput }
          as g_pow_yi_nz ;;
          #import {sig #[ COMMIT ] : chCommitInput → chCommitOutput }
          as commit_to ;;
          #import {sig #[ CDS ] : CDSinput → CDSoutput }
          as CDS ;;
          g_pow_xi ← dl Datatypes.tt ;;
          xi ← get_option DL_loc erefl ;;
          zkp_i ← schnorr (xi, g_pow_xi) ;;
          g_pow_yi ← g_pow_yi_nz Datatypes.tt ;;
          g_pow_xy ← @ret v_G ((g_pow_yi : gT) ^+ (FieldToWitness xi)) ;;
          (* g_pow_xy ← dl (WitnessToField (FieldToWitness (xi) * (inv g_pow_yi)))%R ;; *)
          vote_i ← ret ((g_pow_xy : gT) * g^+(if vi then 1 else 0)%R)%g ;;
          commit ← commit_to vote_i ;;
          cds_i ← CDS ((g_pow_xi, g_pow_yi, vote_i), (xi, vi)) ;;
          ret (((zkp_i, g_pow_xi, commit, (cds_i : t_OrZKPCommit, vote_i))) : (((t_SchnorrZKPCommit × v_G) × v_Z) × (t_OrZKPCommit × v_G))%pack)).
  Defined.
  Final Obligation.
    intros.
    unfold full_protocol_interface_step2_obligation_1.
    eapply (valid_package_cons _ _ _ _ _ _ [] []).
    - apply valid_empty_package.
    - intros.
      ssprove_valid.
      eapply valid_injectMap.
      2: apply prog_valid.
      + solve_in_fset.
    - try (rewrite <- fset0E ; setoid_rewrite @imfset0 ; rewrite in_fset0 ; reflexivity).
  Qed.

  Program Definition full_protocol_interface_step3 (state : t_OvnContractState) (i : nat) (vi : 'bool) :
    package (fset [DDH_loc1])
      [interface
         #val #[ DL ] : 'unit → chDLOutput
       ; #val #[ DDH ] : 'unit → chDDHOutput
       ; #val #[ SCHNORR ] : schnorrInput → schnorrOutput
       ; #val #[ GPOWYINOTZERO ] : chGPowYiNotZeroInput → chGPowYiNotZeroOutput
       ; #val #[ COMMIT ] : chCommitInput → chCommitOutput
       ; #val #[ CDS ] : CDSinput → CDSoutput
      ]
      [interface
         #val #[ FULL_PROTOCOL_INTERFACE ] : 'unit → chSingleProtocolTranscript
      ] :=
    {package [fmap (FULL_PROTOCOL_INTERFACE, ('unit; (((t_SchnorrZKPCommit × v_G) × (v_Z) × (t_OrZKPCommit × v_G)) ; fun (_ : 'unit) => _)))]}.
  Next Obligation.
    intros.
    refine (
          #import {sig #[ DL ] : 'unit → chDLOutput }
          as dl ;;
          #import {sig #[ DDH ] : 'unit → chDDHOutput }
          as ddh ;;
          #import {sig #[ SCHNORR ] : schnorrInput → schnorrOutput }
          as schnorr ;;
          #import {sig #[ GPOWYINOTZERO ] : chGPowYiNotZeroInput → chGPowYiNotZeroOutput }
          as g_pow_yi_nz ;;
          #import {sig #[ COMMIT ] : chCommitInput → chCommitOutput }
          as commit_to ;;
          #import {sig #[ CDS ] : CDSinput → CDSoutput }
          as CDS ;;
          (* g_pow_xi ← dl Datatypes.tt ;; *)
          '(g_pow_xi, g_pow_yi, g_pow_xy) ← ddh Datatypes.tt ;;
          zkp_i ← schnorr (WitnessToField (inv g_pow_xi), g_pow_xi) ;;
          (* g_pow_yi ← g_pow_yi_nz Datatypes.tt ;; *)
          (* vote_i ← ret (g^+(if vi then 1 else 0)%R)%g ;; *)
          xi ← get_option DDH_loc1 erefl ;;
          (* xi ← sample uniform #|'Z_q| ;; *)
          (* let xi := (WitnessToField (otf xi : 'Z_q) : v_Z) in *)
          (* g_pow_xy ← dl (WitnessToField (FieldToWitness (xi) * (inv g_pow_yi)))%R ;; *)
          (* g_pow_xy ← @ret v_G ((g_pow_yi : gT) ^+ (FieldToWitness xi)) ;; *)
          vote_i ← ret ((g_pow_xy : gT) * g^+(if vi then 1 else 0)%R)%g ;;
          commit ← commit_to vote_i ;;
          cds_i ← CDS ((g_pow_xi, g_pow_yi, vote_i), (xi, vi)) ;;
          ret (((zkp_i, g_pow_xi, commit, (cds_i : t_OrZKPCommit, vote_i))) : (((t_SchnorrZKPCommit × v_G) × v_Z) × (t_OrZKPCommit × v_G))%pack)).
  Defined.
  Final Obligation.
    intros.
    unfold full_protocol_interface_step3_obligation_1.
    eapply (valid_package_cons _ _ _ _ _ _ [] []).
    - apply valid_empty_package.
    - intros.
      ssprove_valid.
      eapply valid_injectMap.
      2: apply prog_valid.
      + solve_in_fset.
    - try (rewrite <- fset0E ; setoid_rewrite @imfset0 ; rewrite in_fset0 ; reflexivity).
  Qed.

  Program Definition full_protocol_interface_step4 (state : t_OvnContractState) (i : nat) (vi : 'bool) :
    package (fset [DDH_loc1; DDH_loc2])
      [interface
         #val #[ DL ] : 'unit → chDLOutput
       ; #val #[ DDH ] : 'unit → chDDHOutput
       ; #val #[ SCHNORR ] : schnorrInput → schnorrOutput
       ; #val #[ COMMIT ] : chCommitInput → chCommitOutput
       ; #val #[ GPOWYINOTZERO ] : chGPowYiNotZeroInput → chGPowYiNotZeroOutput
       ; #val #[ CDS ] : CDSinput → CDSoutput
      ]
      [interface
         #val #[ FULL_PROTOCOL_INTERFACE ] : 'unit → chSingleProtocolTranscript
      ] :=
    {package [fmap (FULL_PROTOCOL_INTERFACE, ('unit; (((t_SchnorrZKPCommit × v_G) × (v_Z) × (t_OrZKPCommit × v_G)) ; fun (_ : 'unit) => _)))]}.
  Next Obligation.
    intros.
    refine (
        #import {sig #[ DL ] : 'unit → chDLOutput }
        as dl ;;
        #import {sig #[ DDH ] : 'unit → chDDHOutput }
        as ddh ;;
          #import {sig #[ SCHNORR ] : schnorrInput → schnorrOutput }
          as schnorr ;;
          #import {sig #[ GPOWYINOTZERO ] : chGPowYiNotZeroInput → chGPowYiNotZeroOutput }
          as g_pow_yi_nz ;;
          #import {sig #[ COMMIT ] : chCommitInput → chCommitOutput }
          as commit_to ;;
          #import {sig #[ CDS ] : CDSinput → CDSoutput }
          as CDS ;;
          '(g_pow_xi, g_pow_yi, g_pow_xy) ← ddh Datatypes.tt ;;
          zkp_i ← schnorr (WitnessToField (inv g_pow_xi), g_pow_xi) ;;
          (* g_pow_yi ← g_pow_yi_nz Datatypes.tt ;; *)
          (* let g_pow_yi : v_G := g_pow_yi in *)
          (* let g_pow_xy : v_G := g_pow_xy in *)
          xi ← get_option DDH_loc1 erefl ;;
          (* xyi ← sample uniform #|'Z_q| ;; *)
          (* let xyi := (WitnessToField (otf xyi : 'Z_q) : v_Z) in *)
          (* g_pow_xy ← @ret v_G ((g : gT) ^+ (FieldToWitness xyi)) ;; *)
          vote_i ← ret ((g_pow_xy : gT) * g^+(if vi then 1 else 0)%R)%g ;;
          commit ← commit_to vote_i ;;
          cds_i ← CDS ((g_pow_xi, g_pow_yi, vote_i), (xi, vi)) ;;
          ret (((zkp_i, g_pow_xi, commit, (cds_i : t_OrZKPCommit, vote_i))) : (((t_SchnorrZKPCommit × v_G) × v_Z) × (t_OrZKPCommit × v_G))%pack)).
  Defined.
  Final Obligation.
    intros.
    unfold full_protocol_interface_step4_obligation_1.
    eapply (valid_package_cons _ _ _ _ _ _ [] []).
    - apply valid_empty_package.
    - intros.
      ssprove_valid.
      eapply valid_injectLocations.
      2:{
        eapply valid_injectMap.
        2: apply prog_valid.
        + solve_in_fset.
      }
       + solve_in_fset.
    - try (rewrite <- fset0E ; setoid_rewrite @imfset0 ; rewrite in_fset0 ; reflexivity).
  Qed.
  Fail Next Obligation.

  (** All steps *)

  Program Definition full_protocol_intantiated (state : t_OvnContractState) (i : nat) (vi : 'bool) : package (fset [DL_loc]) [interface]
      [interface
         #val #[ FULL_PROTOCOL_INTERFACE ] : 'unit → chSingleProtocolTranscript
      ] :=
    {package (full_protocol_interface state i vi ∘ par (DL_game false) (par schnorr_real (par (par (GPowYiNotZero_real i state) commit_real) cds_real)))}.
  Final Obligation.
  intros.
  (* set (DL_game false). *)
  (*   trimmed_package (DL_game false). *)
    (* trimmed_package (dl_ideal). *)
  (* trimmed_package (dl_random). *)
  assert (trimmed [interface #val #[DL] : 'unit → chDLOutput ; #val #[DL_GUESS] : chDLInput → 'bool ] (DL_game false)).
  1:{
    unfold trimmed.
    unfold trim.
    rewrite filterm_set.
    simpl ; fold chElement.

    rewrite in_fset.
    rewrite mem_head.
    simpl.

    setoid_rewrite filterm_set ; simpl ; fold chElement.
    rewrite in_fset.
    rewrite in_cons.
    rewrite mem_head.
    rewrite Bool.orb_true_r.

    rewrite filterm0.
    reflexivity.
  }

    trimmed_package (schnorr_real).
    trimmed_package (schnorr_ideal).
    trimmed_package (schnorr_ideal_no_assert).

    trimmed_package (GPowYiNotZero_real i state).
    trimmed_package (GPowYiNotZero_ideal (* i state *)).

    trimmed_package (commit_real).
    trimmed_package (commit_ideal).

    trimmed_package (cds_real).
    trimmed_package (cds_ideal).
    trimmed_package (cds_ideal_no_assert).

    unshelve solve_valid_package.
    all: revgoals.
    all: try (apply fsubsetxx).
    all: try rewrite <- fset0E.
    all: try rewrite !fset0U.
    all: try rewrite !fsetU0.

    all: try rewrite <- fset1E.
    all: unfold idents.
    all: try rewrite imfset1.
    all: try rewrite fdisjoints1.
    all: try rewrite (fset_cons).
    all: try rewrite fset1E.
    all: try rewrite imfsetU.
    all: try rewrite <- !fset1E.
    all: try rewrite !imfset1.
    all: try now rewrite notin_fset.
    (* 1: rewrite <- !fset_cat ; simpl. *)
    all: try rewrite !fset1E.
    all: try rewrite <- !fset_cat.
    all: simpl.
    all: unfold Game_import ; try rewrite <- fset0E.
    all: apply fsubsetxx.
  Qed.

  (* Theorem valid_link_inv : *)
  (*   forall L I E1 E2 p1 p2, *)
  (*     trimmed E1 p1 -> *)
  (*     trimmed E2 p2 -> *)
  (*     ValidPackage L I (E1 :|: E2) (p1 ∘ p2) -> *)
  (*     ValidPackage L I E1 p1 /\ ValidPackage L I E2 p2. *)
  (* Proof. *)
  (*   intros. *)

  Ltac solve_flat :=
    clear ;
    unfold flat ;

    intros n u1 u2 ;
    try rewrite !in_fsetU ;

    let H := fresh in
    let H0 := fresh in
    intros H H0 ;

    rewrite <- !fset1E in H, H0 ;
    rewrite !in_fset1 in H, H0 ;

    repeat (apply (ssrbool.elimT ssrbool.orP) in H ; destruct H) ; apply (ssrbool.elimT eqP) in H ; inversion H ; subst ;

    repeat (apply (ssrbool.elimT ssrbool.orP) in H0 ; destruct H0) ; apply (ssrbool.elimT eqP) in H0 ; now inversion H0 ; subst.

  Lemma advantage_reflexivity :
    forall P A, AdvantageE P P A = 0%R.
  Proof.
    unfold AdvantageE.
    intros.
    rewrite subrr.
    rewrite Num.Theory.normr0.
    reflexivity.
  Qed.

  Ltac simpl_idents :=
    unfold idents
    ; rewrite !fset_cons
    ; try rewrite <- !(fset_cons _ [::])
    ; rewrite <- !fset1E
    ; rewrite !imfsetU
    ; rewrite !imfset1
    ; rewrite !fset1E
    ; rewrite <- !fset_cat
    ; simpl.

  Ltac solve_idents :=
    rewrite fset_cons
    ; rewrite fdisjointUl
    ; rewrite <- !fset1E
    ; rewrite !fdisjoint1s
    ; try rewrite !fset1E
    ; rewrite !in_fset
    ; easy.

  Lemma Advantage_par_emptyR :
    ∀ G₀ G₁ A,
      AdvantageE (par G₀ emptym) (par G₁ emptym) A = AdvantageE G₀ G₁ A.
  Proof.
    intros G₀ G₁ A.
    unfold AdvantageE.
    unfold par.
    rewrite !unionm0.
    reflexivity.
  Qed.

  Lemma Advantage_parR :
    ∀ G₀ G₁ G₁' A L₀ L₁ L₁' E₀ E₁,
      ValidPackage L₀ Game_import E₀ G₀ →
      ValidPackage L₁ Game_import E₁ G₁ →
      ValidPackage L₁' Game_import E₁ G₁' →
      flat E₁ →
      trimmed E₀ G₀ →
      trimmed E₁ G₁ →
      trimmed E₁ G₁' →
      AdvantageE (par G₁ G₀) (par G₁' G₀) A =
        AdvantageE G₁ G₁' (A ∘ par (ID E₁) G₀).
  Proof.
    intros G₀ G₁ G₁' A L₀ L₁ L₁' E₀ E₁.
    intros Va0 Va1 Va1' Fe0 Te0 Te1 Te1'.
    replace (par G₁ G₀) with ((par (ID E₁) G₀) ∘ (par G₁ (ID Game_import) )).
    2:{
      erewrite <- interchange.
      all: ssprove_valid.
      4:{
        ssprove_valid.
        rewrite domm_ID_fset.
        rewrite -fset0E.
        apply fdisjoints0.
      }
      2:{ unfold Game_import. rewrite -fset0E. discriminate. }
      2: apply trimmed_ID.
      rewrite link_id.
      2:{ unfold Game_import. rewrite -fset0E. discriminate. }
      2: assumption.
      rewrite id_link.
      2: assumption.
      reflexivity.
    }
    replace (par G₁' G₀) with ((par (ID E₁) G₀) ∘ (par G₁' (ID Game_import))).
    2:{
      erewrite <- interchange.
      all: ssprove_valid.
      4:{
        ssprove_valid.
        rewrite domm_ID_fset.
        rewrite -fset0E.
        apply fdisjoints0.
      }
      2:{ unfold Game_import. rewrite -fset0E. discriminate. }
      2: apply trimmed_ID.
      rewrite link_id.
      2:{ unfold Game_import. rewrite -fset0E. discriminate. }
      2: assumption.
      rewrite id_link.
      2: assumption.
      reflexivity.
    }
    rewrite -Advantage_link.
    unfold Game_import. rewrite -fset0E.
    rewrite Advantage_par_emptyR.
    reflexivity.
    Unshelve. all: auto.
  Qed.

  (* Lemma compute_g_pow_yi_is_rand i state : *)
  (*   forall (ν : _), *)
  (*     (forall P, ϵ_GPOWYINOTZERO i state P <= ν)%R → *)
  (*   ⊢ ⦃ λ '(s₀, s₁), s₀ = s₁ ⦄ *)
  (*       yi ← sample uniform #|'Z_q| ;; *)
  (*       let yi := (WitnessToField (otf yi : 'Z_q) : v_Z) in *)
  (*       ret (g ^+ (FieldToWitness yi)) ≈ *)
  (*       x ← is_state (compute_g_pow_yi (ret_both i) (f_g_pow_xis (ret_both state))) ;; *)
  (*       ret (x : gT) *)
  (*         ⦃ Logic.eq ⦄. *)
  (* Proof. *)
  (*   (* intros. *) *)
  (*   (* epose (ϵ_GPOWYINOTZERO i state). *) *)
  (*   (* unfold ϵ_GPOWYINOTZERO in s. *) *)

  (*   (* unfold GPowYiNotZero_game in s. *) *)
    
  (* Admitted. *)

  Lemma protocol_dl_real_to_ideal :
    forall state (i : nat) vi,
    ∀ (LA : {fset Location}) (A : raw_package),
      ValidPackage LA [interface #val #[ FULL_PROTOCOL_INTERFACE ] : 'unit → chSingleProtocolTranscript ] A_export A →
      LA :#: Schnorr_ZKP.Schnorr.MyAlg.Sigma_locs ->
      LA :#: Schnorr_ZKP.Schnorr.MyAlg.Simulator_locs ->
      LA :#: OR_ZKP.proof_args.MyAlg.Sigma_locs ->
      LA :#: OR_ZKP.proof_args.MyAlg.Simulator_locs ->
      LA :#: fset [:: DL_loc] ->
      LA :#: fset [:: DDH_loc1; DDH_loc2] ->
      forall (ϵ : _),
      (forall P, ϵ_DL P <= ϵ)%R →
      forall (ψ : _),
      (forall P, ϵ_COMMIT P <= ψ)%R ->
      forall (ν : _),
      (forall P, ϵ_GPOWYINOTZERO i state P <= ν)%R →
      forall (ζ : _),
      (forall P, ϵ_DDH P <= ζ)%R →
      (AdvantageE
           (full_protocol_interface state i vi ∘ par (DL_game false) (par schnorr_real (par (par (GPowYiNotZero_real i state) commit_real) cds_real)))
           (full_protocol_interface_step4 state i vi ∘ (par (DL_game true) (par (DDH_game true) (par schnorr_ideal_no_assert (par (par (GPowYiNotZero_ideal (* i state *)) commit_ideal) cds_ideal_no_assert)))))
           A <= ((ψ + ν) + (ϵ + ζ))%R)%R.
  Proof.
    intros ? ? ? ? ? ? H_LA_Schnorr_Sigma H_LA_Schnorr_Simulator H_LA_Or_Sigma H_LA_Or_Simulator H_LA_Or_DL_loc H_LA_Or_DDH_loc ? ? ? ? ? ? ζ H_DDH.

    assert (trimmed_DL : forall b, trimmed [interface #val #[DL] : 'unit → chDLOutput ; #val #[DL_GUESS] : chDLInput → 'bool ] (DL_game b)).
    1:{
      intros.
      unfold trimmed.
      unfold trim.
      rewrite filterm_set.
      simpl ; fold chElement.

      rewrite in_fset.
      rewrite mem_head.
      simpl.

      setoid_rewrite filterm_set ; simpl ; fold chElement.
      rewrite in_fset.
      rewrite in_cons.
      rewrite mem_head.
      rewrite Bool.orb_true_r.

      rewrite filterm0.
      reflexivity.
    }
    pose (trimmed_DL false).
    pose (trimmed_DL true).

    assert (trimmed_DDH : forall b, trimmed [interface #val #[DDH] : 'unit → chDDHOutput ] (DDH_game b)).
    1:{
      intros.
      unfold trimmed.
      unfold trim.
      rewrite filterm_set.
      simpl ; fold chElement.

      rewrite in_fset.
      rewrite mem_head.
      simpl.

      (* setoid_rewrite filterm_set ; simpl ; fold chElement. *)
      (* rewrite in_fset. *)
      (* rewrite in_cons. *)
      (* rewrite mem_head. *)
      (* rewrite Bool.orb_true_r. *)

      rewrite filterm0.
      reflexivity.
    }
    pose (trimmed_DDH false).
    pose (trimmed_DDH true).

    (* trimmed_package (dl_real). *)
    (* trimmed_package (dl_ideal). *)
    (* trimmed_package (dl_random). *)
    (* trimmed_package (dl_random2). *)

    trimmed_package (schnorr_real).
    trimmed_package (schnorr_ideal).
    trimmed_package (schnorr_ideal_no_assert).

    trimmed_package (GPowYiNotZero_real i state).
    trimmed_package (GPowYiNotZero_ideal (* i state *)).

    trimmed_package (commit_real).
    trimmed_package (commit_ideal).

    trimmed_package (cds_real).
    trimmed_package (cds_ideal).
    trimmed_package (cds_ideal_no_assert).

    pose proof (fpv := pack_valid (full_protocol_intantiated state i vi)).
    unfold full_protocol_intantiated in fpv.
    unfold pack in fpv.

    eapply Order.le_trans ; [ apply Advantage_triangle with (R := (full_protocol_interface state i vi ∘ par (DL_game false) (par schnorr_ideal (par (par (GPowYiNotZero_ideal (* i state *)) commit_ideal) cds_ideal)))) | ].
    (* rewrite <- (add0r (ϵ + ψ)%R). *)
    apply Num.Theory.lerD.
    {
      (* replace (AdvantageE _ _ _) with (@GRing.zero R) ; [ easy | symmetry ]. *)

      unfold_advantageE.
      unshelve unfold_advantageE ; [ .. | | solve_flat ].
      all:revgoals.
      all: try (apply fsubsetxx).
      all: try rewrite <- fset0E.
      all: try rewrite !fset0U.
      all: try (apply fsubsetxx || solve_in_fset).

      eapply Order.le_trans ; [ apply Advantage_triangle with (R := (par schnorr_ideal (par (par (GPowYiNotZero_real i state) commit_real) cds_real))) | ].
      rewrite <- (add0r (ψ + ν)%R).
      apply Num.Theory.lerD ; [ replace (AdvantageE _ _ _) with (@GRing.zero R) ; [ easy | symmetry ] | ].
      {
        rewrite !(par_commut _ (par _ _)).

        erewrite (Advantage_par _ _ _ _ (fset [DL_loc] :|: LA)).
        3,4: apply pack_valid.
        4,5,6: solve_trimmed.
        3: solve_flat.
        2:{
          ssprove_valid.

          all:revgoals.
          all: try (apply fsubsetxx).
          all: try rewrite <- fset0E.
          all: try rewrite !fset0U.
          all: try now (rewrite <- !fset_cat ; simpl ; solve_in_fset).
          all: try (apply fsubsetxx || solve_in_fset).
        }

        apply (schnorr_advantage (fset [DL_loc] :|: LA)).
        2:{ rewrite fdisjointUl.
            apply /andP ; split.
            2: eassumption.
            rewrite <- fset1E.
            rewrite fdisjoint1s.
            rewrite notin_fset.
            easy.
        }
        2: apply fdisjoints0.

        (* ssprove_valid. *)

        (* 3,4: apply pack_valid. *)
        (* 4,5,6: solve_trimmed. *)
        (* 3: solve_flat. *)
        (* 2:{ *)
        (*   ssprove_valid. *)

        (*   all:revgoals. *)
        (*   all: try (apply fsubsetxx). *)
        (*   all: try rewrite <- fset0E. *)
        (*   all: try rewrite !fset0U. *)
        (*   all: try now (rewrite <- !fset_cat ; simpl ; solve_in_fset). *)
        (*   all: try (apply fsubsetxx || solve_in_fset). *)
        (* } *)


        pose (trimmed_ID ([interface #val #[SCHNORR] : schnorrInput → schnorrOutput ]
           :|: ([interface #val #[GPOWYINOTZERO] : chGPowYiNotZeroInput → chGPowYiNotZeroOutput ]
                :|: [interface #val #[COMMIT] : chCommitInput → chCommitOutput ]
                :|: [interface #val #[CDS] : CDSinput → CDSoutput ]))).
        pose (trimmed_ID [interface #val #[SCHNORR] : schnorrInput → schnorrOutput ]).

        solve_valid_package.
        1: apply H.
        1:{
          simpl_idents.
          solve_idents.
        }
        1: apply valid_ID ; solve_flat.
        1: apply valid_ID ; solve_flat.
        Unshelve.
        all:revgoals.

        all: try rewrite <- fset0E.
        all: try rewrite !fset0U.
        all: try rewrite !fsetU0.

        all: try (apply fsubsetxx).
        all: try rewrite <- fset0E.
        all: try rewrite !fset0U.
        all: unfold Game_import ; try rewrite <- fset0E.
        all: try now (rewrite <- !fset_cat ; simpl ; solve_in_fset).
        all: try (apply fsubsetxx || solve_in_fset).
      }

      unshelve unfold_advantageE ; [ .. | | solve_flat ].
      all:revgoals.
      all: try (apply fsubsetxx).
      all: try rewrite <- fset0E.
      all: try rewrite !fset0U.
      all: try now (rewrite <- !fset_cat ; simpl ; solve_in_fset).
      all: try (apply fsubsetxx || solve_in_fset).


      eapply Order.le_trans ; [ apply Advantage_triangle with (R := ((par (par (GPowYiNotZero_ideal (* i state *)) commit_ideal) cds_real))) | ].
      rewrite <- (addr0 (ψ + ν)%R).
      apply Num.Theory.lerD ; [ | replace (AdvantageE _ _ _) with (@GRing.zero R) ; [ easy | symmetry ] ].
      {
        rewrite !(par_commut _ cds_real).
        unfold_advantageE.
        2: solve_flat.
        Unshelve.
        all: try (apply fsubsetxx).
        all: try rewrite <- fset0E.
        all: try rewrite !fset0U.
        all: try now (rewrite <- !fset_cat ; simpl ; solve_in_fset).
        all: try (apply fsubsetxx || solve_in_fset).

        eapply Order.le_trans ; [ apply Advantage_triangle with (R := ((par (GPowYiNotZero_real i state) commit_ideal))) | ].
        apply Num.Theory.lerD.
        {
          unfold_advantageE.
          2: solve_flat.
          match goal with | |- context [ AdvantageE _ _ ?A ] => specialize (H1 A) end.
          unfold ϵ_COMMIT in H1.
          rewrite Advantage_sym.
          rewrite Advantage_E in H1.
          apply H1.
        }
        {
          rewrite !(par_commut _ commit_ideal).
          unfold_advantageE.
          2: solve_flat.
          match goal with | |- context [ AdvantageE _ _ ?A ] => specialize (H2 A) end.
          unfold ϵ_GPOWYINOTZERO in H2.
          rewrite Advantage_sym.
          rewrite Advantage_E in H2.
          apply H2.
        }
      }
      {
        unfold_advantageE.
        2: solve_flat.
        Unshelve.
        all: try (apply fsubsetxx).
        all: try rewrite <- fset0E.
        all: try rewrite !fset0U.
        all: try now (rewrite <- !fset_cat ; simpl ; solve_in_fset).
        all: try (apply fsubsetxx || solve_in_fset).

        eapply cds_advantage.
        1: instantiate (1 := LA :|: (fset [DL_loc;DDH_loc1; DDH_loc2])).
        2:{
          unfold OR_ZKP.proof_args.MyAlg.Sigma_locs.
          rewrite fdisjointUl.
          apply /andP ; split.
          - eassumption.
          - rewrite <- fset1E.
            rewrite fdisjoints1.
            apply notin_fset.
        }
        2:{ apply fdisjoints0. }

        pose (trimmed_ID
          ([interface #val #[SCHNORR] : schnorrInput → schnorrOutput ]
           :|: ([interface #val #[GPOWYINOTZERO] : chGPowYiNotZeroInput → chDLOutput ]
                :|: [interface #val #[COMMIT] : chDLOutput → chCommitOutput ]
                :|: [interface #val #[CDS] : CDSinput → CDSoutput ]))).
        pose (trimmed_ID ([interface #val #[GPOWYINOTZERO] : chGPowYiNotZeroInput → chDLOutput ]
          :|: [interface #val #[COMMIT] : chDLOutput → chCommitOutput ]
          :|: [interface #val #[CDS] : CDSinput → CDSoutput ])).
        epose (trimmed_ID [interface #val #[CDS] : CDSinput → CDSoutput ]).

        solve_valid_package.
        1: apply H.

        1:{
          simpl_idents.
          solve_idents.
        }

        2:{
          simpl_idents.
          rewrite <- !fset1E.
          rewrite fdisjoint1s.
          rewrite !in_fset.
          easy.
        }

        1,2,3: apply valid_ID ; solve_flat.

        Unshelve.
        all:revgoals.
        all: try (apply fsubsetxx).
        all: try rewrite <- fset0E.
        all: try rewrite !fset0U.
        all: try now (rewrite <- !fset_cat ; simpl ; solve_in_fset).
        (* all: try (apply fsubsetxx || solve_in_fset). *)
        all: try (apply fsubsetxx).
        all: unfold Game_import ; try rewrite <- fset0E.
        1: try (apply fsubsetxx || solve_in_fset).
        1: try (apply fsubsetxx || solve_in_fset).
        1: instantiate (1 := fset0).
        1: simpl.
        1: try (apply fsubsetxx || solve_in_fset).
        1: try (apply fsubsetxx || solve_in_fset).
        1: try (apply fsubsetxx || solve_in_fset).
      }
    }

    eapply Order.le_trans ; [ apply Advantage_triangle with (R := (full_protocol_interface state i vi ∘ par (DL_game false) (par schnorr_ideal_no_assert (par (par (GPowYiNotZero_ideal (* i state *)) commit_ideal) cds_ideal_no_assert)))) | ].
    rewrite <- (add0r (ϵ + ζ)%R). (* rewrite <- (add0r (ϵ + (ϵ + ζ))%R). *)
    apply Num.Theory.lerD.
    {
      replace (AdvantageE _ _ _) with (@GRing.zero R) ; [ easy | symmetry ].

      apply: eq_rel_perf_ind_ignore.
      2:{
        unshelve solve_valid_package.
        all: revgoals.
        all: try (apply fsubsetxx).
        all: try rewrite <- fset0E.
        all: try rewrite !fset0U.
        all: try rewrite !fsetU0.
        all: try now (rewrite <- !fset_cat ; simpl ; solve_in_fset).
        all: try (apply fsubsetxx || solve_in_fset).

        all: simpl_idents; solve_idents.
      }
      1:{
        unshelve solve_valid_package.
        all: revgoals.
        all: try (apply fsubsetxx).
        all: try rewrite <- fset0E.
        all: try rewrite !fset0U.
        all: try rewrite !fsetU0.
        all: try now (rewrite <- !fset_cat ; simpl ; solve_in_fset).
        all: try (apply fsubsetxx || solve_in_fset).

        all: simpl_idents; solve_idents.
      }
      3: apply H.
      1: (apply fsubsetxx || solve_in_fset).
      2,3: eassumption.

      unfold eq_up_to_inv.
      simplify_eq_rel inp_unit.

      simpl.

      repeat choice_type_eqP_handle.
      erewrite !cast_fun_K.
      fold chElement.

      apply (r_uniform_bij) with (f := fun x => x) ; [ now apply inv_bij | intros xi ].
      apply better_r_put_get_lhs.
      apply better_r_put_get_rhs.
      apply r_put_vs_put.

      rewrite bind_rewrite.
      (* rewrite bind_rewrite. *)

      simpl.

      repeat choice_type_eqP_handle.
      erewrite !cast_fun_K.
      fold chElement.
      
      apply (r_uniform_bij) with (f := fun x => x) ; [ now apply inv_bij | intros ? ].

      replace (Schnorr_ZKP.Schnorr.MyParam.R
                 (g ^+ FieldToWitness (WitnessToField (otf xi)))
                 (FieldToWitness (WitnessToField (otf xi)))) with
        true.
      2:{
        symmetry.
        unfold Schnorr_ZKP.Schnorr.MyParam.R.
        rewrite eqxx.
        reflexivity.
      }
      unfold assertD at 1.



      simpl.

      ssprove_sync=> ?.
      ssprove_same_head_generic.
      ssprove_sync=> ?.
      ssprove_sync=> ?.
      
      rewrite !eqxx.
      rewrite !FieldToWitnessCancel.

      (* replace (_ == _) with true ; [ | symmetry ]. *)
      (* 2:{ *)
      (*   rewrite mulrC. *)
      (*   rewrite trunc_pow. *)
      (*   rewrite expgM. *)
      (*   rewrite inv_is_inv. *)
      (*   destruct vi ; now rewrite eqxx. *)
      (* } *)
      simpl.
      ssprove_sync=> ?.
      ssprove_sync=> ?.
      ssprove_sync=> ?.
      ssprove_sync=> ?.
      apply r_ret.
      {
        intros.
        split ; [ repeat rewrite pair_equal_spec ; repeat split | ].
        unfold heap_ignore.
        intros ℓ ?.
        destruct H13 as [? [[? []] ?]].
        subst.
        rewrite get_set_heap_neq.
        2:{ apply /eqP ; red ; intros.
            subst.
            rewrite fsetUid in H14.
            rewrite in_fset in H14.
            now rewrite mem_head in H14.
        }

        rewrite get_set_heap_neq.
        2:{ apply /eqP ; red ; intros.
            subst.
            rewrite fsetUid in H14.
            rewrite in_fset in H14.
            now rewrite mem_head in H14.
        }

        now apply H13.
      }
    }

    eapply Order.le_trans ; [ apply Advantage_triangle with (R := (full_protocol_interface_step1 state i vi ∘ (par (DL_game false) ((par schnorr_ideal_no_assert (par (par (GPowYiNotZero_ideal (* i state *)) commit_ideal) cds_ideal_no_assert)))))) | ].
    rewrite <- (add0r (ϵ + ζ)%R). (* rewrite <- (add0r (ϵ + (ϵ + ζ))%R). *)
    apply Num.Theory.lerD.
    1:{
      replace (AdvantageE _ _ _) with (@GRing.zero R) ; [ easy | symmetry ].

      apply: eq_rel_perf_ind_ignore.
      2:{
        unshelve solve_valid_package.
        all: revgoals.
        all: try (apply fsubsetxx).
        all: try rewrite <- fset0E.
        all: try rewrite !fset0U.
        all: try rewrite !fsetU0.
        all: try now (rewrite <- !fset_cat ; simpl ; solve_in_fset).
        all: try (apply fsubsetxx || solve_in_fset).
        all: (simpl_idents ; solve_idents).
      }
      1:{
        unshelve solve_valid_package.
        all: revgoals.
        all: try (apply fsubsetxx).
        all: try rewrite <- fset0E.
        all: try rewrite !fset0U.
        all: try rewrite !fsetU0.
        all: try now (rewrite <- !fset_cat ; simpl ; solve_in_fset).
        all: try (apply fsubsetxx || solve_in_fset).
        all: (simpl_idents ; solve_idents).
      }
      3: apply H.
      1: (apply fsubsetxx || solve_in_fset).
      2,3: eassumption.

      unfold eq_up_to_inv.
      simplify_eq_rel inp_unit.

      simpl.

      repeat choice_type_eqP_handle.
      erewrite !cast_fun_K.
      fold chElement.

      apply (r_uniform_bij) with (f := fun x => x) ; [ now apply inv_bij | intros xi ].

      apply better_r_put_get_lhs.
      apply better_r_put_get_rhs.
      apply r_put_vs_put.

      rewrite bind_rewrite.
      (* rewrite bind_rewrite. *)

      simpl.

      repeat choice_type_eqP_handle.
      erewrite !cast_fun_K.
      fold chElement.

      simpl.

      ssprove_sync=> ?.
      ssprove_sync=> ?.

      ssprove_same_head_generic.
      (* ssprove_same_head_generic. *)

      rewrite !FieldToWitnessCancel.

      ssprove_sync=> ?.
      ssprove_sync=> ?.
      ssprove_sync=> ?.
      ssprove_sync=> ?.
      ssprove_sync=> ?.
      ssprove_sync=> ?.

      apply r_ret.
      split ; [ repeat rewrite pair_equal_spec ; repeat split | ].

      unfold heap_ignore.
      intros ℓ ?.
      destruct H13 as [? [[? []] ?]].
      subst.
      rewrite get_set_heap_neq.
      2:{ apply /eqP ; red ; intros.
          subst.
          rewrite fsetUid in H14.
          rewrite in_fset in H14.
          now rewrite mem_head in H14.
      }

      rewrite get_set_heap_neq.
      2:{ apply /eqP ; red ; intros.
          subst.
          rewrite fsetUid in H14.
          rewrite in_fset in H14.
          now rewrite mem_head in H14.
      }

      now apply H13.
    }

    eapply Order.le_trans ; [ apply Advantage_triangle with (R := (full_protocol_interface_step1 state i vi ∘ (par (DL_game true) ((par schnorr_ideal_no_assert (par (par (GPowYiNotZero_ideal (* i state *)) commit_ideal) cds_ideal_no_assert)))))) | ].
    apply Num.Theory.lerD.
    1:{
      rewrite <- Advantage_link.
      epose (Advantage_parR (par schnorr_ideal_no_assert
                                               (par (par (GPowYiNotZero_ideal (* i state *)) commit_ideal) cds_ideal_no_assert)) (DL_game false) (DL_game true) (A ∘ full_protocol_interface_step1 state i vi)).
      erewrite e.
      3,4: apply pack_valid.
      4,5,6: solve_trimmed.
      3:{
        rewrite fset_cons.
        rewrite fset1E.
        
        clear ;
          unfold flat ;

          intros n u1 u2 ;
          try rewrite !in_fsetU ;

          let H := fresh in
          let H0 := fresh in
          intros H H0.
        rewrite <- !fset1E in H, H0.
        rewrite !in_fset1 in H, H0 ;

    repeat (apply (ssrbool.elimT ssrbool.orP) in H ; destruct H) ; apply (ssrbool.elimT eqP) in H ; inversion H ; subst ;

      repeat (apply (ssrbool.elimT ssrbool.orP) in H0 ; destruct H0) ; apply (ssrbool.elimT eqP) in H0 ; now inversion H0 ; subst.
      }
      2:{
        unshelve solve_valid_package.
        all: revgoals.
        all: try (apply fsubsetxx).
        all: try rewrite <- fset0E.
        all: try rewrite !fset0U.
        all: try rewrite !fsetU0.
        all: try now (rewrite <- !fset_cat ; simpl ; solve_in_fset).
        all: try (apply fsubsetxx || solve_in_fset).
        all: (simpl_idents ; solve_idents).
      }
      apply H0.
    }

    pose (step4 := full_protocol_interface_step4 state i vi ∘ (par (DL_game true) (par (DDH_game true)(par schnorr_ideal_no_assert (par (par (GPowYiNotZero_ideal (* i state *)) commit_ideal) cds_ideal_no_assert))))).
    eassert (step4_valid : ValidPackage _ Game_import [interface #val #[ FULL_PROTOCOL_INTERFACE ] : 'unit → chSingleProtocolTranscript ] step4).
    {
      subst step4.
      instantiate (1 := (fset [DL_loc;DDH_loc1; DDH_loc2])).
      unshelve solve_valid_package.
      all: revgoals.
      all: try (apply fsubsetxx).
      all: try rewrite <- fset0E.
      all: try rewrite !fset0U.
      all: try rewrite !fsetU0.
      all: try now (rewrite <- !fset_cat ; simpl ; solve_in_fset).
      all: try (apply fsubsetxx || solve_in_fset).
      all: try (simpl_idents ; solve_idents).
      simpl.
      solve_in_fset.
    }

    pose (step1 := (full_protocol_interface_step1 state i vi ∘ (par (DL_game true) ((* par (DDH_game false) *) (par schnorr_ideal_no_assert (par (par (GPowYiNotZero_ideal (* i state *)) commit_ideal) cds_ideal_no_assert)))))).
    eassert (step1_valid : ValidPackage _ Game_import [interface #val #[ FULL_PROTOCOL_INTERFACE ] : 'unit → chSingleProtocolTranscript ] step1).
    {
      subst step1.
      instantiate (1 := (fset [DL_loc])).
      unshelve solve_valid_package.
      all: revgoals.
      all: try (apply fsubsetxx).
      all: try rewrite <- fset0E.
      all: try rewrite !fset0U.
      all: try rewrite !fsetU0.
      all: try now (rewrite <- !fset_cat ; simpl ; solve_in_fset).
      all: try (apply fsubsetxx || solve_in_fset).
      all: try (simpl_idents ; solve_idents).
    }

    pose (step2 := full_protocol_interface_step2 state i vi ∘ (par (DL_game true) (par (DDH_game false) (par schnorr_ideal_no_assert (par (par (GPowYiNotZero_ideal (* i state *)) commit_ideal) cds_ideal_no_assert))))).
    eassert (step2_valid : ValidPackage _ Game_import [interface #val #[ FULL_PROTOCOL_INTERFACE ] : 'unit → chSingleProtocolTranscript ] step2).
    {
      subst step2.
      instantiate (1 := (fset [DL_loc;DDH_loc1; DDH_loc2])).
      unshelve solve_valid_package.

      all: revgoals.
      all: try (apply fsubsetxx).
      all: try rewrite <- fset0E.
      all: try rewrite !fset0U.
      all: try rewrite !fsetU0.
      all: try now (rewrite <- !fset_cat ; simpl ; solve_in_fset).
      all: try (simpl_idents ; solve_idents).
      all: simpl.
      all: try (apply fsubsetxx || solve_in_fset).
    }

    rewrite <- (add0r ζ%R). (* rewrite <- (add0r (ϵ + ζ)%R). *)
    (* try apply (AdvantageE_le_0 _ _ _ ) ; *)
    eapply Order.le_trans ; [ apply Advantage_triangle with (R := step2) | ].
    apply Num.Theory.lerD.
    (* ; *)
    (* replace (AdvantageE _ _ _) with (@GRing.zero R) ; [ *)
    (*     replace (AdvantageE _ _ _) with (@GRing.zero R) ; [ rewrite add0r | symmetry ] | *)
    (*     symmetry ] ; revgoals. *)
    (* 3:{ *)
    (*   rewrite add0r. *)
    (*   apply Num.Theory.addr_ge0. *)
    (*   1:{ *)
    (*     eapply Order.le_trans. *)
    (*     2: apply (H0 A). *)
    (*     apply Num.Theory.normr_ge0. *)
    (*   } *)
    (*   1:{ *)
    (*     eapply Order.le_trans. *)
    (*     2: apply (H_DDH A). *)
    (*     apply Num.Theory.normr_ge0. *)
    (*   } *)
    (* } *)

    (* split_advantage step2. *)
    {
      fold step1.
      subst step1 step2.

      replace (AdvantageE _ _ _) with (@GRing.zero R) ; [ easy | symmetry ].

      apply: eq_rel_perf_ind_ignore.
      1: (apply fsubsetxx || solve_in_fset).
      2: eassumption.
      2:{ rewrite fset_cons.
          rewrite fset1E.
          rewrite fdisjointUr.
          apply /andP ; split ; eassumption.
      }

      unfold eq_up_to_inv.
      simplify_eq_rel inp_unit.

      simpl.

      repeat choice_type_eqP_handle.
      erewrite !cast_fun_K.
      fold chElement.

      simpl.

      apply (r_uniform_bij) with (f := fun x => x) ; [ now apply inv_bij | intros xi ].

      apply better_r_put_get_rhs.
      apply better_r_put_get_lhs.
      apply r_put_vs_put.

      (* apply better_r_put_lhs. *)

      (* eapply r_transR. *)
      (* 1: apply swap_samples. *)

      (** Reflexivity from here on *)

      simpl.
      repeat choice_type_eqP_handle.
      erewrite !cast_fun_K.
      fold chElement.

      simpl.
      ssprove_sync=> ?.
      ssprove_sync=> ?.
      ssprove_same_head_generic.
      (* ssprove_same_head_generic. *)
      ssprove_sync=> ?.
      ssprove_sync=> ?.
      ssprove_sync=> ?.
      ssprove_sync=> ?.
      ssprove_sync=> ?.
      ssprove_sync=> ?.
      apply r_ret.
      split ; [ repeat rewrite pair_equal_spec ; repeat split | ].
      destruct H13 as [? []].
      destruct H13 as [? []].
      subst.
      intros ? ?.
      rewrite get_set_heap_neq.
      2:{ clear -H13 H14.
        apply /eqP ; red ; intros.
          subst.
          rewrite <- fset_cat in H14.
          rewrite in_fset in H14.
          simpl in H14.
          rewrite notin_cons in H14.
          now move: H14 => /andP [] /eqP.
      }

      rewrite get_set_heap_neq.
      2:{ clear -H13 H14.
          apply /eqP ; red ; intros.
          subst.
          rewrite <- fset_cat in H14.
          rewrite in_fset in H14.
          simpl in H14.
          rewrite notin_cons in H14.
          now move: H14 => /andP [] /eqP.
      }

      now apply H13.
    }

    pose (step3 := full_protocol_interface_step3 state i vi ∘ (par (DL_game true) (par (DDH_game false) (par schnorr_ideal_no_assert (par (par (GPowYiNotZero_ideal (* i state *)) commit_ideal) cds_ideal_no_assert))))).
    eassert (step3_valid : ValidPackage _ Game_import [interface #val #[ FULL_PROTOCOL_INTERFACE ] : 'unit → chSingleProtocolTranscript ] step3).
    {
      subst step3.
      instantiate (1 := (fset [DL_loc;DDH_loc1; DDH_loc2])).
      unshelve solve_valid_package.
      all: revgoals.
      all: try (apply fsubsetxx).
      all: try rewrite <- fset0E.
      all: try rewrite !fset0U.
      all: try rewrite !fsetU0.
      all: try now (rewrite <- !fset_cat ; simpl ; solve_in_fset).
      all: try (simpl_idents ; solve_idents).
      all: simpl.
      all: try (apply fsubsetxx || solve_in_fset).
    }

    rewrite <- (add0r ζ%R). (* rewrite <- (add0r (ϵ + ζ)%R). *)
    eapply Order.le_trans ; [ apply Advantage_triangle with (R := step3) | ].
    apply Num.Theory.lerD.
    (* split_advantage step3. *)
    {
      subst step2 step3.

      replace (AdvantageE _ _ _) with (@GRing.zero R) ; [ easy | symmetry ].

      apply: eq_rel_perf_ind_ignore.
      1: (apply fsubsetxx || solve_in_fset).
      2:{ rewrite fset_cons.
          rewrite fset1E.
          rewrite fdisjointUr.
          apply /andP ; split ; eassumption.
      }
      2:{ rewrite fset_cons.
          rewrite fset1E.
          rewrite fdisjointUr.
          apply /andP ; split ; eassumption.
      }

      unfold eq_up_to_inv.
      simplify_eq_rel inp_unit.

      simpl.

      repeat choice_type_eqP_handle.
      erewrite !cast_fun_K.
      fold chElement.

      simpl.

      eapply (r_transR _ (
                  xi ← sample uniform #|'Z_q| ;;
                  #put DDH_loc1 := Option_Some (WitnessToField (otf xi)) ;;
                  a1 ← sample uniform #|'Z_q| ;;
                  a2 ← sample uniform #|'Z_q| ;;
                  x ← is_state Build_t_SchnorrZKPCommit ;;
                  yi ← sample uniform #|'Z_q| ;;
                  #put DDH_loc2 := Option_Some (WitnessToField (otf yi)) ;;
                  _)).
      1:{
        simpl.

        apply (r_uniform_bij) with (f := fun x => x) ; [ now apply inv_bij | intros xi ].
        apply better_r_put_rhs.
        apply better_r_put_lhs.

        simpl.

        repeat choice_type_eqP_handle.
        erewrite !cast_fun_K.
        fold chElement.

        simpl.

        eapply (r_transR ).
        1:{
          apply (r_uniform_bij) with (f := fun x => x) ; [ now apply inv_bij | intros yi ].
          apply better_r_put_rhs.
          apply (r_uniform_bij) with (f := fun x => x) ; [ now apply inv_bij | intros a1 ].
          apply (r_uniform_bij) with (f := fun x => x) ; [ now apply inv_bij | intros a2 ].

          apply (better_r_put_lhs (DDH_loc2) (Option_Some (WitnessToField (otf yi)))).

          eapply rpre_weaken_rule.
          1: apply rreflexivity_rule.

          intros ? ? [].
          destruct H13 as [].
          destruct H13 as [? []].
          subst.

          reflexivity.
        }
        simpl.

        eapply (r_transR ).
        1:{
          eapply (r_transL).
          1:apply swap_samples.
          apply (r_uniform_bij) with (f := fun x => x) ; [ now apply inv_bij | intros yi ].
          apply (r_uniform_bij) with (f := fun x => x) ; [ now apply inv_bij | intros a1 ].
          apply rreflexivity_rule.
        }
        simpl.

        apply (r_uniform_bij) with (f := fun x => x) ; [ now apply inv_bij | intros a1 ].

        eapply (r_transR ).
        1:{
          eapply (r_transL).
          1:apply swap_samples.
          apply (r_uniform_bij) with (f := fun x => x) ; [ now apply inv_bij | intros yi ].
          apply (r_uniform_bij) with (f := fun x => x) ; [ now apply inv_bij | intros a2 ].
          apply rreflexivity_rule.
        }
        simpl.

        apply (r_uniform_bij) with (f := fun x => x) ; [ now apply inv_bij | intros a2 ].

        eapply (r_transL ).
        1:{
          eapply (proj2 (bobble_sampleC _ _ _ _)).
          apply r_bind_feq.
          1: apply rreflexivity_rule.
          intros.
          apply (r_uniform_bij) with (f := fun x => x) ; [ now apply inv_bij | intros yi ].
          apply rreflexivity_rule.
        }
        simpl.

        apply (r_uniform_bij) with (f := fun x => x) ; [ now apply inv_bij | intros yi ].

        apply (better_r_put_rhs (DDH_loc2) (Option_Some (WitnessToField (otf yi)))).

        eapply r_bind.
        1:{
          eapply (r_reflexivity_alt (set_rhs DDH_loc2 (Option_Some (WitnessToField (otf yi)))
        (set_lhs DDH_loc1 (Option_Some (WitnessToField (otf xi)))
           (set_rhs DDH_loc1 (Option_Some (WitnessToField (otf xi))) (λ '(s₀, s₁), s₀ = s₁))))).
          1:{ instantiate (1 := fset0). ssprove_valid'_2. }
          1,2: easy.
        }
        intros.
        (* apply (r_uniform_bij) with (f := fun x => x) ; [ now apply inv_bij | intros ? ]. *)

        apply (better_r_put_lhs (DDH_loc2) (Option_Some (WitnessToField (otf yi)))).

        apply better_r.
        eapply r_get_remind_rhs.
        1:{
          unfold Remembers_rhs.
          intros.
          unfold rem_rhs.
          destruct H13 as [? []].
          destruct H13 as [? []].
          destruct H15 as [[] ?].
          destruct H15 as [[] ?].
          destruct H15 as [].
          subst.
          rewrite get_set_heap_neq.
          {
            rewrite get_set_heap_eq.
            {
              reflexivity.
            }
          }
          apply /eqP.
          easy.
        }

        apply rpre_hypothesis_rule.
        intros ? ? ?.
        destruct H13 as [? []].
        destruct H13 as [? []].
        destruct H15 as [[] ?].
        destruct H15 as [[] ?].
        destruct H15 as [].
        subst.

        eapply rpre_weaken_rule.
        1: apply rreflexivity_rule.

        intros ? ? ?.
        destruct H13 as [].
        simpl in H13, H14.
        subst.
        reflexivity.
      }

      apply (r_uniform_bij) with (f := fun x => x) ; [ now apply inv_bij | intros xi ].
      apply better_r_put_rhs.
      apply better_r_put_lhs.

      apply better_r.
      eapply r_get_remind_lhs.
      1:{
        unfold Remembers_lhs.
        intros.
        unfold rem_lhs.
        destruct H13 as [? []].
        destruct H13 as [? []].
        subst.
        rewrite get_set_heap_eq.
        {
          reflexivity.
        }
      }

      simpl.
      
      repeat choice_type_eqP_handle.
      erewrite !cast_fun_K.
      fold chElement.

      simpl.

      apply (r_uniform_bij) with (f := fun x => x) ; [ now apply inv_bij | intros ? ].
      apply (r_uniform_bij) with (f := fun x => x) ; [ now apply inv_bij | intros ? ].

      eapply r_bind.
      1:{
        eapply r_reflexivity_alt.
        1:{ instantiate (1 := fset0). ssprove_valid'_2. }
        1,2: easy.
      }
      intros.

      apply (r_uniform_bij) with (f := fun x => x) ; [ now apply inv_bij | intros yi ].
      apply better_r_put_rhs.
      apply (r_uniform_bij) with (f := fun x => x) ; [ now apply inv_bij | intros ? ].
      apply (r_uniform_bij) with (f := fun x => x) ; [ now apply inv_bij | intros ? ].
      apply (r_uniform_bij) with (f := fun x => x) ; [ now apply inv_bij | intros ? ].
      apply (r_uniform_bij) with (f := fun x => x) ; [ now apply inv_bij | intros ? ].
      apply (r_uniform_bij) with (f := fun x => x) ; [ now apply inv_bij | intros ? ].
      
      apply r_ret.
      clear.
      intros.
      destruct H.
      destruct H.
      destruct H.
      destruct H1.
      destruct H1.
      destruct H1.
      destruct H1.
      subst.
      replace (g ^+ FieldToWitness (WitnessToField (otf yi)) ^+ FieldToWitness (WitnessToField (otf xi))) with (g ^+ (FieldToWitness (WitnessToField (otf xi)) * FieldToWitness (WitnessToField (otf yi)))).
      2:{
        rewrite <- !expgM.
        rewrite mulnC.
        reflexivity.
      }
      split ; [ repeat rewrite pair_equal_spec ; repeat split | ].
      - intros ? ?.
        rewrite get_set_heap_neq.
        2:{ clear -H.
        apply /eqP ; red ; intros.
          subst.
          rewrite <- fset_cat in H.
          rewrite in_fset in H.
          simpl in H.
          rewrite !notin_cons in H.
          repeat move: H => /andP [/eqP ? H].
          easy.
        }

        rewrite get_set_heap_neq.
        2:{ clear -H.
        apply /eqP ; red ; intros.
          subst.
          rewrite <- fset_cat in H.
          rewrite in_fset in H.
          simpl in H.
          rewrite !notin_cons in H.
          repeat move: H => /andP [/eqP ? H].
          easy.
        }

        rewrite get_set_heap_neq.
        2:{ clear -H.
        apply /eqP ; red ; intros.
          subst.
          rewrite <- fset_cat in H.
          rewrite in_fset in H.
          simpl in H.
          rewrite !notin_cons in H.
          repeat move: H => /andP [/eqP ? H].
          easy.
        }

        now apply H1.
    }

    {
      fold step4.
      subst step3 step4.

      rewrite <- (addr0 ζ).
      (* rewrite addrC. *)
      eapply Order.le_trans ; [ apply Advantage_triangle with (R := (full_protocol_interface_step3 state i vi ∘ (par (DL_game true) (par (DDH_game true) (par schnorr_ideal_no_assert (par (par (GPowYiNotZero_ideal (* i state *)) commit_ideal) cds_ideal_no_assert)))))) | ].
      apply Num.Theory.lerD.

      (* replace (AdvantageE _ _ _) with (@GRing.zero R) ; [ | symmetry ]. *)
      1:{
        rewrite <- Advantage_link.
        setoid_rewrite Advantage_par.
        1:{
          setoid_rewrite Advantage_parR.
          1:{
            unfold ϵ_DDH in H_DDH.
            rewrite <- (Advantage_E DDH_game).
            apply H_DDH.
          }

          2,3: apply DDH_game.
          2: solve_flat.
          2: solve_trimmed.
          2,3: solve_trimmed.

          unshelve solve_valid_package.
          all: revgoals.
          all: try (apply fsubsetxx).
          all: try rewrite <- fset0E.
          all: try rewrite !fset0U.
          all: try rewrite !fsetU0.
          all: try now (rewrite <- !fset_cat ; simpl ; solve_in_fset).
          all: try (simpl_idents ; solve_idents).
          all: simpl.
          all: try (apply fsubsetxx || solve_in_fset).
        }

        5,6,7: solve_trimmed.
        1: apply pack_valid.

        {
          unshelve solve_valid_package.
          all: revgoals.
          all: try (apply fsubsetxx).
          all: try rewrite <- fset0E.
          all: try rewrite !fset0U.
          all: try rewrite !fsetU0.
          all: try (simpl_idents ; solve_idents).
          all: simpl ; try (unfold Game_import ; rewrite <- fset0E).
          all: try now (rewrite <- !fset_cat ; simpl ; solve_in_fset).
          all: try (apply fsubsetxx || solve_in_fset).
        }
        {
          unshelve solve_valid_package.
          all: revgoals.
          all: try (apply fsubsetxx).
          all: try rewrite <- fset0E.
          all: try rewrite !fset0U.
          all: try rewrite !fsetU0.
          all: try (simpl_idents ; solve_idents).
          all: simpl ; try (unfold Game_import ; rewrite <- fset0E).
          all: try now (rewrite <- !fset_cat ; simpl ; solve_in_fset).
          all: try (apply fsubsetxx || solve_in_fset).
        }

        solve_flat.
      }

      (* replace (AdvantageE _ _ _) with (@GRing.zero R) ; [ | symmetry ]. *)
      (* { *)
      (*   eapply Order.le_trans. *)
      (*   2: apply (H0 A). *)
      (*   apply Num.Theory.normr_ge0. *)
      (* } *)
      replace (AdvantageE _ _ _) with (@GRing.zero R) ; [ easy | symmetry ].

      apply: eq_rel_perf_ind_ignore.
      1: (apply fsubsetxx || solve_in_fset).
      2:{ rewrite fset_cons.
          rewrite fset1E.
          rewrite fdisjointUr.
          apply /andP ; split ; eassumption.
      }
      2:{ rewrite fset_cons.
          rewrite fset1E.
          rewrite fdisjointUr.
          apply /andP ; split ; eassumption.
      }

      unfold eq_up_to_inv.
      simplify_eq_rel inp_unit.

      simpl.

      repeat choice_type_eqP_handle.
      erewrite !cast_fun_K.
      fold chElement.

      simpl.

      apply (r_uniform_bij) with (f := fun x => x) ; [ now apply inv_bij | intros xi ].
      apply better_r_put_rhs.
      apply better_r_put_lhs.
      apply (r_uniform_bij) with (f := fun x => x) ; [ now apply inv_bij | intros yi ].
      apply better_r_put_rhs.
      apply better_r_put_lhs.

      simpl.

      repeat choice_type_eqP_handle.
      erewrite !cast_fun_K.
      fold chElement.

      simpl.

      apply (r_uniform_bij) with (f := fun x => x) ; [ now apply inv_bij | intros zi ].
      apply (r_uniform_bij) with (f := fun x => x) ; [ now apply inv_bij | intros a1 ].
      apply (r_uniform_bij) with (f := fun x => x) ; [ now apply inv_bij | intros a2 ].
      ssprove_same_head_generic.


      apply better_r.
      eapply r_get_remind_rhs.
      1:{
        unfold Remembers_rhs.
        intros.
        unfold rem_rhs.
        destruct H13 as [? []].
        destruct H13 as [? []].
        destruct H13 as [? []].
        destruct H13 as [? []].
        subst.
        rewrite get_set_heap_neq.
        {
          rewrite get_set_heap_eq.
          {
            reflexivity.
          }
        }
        apply /eqP.
        easy.
      }

      eapply r_get_remind_lhs.
      1:{
        unfold Remembers_lhs.
        intros.
        unfold rem_lhs.
        destruct H13 as [? []].
        destruct H13 as [? []].
        destruct H13 as [? []].
        destruct H13 as [? []].
        subst.
        rewrite get_set_heap_neq.
        {
          rewrite get_set_heap_eq.
          {
            reflexivity.
          }
        }
        apply /eqP.
        easy.
      }

      simpl.

      repeat choice_type_eqP_handle.
      erewrite !cast_fun_K.
      fold chElement.

      simpl.

        (* TODO: Use r_pre_hypothesis to solve evar constraints instead of further elaborating *)
        apply (r_uniform_bij) with (f := fun x => x) ; [ now apply inv_bij | intros ? ].
        apply (r_uniform_bij) with (f := fun x => x) ; [ now apply inv_bij | intros ? ].
        apply (r_uniform_bij) with (f := fun x => x) ; [ now apply inv_bij | intros ? ].
        apply (r_uniform_bij) with (f := fun x => x) ; [ now apply inv_bij | intros ? ].
        apply (r_uniform_bij) with (f := fun x => x) ; [ now apply inv_bij | intros ? ].

        apply r_ret.
        intros.
        destruct H13 as [? []].
        destruct H13 as [? []].
        destruct H13 as [? []].
        destruct H13 as [? []].
        subst.

        (* replace (FieldToWitness (WitnessToField (otf zi))) *)
        (*   with (FieldToWitness (WitnessToField (otf xi)) * *)
        (*            FieldToWitness (WitnessToField (otf yi)))%R. *)
        (* 2: admit. (* DDH assumption *) *)
        rewrite !trunc_pow.
        split ; [ repeat rewrite pair_equal_spec ; repeat split | ].
        intros ? ?.
        rewrite get_set_heap_neq.
        2:{ clear -H14.
            rename H14 into H.
            apply /eqP ; red ; intros.
          subst.
          rewrite <- fset_cat in H.
          rewrite in_fset in H.
          simpl in H.
          rewrite !notin_cons in H.
          repeat move: H => /andP [/eqP ? H].
          easy.
        }

        rewrite get_set_heap_neq.
        2:{ clear -H14.
            rename H14 into H.
            apply /eqP ; red ; intros.
          subst.
          rewrite <- fset_cat in H.
          rewrite in_fset in H.
          simpl in H.
          rewrite !notin_cons in H.
          repeat move: H => /andP [/eqP ? H].
          easy.
        }

        rewrite get_set_heap_neq.
        2:{ clear -H14.
            rename H14 into H.
            apply /eqP ; red ; intros.
          subst.
          rewrite <- fset_cat in H.
          rewrite in_fset in H.
          simpl in H.
          rewrite !notin_cons in H.
          repeat move: H => /andP [/eqP ? H].
          easy.
        }

        rewrite get_set_heap_neq.
        2:{ clear -H14.
            rename H14 into H.
            apply /eqP ; red ; intros.
          subst.
          rewrite <- fset_cat in H.
          rewrite in_fset in H.
          simpl in H.
          rewrite !notin_cons in H.
          repeat move: H => /andP [/eqP ? H].
          easy.
        }
        now apply H13.
    }
  Qed. (* Fail Timeout 5 Qed. Admitted. (* 123.43 secs *) *)

  Lemma all_step_advantage :
    forall state (i : nat),
    ∀ (LA : {fset Location}) (A : raw_package),
      ValidPackage LA [interface #val #[ FULL_PROTOCOL_INTERFACE ] : 'unit → chSingleProtocolTranscript ] A_export A →
      LA :#: Schnorr_ZKP.Schnorr.MyAlg.Sigma_locs ->
      LA :#: Schnorr_ZKP.Schnorr.MyAlg.Simulator_locs ->
      LA :#: OR_ZKP.proof_args.MyAlg.Sigma_locs ->
      LA :#: OR_ZKP.proof_args.MyAlg.Simulator_locs ->
      LA :#: fset [:: DL_loc] ->
      LA :#: fset [:: DDH_loc1; DDH_loc2] ->
    forall (ϵ : _),
      (forall P, ϵ_DL P <= ϵ)%R →
      forall (ψ : _),
      (forall P, ϵ_COMMIT P <= ψ)%R ->
      forall (ν : _),
      (forall P, ϵ_GPOWYINOTZERO i state P <= ν)%R →
      forall (ζ : _),
      (forall P, ϵ_DDH P <= ζ)%R →
      (AdvantageE
         (full_protocol_interface state i true ∘ par (DL_game false) (par schnorr_real (par (par (GPowYiNotZero_real i state) commit_real) cds_real)))
        (full_protocol_interface state i false ∘ par (DL_game false) (par schnorr_real (par (par (GPowYiNotZero_real i state) commit_real) cds_real))) A <= ((ψ + ν) + (ϵ + ζ)) + ((ψ + ν) + (ϵ + ζ)))%R.
  Proof.
    intros ? ? ? ? ? H_LA_Schnorr_Sigma H_LA_Schnorr_Simulator H_LA_Or_Sigma H_LA_Or_Simulator H_LA_Or_DL_loc H_LA_Or_DDH_loc ? ? ? ? ? ? ζ H_DDH.

    (* Close in from the left *)
    eapply Order.le_trans ; [ apply Advantage_triangle with (R := (full_protocol_interface_step4 state i true ∘ (par (DL_game true) (par (DDH_game true) (par schnorr_ideal_no_assert (par (par (GPowYiNotZero_ideal (* i state *)) commit_ideal) cds_ideal_no_assert)))))) | ].
    apply Num.Theory.lerD.
    1: eapply (protocol_dl_real_to_ideal) ; eassumption.

    (* Close in from the right *)
    eapply Order.le_trans ; [ apply Advantage_triangle with (R := (full_protocol_interface_step4 state i false ∘ (par (DL_game true) (par (DDH_game true) (par schnorr_ideal_no_assert (par (par (GPowYiNotZero_ideal (* i state *)) commit_ideal) cds_ideal_no_assert)))))) | ].
    rewrite <- (add0r ((ψ + ν) + (ϵ + ζ))%R).
    apply Num.Theory.lerD.
    2: rewrite Advantage_sym ; eapply (protocol_dl_real_to_ideal) ; eassumption.

    replace (AdvantageE _ _ _) with (@GRing.zero R) ; [ easy | symmetry ].
    {
      (* trimmed_package (dl_real). *)
      (* trimmed_package (dl_ideal). *)
      (* trimmed_package (dl_random). *)
      (* trimmed_package (dl_random2). *)

      assert (trimmed_DL : forall b, trimmed [interface #val #[DL] : 'unit → chDLOutput ; #val #[DL_GUESS] : chDLInput → 'bool ] (DL_game b)).
      1:{
        intros.
        unfold trimmed.
        unfold trim.
        rewrite filterm_set.
        simpl ; fold chElement.

        rewrite in_fset.
        rewrite mem_head.
        simpl.

        setoid_rewrite filterm_set ; simpl ; fold chElement.
        rewrite in_fset.
        rewrite in_cons.
        rewrite mem_head.
        rewrite Bool.orb_true_r.

        rewrite filterm0.
        reflexivity.
      }
      pose (trimmed_DL false).
      pose (trimmed_DL true).

      assert (trimmed_DDH : forall b, trimmed [interface #val #[DDH] : 'unit → chDDHOutput ] (DDH_game b)).
      1:{
        intros.
        unfold trimmed.
        unfold trim.
        rewrite filterm_set.
        simpl ; fold chElement.

        rewrite in_fset.
        rewrite mem_head.
        simpl.

        (* setoid_rewrite filterm_set ; simpl ; fold chElement. *)
        (* rewrite in_fset. *)
        (* rewrite in_cons. *)
        (* rewrite mem_head. *)
        (* rewrite Bool.orb_true_r. *)

        rewrite filterm0.
        reflexivity.
      }
      pose (trimmed_DDH false).
      pose (trimmed_DDH true).

      trimmed_package (schnorr_real).
      trimmed_package (schnorr_ideal).
      trimmed_package (schnorr_ideal_no_assert).

      trimmed_package (GPowYiNotZero_real i state).
      trimmed_package (GPowYiNotZero_ideal (* i state *)).

      trimmed_package (commit_real).
      trimmed_package (commit_ideal).

      trimmed_package (cds_real).
      trimmed_package (cds_ideal).
      trimmed_package (cds_ideal_no_assert).

      trimmed_package (full_protocol_interface_step4 state i false).

      assert (forall vi, ValidPackage (locs (DL_game true) :|: fset [:: DDH_loc1; DDH_loc2] :|: Schnorr_ZKP.Schnorr.MyAlg.Sigma_locs) Game_import
    [interface #val #[FULL_PROTOCOL_INTERFACE] : chGPowYiNotZeroInput → chSingleProtocolTranscript ]
    (full_protocol_interface_step4 state i vi
     ∘ par (DL_game true)
         (par (DDH_game true)
            (par schnorr_ideal_no_assert
               (par (par (GPowYiNotZero_ideal (* i state *)) commit_ideal)
                  cds_ideal_no_assert))))).
      {
        intros.

        unshelve solve_valid_package.
        all: revgoals.

        all: try (apply fsubsetxx).
        all: try rewrite <- fset0E.
        all: try rewrite !fset0U.
        all: try rewrite !fsetU0.
        all: try now (rewrite <- !fset_cat ; simpl ; solve_in_fset).
        all: try (apply fsubsetxx || solve_in_fset).
        all: try (simpl_idents ; solve_idents).
      }

      apply: eq_rel_perf_ind_ignore.
      1: apply fsubsetxx.
      2:{ rewrite fdisjointUr.
          rewrite fdisjointUr.
          apply /andP ; split ; [ | eassumption].
          apply /andP ; split ; [ | eassumption].
          eassumption.
      }
      2:{ rewrite fdisjointUr.
          rewrite fdisjointUr.
          apply /andP ; split ; [ | eassumption].
          apply /andP ; split ; [ | eassumption].
          eassumption.
      }

      unfold eq_up_to_inv.
      simplify_eq_rel inp_unit.

      repeat choice_type_eqP_handle.
      erewrite !cast_fun_K.
      fold chElement.

      simpl.

      ssprove_code_simpl.
      simpl.

      ssprove_sync=> xi.
      (* apply better_r_put_rhs. *)
      (* apply better_r_put_lhs. *)
      apply r_put_vs_put.

      ssprove_sync=> yi.

      apply r_put_vs_put.
      eapply (r_uniform_bij) with (f := (fun (x : Arit (uniform #|'Z_q|)) => fto (otf x + 1 )%R)) ; [ | intros zi ].
      1:{
        eapply (Bijective (g := (fun (x : Arit (uniform #|'Z_q|)) => fto (otf x - 1)%R))).
        {
          unfold cancel.
          intros.
          rewrite otf_fto.
          rewrite addrK.
          rewrite fto_otf.
          reflexivity.
        }
        {
          unfold cancel.
          intros.
          rewrite otf_fto.
          rewrite <- addrA.
          rewrite addNr.
          rewrite addr0.
          rewrite fto_otf.
          reflexivity.
        }
      }
      (* ssprove_sync=> xi2. (* GOTO HERE *) *)
      ssprove_sync=> a1.

(* (* g_pow_xi ← dl Datatypes.tt ;; *) *)
(*           '(g_pow_xi, g_pow_yi) ← ddh Datatypes.tt ;; *)
(*           zkp_i ← schnorr (WitnessToField (inv g_pow_xi), g_pow_xi) ;; *)
(*           (* g_pow_yi ← g_pow_yi_nz Datatypes.tt ;; *) *)
(*           let g_pow_yi : v_G := g_pow_yi in *)
(*           xi ← get_option DDH_loc1 erefl ;; *)
(*           g_pow_xy ← @ret v_G ((g_pow_yi : gT) ^+ (FieldToWitness xi)) ;; *)
(*           vote_i ← ret ((g_pow_xy : gT) * g^+(if vi then 1 else 0)%R)%g ;; *)
(*           commit ← commit_to vote_i ;; *)
(*           cds_i ← CDS ((g_pow_xi, g_pow_yi, vote_i), (xi, vi)) ;; *)
(*           ret (((zkp_i, g_pow_xi, commit, (cds_i : t_OrZKPCommit, vote_i))) : (((t_SchnorrZKPCommit × v_G) × v_Z) × (t_OrZKPCommit × v_G))%pack)). *)
      ssprove_sync=> a2.

      ssprove_same_head_generic.

      eapply r_get_remind_lhs.
      1:{
        unfold Remembers_lhs.
        intros.
        unfold rem_lhs.
        destruct H15 as [? []].
        destruct H15 as [? []].
        destruct H15 as [? []].
        destruct H15 as [? []].
        subst.
        rewrite get_set_heap_neq.
        1:{
          rewrite get_set_heap_eq.
          reflexivity.
        }
        apply /eqP.
        unfold DDH_loc2.
        clear.
        red ; intros.
        inversion H.
      }

      simpl.

      rewrite !FieldToWitnessCancel.
      rewrite !otf_fto.
      rewrite trunc_pow.
      rewrite expgD.
      (* rewrite mulg1. *)

      eapply r_get_remind_rhs.
      1:{
        unfold Remembers_rhs.
        intros.
        unfold rem_rhs.
        destruct H15 as [? []].
        destruct H15 as [? []].
        destruct H15 as [? []].
        destruct H15 as [? []].
        subst.
        rewrite get_set_heap_neq.
        1:{
          rewrite get_set_heap_eq.
          reflexivity.
        }
        apply /eqP.
        unfold DDH_loc2.
        clear.
        red ; intros.
        inversion H.
      }

      simpl.
      repeat choice_type_eqP_handle.

      apply (r_uniform_bij) with (f := fun x => x) ; [ now apply inv_bij | intros rand1 ].
      (* ssprove_sync=> ?. *)
      (* apply better_r_put_rhs. *)
      (* apply better_r_put_lhs. *)

      (* apply r_put_vs_put. *)
      apply (r_uniform_bij) with (f := fun x => x) ; [ now apply inv_bij | intros rand2 ].
      (* ssprove_sync=> ?. *)
      apply (r_uniform_bij) with (f := fun x => x) ; [ now apply inv_bij | intros rand3 ].
      apply (r_uniform_bij) with (f := fun x => x) ; [ now apply inv_bij | intros rand4 ].
      apply (r_uniform_bij) with (f := fun x => x) ; [ now apply inv_bij | intros rand5 ].

      (* GOTO HERE: (((zkp_i, g_pow_xi, commit, (cds_i : t_OrZKPCommit, vote_i))) : (((t_SchnorrZKPCommit × v_G) × v_Z) × (t_OrZKPCommit × v_G))%pack) *)
      
      apply r_ret.
      {
        intros.
        rewrite !trunc_pow.
        rewrite !mulg1.
        rewrite !expgD.

        split ; [ repeat rewrite pair_equal_spec ; repeat split | ].
        
        unfold heap_ignore.
        intros ℓ ?.

        destruct H15.
        destruct H15.
        destruct H15.
        destruct H15.
        destruct H15.
        destruct H15.
        destruct H15.
        destruct H15.
        subst.

        rewrite get_set_heap_neq.
        2:{ clear -H16.
            rename H16 into H.
            apply /eqP ; red ; intros.
            subst.
            unfold Schnorr_ZKP.Schnorr.MyAlg.Sigma_locs in H.
            rewrite <- !fset_cat in H.
            simpl in H.
            rewrite notin_fset in H.
            rewrite !notin_cons in H.
            repeat move: H => /andP [/eqP ? H].
            easy.
        }

        rewrite get_set_heap_neq.
        2:{ clear -H16.
            rename H16 into H.
            apply /eqP ; red ; intros.
            subst.
            unfold Schnorr_ZKP.Schnorr.MyAlg.Sigma_locs in H.
            rewrite <- !fset_cat in H.
            simpl in H.
            rewrite notin_fset in H.
            rewrite !notin_cons in H.
            repeat move: H => /andP [/eqP ? H].
            easy.
        }

        rewrite get_set_heap_neq.
        2:{ clear -H16.
            rename H16 into H.
            apply /eqP ; red ; intros.
            subst.
            unfold Schnorr_ZKP.Schnorr.MyAlg.Sigma_locs in H.
            rewrite <- !fset_cat in H.
            simpl in H.
            rewrite notin_fset in H.
            rewrite !notin_cons in H.
            repeat move: H => /andP [/eqP ? H].
            easy.
        }

        rewrite get_set_heap_neq.
        2:{ clear -H16.
            rename H16 into H.
            apply /eqP ; red ; intros.
            subst.
            unfold Schnorr_ZKP.Schnorr.MyAlg.Sigma_locs in H.
            rewrite <- !fset_cat in H.
            simpl in H.
            rewrite notin_fset in H.
            rewrite !notin_cons in H.
            repeat move: H => /andP [/eqP ? H].
            easy.
        }

        now apply H15.
      }

      (* easy. *)
    }
  Qed.


  Program Definition real_protocol (i : nat) (state : t_OvnContractState) (vi : 'bool) :
    package fset0
      [interface]
      [interface #val #[ FULL_PROTOCOL_INTERFACE ] : 'unit → chSingleProtocolTranscript ]
    :=
    [package
        #def #[ FULL_PROTOCOL_INTERFACE ] (_ : 'unit) : chSingleProtocolTranscript
        {
          xi ← sample (uniform #|'Z_q|) ;; let xi := WitnessToField (otf xi) : v_Z in
          ri ← sample (uniform #|'Z_q|) ;; let ri := WitnessToField (otf ri) in

          temp ← is_state (register_vote (ret_both ((i, xi, ri) : t_RegisterParam)) (ret_both state)) ;;
          state ← match temp : t_Result (v_A × t_OvnContractState) t_ParseError with
          | Result_Ok_case (_ , new_state) => ret new_state
          | Result_Err_case _ => ret (chCanonical t_OvnContractState)
            end ;;
          round_1 ←
              (zkp_i ← is_state (A := t_SchnorrZKPCommit) ((f_zkp_xis (ret_both (state : t_OvnContractState))).a[ ret_both (i : int32) ]) ;;
              g_pow_xi ← is_state (A := v_G) ((f_g_pow_xis (ret_both (state : t_OvnContractState))).a[ ret_both (i : int32) ]) ;;
              ret (zkp_i , g_pow_xi)) ;;
          (* TODO: allow modification of state *)

          temp ← is_state (commit_to_vote (ret_both ((i, xi, is_pure f_field_zero, is_pure f_field_zero, is_pure f_field_zero, vi) : t_CastVoteParam)) (ret_both (state : t_OvnContractState))) ;;
          state ← match temp : t_Result (v_A × t_OvnContractState) t_ParseError with
          | Result_Ok_case (_ , new_state) => ret new_state
          | Result_Err_case _ => ret (chCanonical t_OvnContractState)
            end ;;
          round_2 ← is_state (A := f_Z) ((f_commit_vis (ret_both (state : t_OvnContractState))).a[ ret_both (i : int32) ]) ;;
            (* TODO: allow modification of state *)

          w ← sample (uniform #|'Z_q|) ;; let w := WitnessToField (otf w) in
          r ← sample (uniform #|'Z_q|) ;; let r := WitnessToField (otf r) in
          d ← sample (uniform #|'Z_q|) ;; let d := WitnessToField (otf d) in
          temp ← is_state (cast_vote (ret_both ((i, xi, w, r, d, vi) : t_CastVoteParam)) (ret_both (state : t_OvnContractState))) ;;
          state ← match temp : t_Result (v_A × t_OvnContractState) t_ParseError with
          | Result_Ok_case (_ , new_state) => ret new_state
          | Result_Err_case _ => ret (chCanonical t_OvnContractState)
            end ;;
          round_3 ← (
              vote_i ← is_state (A := v_G) ((f_g_pow_xi_yi_vis (ret_both (state : t_OvnContractState))).a[ ret_both (i : int32) ]) ;;
              or_zkp_i ← is_state (A := t_OrZKPCommit) ((f_zkp_vis (ret_both (state : t_OvnContractState))).a[ ret_both (i : int32) ]) ;;
              ret (or_zkp_i, vote_i)) ;;
          (* TODO: allow modification of state *)

          ret ((round_1, round_2) , round_3)
        }
    ].
  Final Obligation.
    fold chElement in *.
    intros.
    ssprove_valid.
    all: try (apply valid_scheme ; rewrite <- fset0E ; apply (ChoiceEquality.is_valid_code (both_prog_valid _))).
    1: try destruct x0 , s.
    3: try destruct x3 , s.
    5: try destruct x6 , s.
    all: ssprove_valid.
  Qed.

  Lemma real_to_full_protocol_advantage :
    forall state (i : nat) vi,
      (Z.to_nat (unsigned (i : int32)) < from_uint_size (is_pure n))%coq_nat ->
    ∀ (LA : {fset Location}) (A : raw_package),
      ValidPackage LA [interface #val #[ FULL_PROTOCOL_INTERFACE ] : 'unit → chSingleProtocolTranscript ] A_export A →
      LA :#: fset [:: DL_loc] ->
      (AdvantageE
         (real_protocol i state vi)
         (full_protocol_interface state i vi ∘ par (DL_game false) (par schnorr_real (par (par (GPowYiNotZero_real i state) commit_real) cds_real)))
         A = 0)%R.
  Proof.
    intros state i vi i_lt_n ? ? ? H_disj_DL.
    intros.

    assert (trimmed_DL : forall b, trimmed [interface #val #[DL] : 'unit → chDLOutput ; #val #[DL_GUESS] : chDLInput → 'bool ] (DL_game b)).
    1:{
      intros.
      unfold trimmed.
      unfold trim.
      rewrite filterm_set.
      simpl ; fold chElement.

      rewrite in_fset.
      rewrite mem_head.
      simpl.

      setoid_rewrite filterm_set ; simpl ; fold chElement.
      rewrite in_fset.
      rewrite in_cons.
      rewrite mem_head.
      rewrite Bool.orb_true_r.

      rewrite filterm0.
      reflexivity.
    }
    pose (trimmed_DL false).
    pose (trimmed_DL true).

    (* trimmed_package (dl_real). *)
    (* trimmed_package (dl_ideal). *)
    (* trimmed_package (dl_random). *)

    trimmed_package (schnorr_real).
    trimmed_package (schnorr_ideal).
    trimmed_package (schnorr_ideal_no_assert).

    trimmed_package (GPowYiNotZero_real i state).
    trimmed_package (GPowYiNotZero_ideal (* i state *)).

    trimmed_package (commit_real).
    trimmed_package (commit_ideal).

    trimmed_package (cds_real).
    trimmed_package (cds_ideal).
    trimmed_package (cds_ideal_no_assert).

    pose proof (fpv := pack_valid (full_protocol_intantiated state i vi)).

    apply: eq_rel_perf_ind_ignore.
    1: (apply fsubsetxx || solve_in_fset || shelve).
    2: apply fdisjoints0.
    2: apply H_disj_DL.

    unfold eq_up_to_inv.
    simplify_eq_rel inp_unit.

    repeat choice_type_eqP_handle.
    erewrite !cast_fun_K.
    fold chElement.

    apply (r_uniform_bij) with (f := fun x => x) ; [ now apply inv_bij | intros xi ].
    apply better_r_put_rhs.

    apply better_r.
    eapply r_get_remind_rhs.
    1:{
      unfold Remembers_rhs.
      intros.
      unfold rem_rhs.
      destruct H10 as [? []].
      subst.
      rewrite get_set_heap_eq.
      1:{
        reflexivity.
      }
    }
    simpl.

    repeat choice_type_eqP_handle.
    erewrite !cast_fun_K.
    fold chElement.

    (* rewrite (bind_rewrite v_G _ (g ^+ FieldToWitness (WitnessToField (otf xi)))). *)
    (* simpl. *)

    replace (Schnorr_ZKP.Schnorr.MyParam.R _ _) with true ; [ | symmetry ].
    2:{
      unfold Schnorr_ZKP.Schnorr.MyParam.R.
      now rewrite eqxx.
    }
    simpl assertD.
    simpl.

    apply (r_uniform_bij) with (f := fun x => x) ; [ now apply inv_bij | intros ri ].

    (* Round 1 / Register vote *)
    unfold register_vote at 1.
    rewrite bind_assoc.
    rewrite bind_assoc.
    rewrite bind_rewrite.
    rewrite bind_assoc.
    rewrite bind_rewrite.
    simpl.
    rewrite bind_assoc.

    (* STUCK .. *)

    apply rpre_hypothesis_rule.
    intros.
    destruct H10 as [Ha Hb].
    destruct Hb as [Hc Hb].
    subst.
    eapply rpre_weaken_rule.
    2: shelve.

    apply somewhat_let_substitution.
    eapply rpre_weaken_rule.
    2: shelve.

    apply somewhat_substitution.
    rewrite bind_rewrite.
    apply somewhat_let_substitution.

    Unshelve.
    2:{
      intros ? ? ?.
      destruct H10.
      simpl in H11.
      subst.
      intros ? ?.
      rewrite get_set_heap_neq.
      2:{ clear -H10.
          rename H10 into H.
          apply /eqP ; red ; intros.
          subst.
          unfold Schnorr_ZKP.Schnorr.MyAlg.Sigma_locs in H.
          rewrite fset0U in H.
          rewrite notin_fset in H.
          rewrite !notin_cons in H.
          repeat move: H => /andP [/eqP ? H].
          easy.
      }

      now apply Hc.
    }
    2:{
      intros ? ? ?.
      intros ? ?.
      now apply H10.
    }

    progress repeat replace (f_rp_zkp_random _) with (ret_both (WitnessToField (otf ri))) by now apply both_eq.
    progress repeat replace (f_rp_xi _) with (ret_both (WitnessToField (otf xi))) by now apply both_eq.
    progress repeat replace (f_rp_i _) with (ret_both (i : int32)) by now apply both_eq.

    rewrite <- conversion_is_true.
    ssprove_same_head_generic.

    apply somewhat_let_substitution.
    apply somewhat_substitution.
    rewrite bind_rewrite.

    apply somewhat_let_substitution.
    apply somewhat_substitution.
    rewrite bind_rewrite.

    apply somewhat_let_substitution.
    apply somewhat_substitution.
    rewrite bind_rewrite.

    apply somewhat_let_substitution.
    apply somewhat_substitution.
    rewrite bind_rewrite.

    rewrite bind_assoc.
    rewrite bind_assoc.
    apply somewhat_substitution.
    rewrite bind_rewrite.
    simpl.

    rewrite bind_assoc.
    match goal with | |- context [ ⊢ ⦃ _ ⦄ bind (is_state ?a) ?f ≈ _ ⦃ _ ⦄ ] => apply (somewhat_substitution a f) end.

    repeat set (update_at_usize _ _ _).
    rewrite (hacspec_function_guarantees (fun x => array_index x _)).
    rewrite <- (hacspec_function_guarantees).
    (* rewrite (hacspec_function_guarantees (fun x => n_seq_array_or_seq x _)). *)

    eassert (forall state (v : both (nseq_ _ (from_uint_size (is_pure n)))), is_pure (f_zkp_xis (Build_t_OvnContractState [ state ] ( f_round1 := v))) = is_pure (f_zkp_xis state)).
    {
      clear ; intros.
      unfold f_zkp_xis at 1.
      unfold Build_t_OvnContractState at 1.
      simpl.
      reflexivity.
    }

    eassert (forall state (v : both (nseq_ _ (from_uint_size (is_pure n)))), is_pure (f_zkp_xis (Build_t_OvnContractState [ state ] ( f_zkp_xis := v))) = is_pure v).
    {
      clear ; intros.
      unfold f_zkp_xis at 1.
      unfold Build_t_OvnContractState at 1.
      simpl.
      reflexivity.
    }

    rewrite H10.
    rewrite H11.
    clear H10 H11.

    (* rewrite <- (hacspec_function_guarantees (fun x => n_seq_array_or_seq x _)). *)
    (* rewrite <- (hacspec_function_guarantees (fun x => array_index x _)). *)

    subst b0.
    replace (cast_int (ret_both i)) with (ret_both (i : int32)).
    2:{ apply both_eq.
        simpl.
        unfold cast_int at 1, lift1_both at 1, bind_both, bind_raw_both.
        simpl.
        rewrite wrepr_unsigned.
        reflexivity.
    }

    set (f_zkp_xis _).
    (* epose (strip_nseq_array_or_seq i). *)
    (* rewrite <- e. *)

    setoid_rewrite (array_update_eq b0 (ret_both a) i i_lt_n).
    subst b0.
    simpl.

    rewrite bind_assoc.

    repeat set (update_at_usize _ _ _).
    Misc.pattern_rhs_approx.
    match goal with | |- context [ ⊢ ⦃ _ ⦄ bind _ ?f ≈ _ ⦃ _ ⦄ ] => set f end.

    apply somewhat_substitution.

    rewrite (hacspec_function_guarantees (fun x => array_index x _)).
    rewrite <- hacspec_function_guarantees.

      eassert (forall state (v : both (nseq_ _ (from_uint_size (is_pure n)))),
                  is_pure (f_g_pow_xis (Build_t_OvnContractState [ state ] ( f_g_pow_xis := v)))
                  = is_pure v).
      {
        clear ; intros.
        unfold f_g_pow_xis at 1.
        unfold Build_t_OvnContractState at 1.
        simpl.
        reflexivity.
      }

      eassert (forall state (v : both (nseq_ _ (from_uint_size (is_pure n)))),
                  is_pure (f_g_pow_xis (Build_t_OvnContractState [ state ] ( f_zkp_xis := v)))
                  =
                    is_pure (f_g_pow_xis (state))).
      {
        clear ; intros.
        unfold f_g_pow_xis at 1.
        unfold Build_t_OvnContractState at 1.
        simpl.
        reflexivity.
      }

      eassert (forall state (v : both (nseq_ _ (from_uint_size (is_pure n)))),
                  is_pure (f_g_pow_xis (Build_t_OvnContractState [ state ] ( f_round1 := v)))
                  = is_pure (f_g_pow_xis (state))).
      {
        clear ; intros.
        unfold f_g_pow_xis at 1.
        unfold Build_t_OvnContractState at 1.
        simpl.
        reflexivity.
      }

      rewrite H13.
      rewrite H12.
      rewrite H11.
      clear H11 H12 H13.


    rewrite <- (hacspec_function_guarantees (fun x => array_index x _)).
    subst b.
    replace (cast_int (ret_both i)) with (ret_both (i : int32)).
    2:{ apply both_eq.
        simpl.
        unfold cast_int at 1, lift1_both at 1, bind_both, bind_raw_both.
        simpl.
        rewrite wrepr_unsigned.
        reflexivity.
    }

    setoid_rewrite (array_update_eq _ (ret_both _) i i_lt_n).
    rewrite bind_rewrite.
    subst r H10.
    hnf.
    rewrite bind_rewrite.

    (* Round 2 / commit_to_vote *)
    unfold commit_to_vote at 1.

    rewrite bind_assoc.
    rewrite bind_assoc.
    rewrite bind_rewrite.
    rewrite bind_assoc.
    rewrite bind_rewrite.
    simpl.
    rewrite bind_assoc.

    apply somewhat_let_substitution.
    apply somewhat_substitution.
    rewrite bind_rewrite.

    apply somewhat_let_substitution.

    progress repeat replace (f_cvp_xi _) with (ret_both (WitnessToField (otf xi))) by now apply both_eq.
    progress repeat replace (f_cvp_vote _) with (ret_both (vi : 'bool)) by now apply both_eq.
    progress repeat replace (f_cvp_i _) with (ret_both (i : int32)) by now apply both_eq.

    apply somewhat_substitution.
    rewrite (hacspec_function_guarantees (compute_g_pow_yi _)).

    eassert (forall state (v : both (nseq_ _ (from_uint_size (is_pure n)))),
                is_pure (f_g_pow_xis (Build_t_OvnContractState [ state ] ( f_g_pow_xis := v)))
                = is_pure v).
    {
      clear ; intros.
      unfold f_g_pow_xis at 1.
      unfold Build_t_OvnContractState at 1.
      simpl.
      reflexivity.
    }

    eassert (forall state (v : both (nseq_ _ (from_uint_size (is_pure n)))),
                is_pure (f_g_pow_xis (Build_t_OvnContractState [ state ] ( f_zkp_xis := v)))
                =
                  is_pure (f_g_pow_xis (state))).
    {
      clear ; intros.
      unfold f_g_pow_xis at 1.
      unfold Build_t_OvnContractState at 1.
      simpl.
      reflexivity.
    }

    eassert (forall state (v : both (nseq_ _ (from_uint_size (is_pure n)))),
                is_pure (f_g_pow_xis (Build_t_OvnContractState [ state ] ( f_round1 := v)))
                = is_pure (f_g_pow_xis (state))).
    {
      clear ; intros.
      unfold f_g_pow_xis at 1.
      unfold Build_t_OvnContractState at 1.
      simpl.
      reflexivity.
    }

    rewrite H12.
    rewrite H11.
    rewrite H10.
    clear H10 H11 H12.
    replace (cast_int (ret_both i)) with (ret_both (i : int32)).
    2:{ apply both_eq.
        simpl.
        unfold cast_int at 1, lift1_both at 1, bind_both, bind_raw_both.
        simpl.
        rewrite wrepr_unsigned.
        reflexivity.
    }

    rewrite <- hacspec_function_guarantees.
    rewrite compute_g_pow_yi_update_eq. 2: apply i_lt_n.
    rewrite bind_rewrite.

    apply somewhat_let_substitution.
    (* ssprove_same_head a0. *)
    apply somewhat_substitution.
    rewrite bind_rewrite.
    rewrite (bind_assoc (is_state (compute_g_pow_yi _ _))).
    apply somewhat_substitutionR.
    set (a0 := (is_pure (compute_g_pow_yi (ret_both i) (f_g_pow_xis (ret_both _))))).
    rewrite !bind_rewrite.

    apply somewhat_let_substitution.
    unfold commit_to at 1.
    eapply r_bind_feq_alt.
    {
      rewrite bind_ret.
      rewrite !FieldToWitnessCancel.
      set (s := is_pure _).
      set (s0 := (_ * _)%g).
      assert (s = s0) ; subst s s0.
      {
        unfold compute_group_element_for_vote at 1.

        (* rewrite mulrC. *)
        (* rewrite trunc_pow. *)
        (* rewrite expgM. *)
        (* rewrite inv_is_inv. *)

        Misc.push_down_sides.
        rewrite <- pow_witness_to_field.
        rewrite <- conversion_is_true.
        destruct vi ; [ rewrite rmorph1 | rewrite rmorph0 ] ; reflexivity.
      }
      rewrite H10.
      apply (r_reflexivity_alt (L := fset0)) ; [ ssprove_valid | easy | easy ].
      all: try (apply valid_scheme ; rewrite <- fset0E ; apply (ChoiceEquality.is_valid_code (both_prog_valid _))).
    }
    intros.
    apply somewhat_substitution.
    rewrite !bind_rewrite.
    (* apply somewhat_substitution. *)
    (* rewrite !bind_rewrite. *)
    simpl.

    (* Round 3 / cast_vote *)

    unfold cast_vote at 1.

    rewrite !eqxx.
    (* replace (_ == _) with true ; [ | symmetry]. *)
    (* 2:{ *)
    (*   rewrite !FieldToWitnessCancel. *)
    (*   rewrite mulrC. *)
    (*     rewrite trunc_pow. *)
    (*     rewrite expgM. *)
    (*     rewrite inv_is_inv. *)
    (*     destruct vi ; now rewrite eqxx. *)
    (* } *)
    simpl assertD.
    simpl.

    apply (r_uniform_bij) with (f := fun x => x) ; [ now apply inv_bij | intros w ].
    apply (r_uniform_bij) with (f := fun x => x) ; [ now apply inv_bij | intros r ].
    apply (r_uniform_bij) with (f := fun x => x) ; [ now apply inv_bij | intros d ].

    rewrite bind_assoc.
    rewrite bind_assoc.
    rewrite bind_rewrite.

    rewrite bind_assoc.
    rewrite bind_assoc.
    rewrite bind_assoc.
    simpl.

    rewrite bind_assoc.
    apply somewhat_let_substitution.
    apply somewhat_substitution.
    rewrite bind_rewrite.
    apply somewhat_let_substitution.

    progress repeat replace (f_cvp_xi _) with (ret_both (WitnessToField (otf xi))) by now apply both_eq.
    progress repeat replace (f_cvp_zkp_random_w _) with (ret_both (WitnessToField (otf w))) by now apply both_eq.
    progress repeat replace (f_cvp_zkp_random_r _) with (ret_both (WitnessToField (otf r))) by now apply both_eq.
    progress repeat replace (f_cvp_zkp_random_d _) with (ret_both (WitnessToField (otf d))) by now apply both_eq.
    progress repeat replace (f_cvp_vote _) with (ret_both (vi : 'bool)) by now apply both_eq.
    progress repeat replace (f_cvp_i _) with (ret_both (i : int32)) by now apply both_eq.

    set (ret_both (is_pure _)).
    apply r_bind_feq_alt.
    {
      replace b with (ret_both a0) ; subst a0 b.
      2:{
        symmetry.
        repeat set (update_at_usize _ _ _).
        f_equal.

        replace (cast_int (ret_both i)) with (ret_both (i : int32)).
        2:{ apply both_eq.
            simpl.
            unfold cast_int at 1, lift1_both at 1, bind_both, bind_raw_both.
            simpl.
            rewrite wrepr_unsigned.
            reflexivity.
        }

        rewrite hacspec_function_guarantees.

        eassert (forall state (v : both (nseq_ _ (from_uint_size (is_pure n)))),
                    is_pure (f_g_pow_xis (Build_t_OvnContractState [ state ] ( f_g_pow_xis := v)))
                    = is_pure v).
        {
          clear ; intros.
          unfold f_g_pow_xis at 1.
          unfold Build_t_OvnContractState at 1.
          simpl.
          reflexivity.
        }

        eassert (forall state (v : both (nseq_ _ (from_uint_size (is_pure n)))),
                    is_pure (f_g_pow_xis (Build_t_OvnContractState [ state ] ( f_zkp_xis := v)))
                    =
                      is_pure (f_g_pow_xis (state))).
        {
          clear ; intros.
          unfold f_g_pow_xis at 1.
          unfold Build_t_OvnContractState at 1.
          simpl.
          reflexivity.
        }

        eassert (forall state (v : both (nseq_ _ (from_uint_size (is_pure n)))),
                    is_pure (f_g_pow_xis (Build_t_OvnContractState [ state ] ( f_round1 := v)))
                    = is_pure (f_g_pow_xis (state))).
        {
          clear ; intros.
          unfold f_g_pow_xis at 1.
          unfold Build_t_OvnContractState at 1.
          simpl.
          reflexivity.
        }

        eassert (forall state (v : both (nseq_ _ (from_uint_size (is_pure n)))),
                    is_pure (f_g_pow_xis (Build_t_OvnContractState [ state ] ( f_commit_vis := v)))
                    = is_pure (f_g_pow_xis (state))).
        {
          clear ; intros.
          unfold f_g_pow_xis at 1.
          unfold Build_t_OvnContractState at 1.
          simpl.
          reflexivity.
        }

        rewrite H13.
        rewrite H12.
        rewrite H11.
        rewrite H10.
        clear H10 H11 H12 H13.

        subst b.
        rewrite <- hacspec_function_guarantees.
        rewrite compute_g_pow_yi_update_eq. 2: apply i_lt_n.
        reflexivity.
      }
      apply (r_reflexivity_alt (L := fset0)).
      1: apply valid_scheme ; rewrite <- fset0E ; apply (ChoiceEquality.is_valid_code (both_prog_valid _)).
      1,2:easy.
    }
    intros.

    apply somewhat_let_substitution.
    apply somewhat_substitution.
    rewrite bind_rewrite.

    apply somewhat_let_substitution.
    apply somewhat_substitution.
    rewrite bind_rewrite.

    apply somewhat_let_substitution.
    apply somewhat_substitution.
    rewrite bind_rewrite.

    apply somewhat_let_substitution.
    apply somewhat_substitution.
    rewrite bind_rewrite.

    rewrite bind_assoc.
    rewrite bind_assoc.
    apply somewhat_substitution.
    rewrite bind_rewrite.
    simpl.

    rewrite bind_assoc.
    apply somewhat_substitution.

    clear -i_lt_n.

    eapply r_transL.
    {
      apply r_bind_feq.
      {
        apply r_ret.
        intros.

        rewrite pair_equal_spec ; split ; [ | subst ; easy ].

        repeat set (update_at_usize _ _ _).
        rewrite (hacspec_function_guarantees (fun x => array_index x _)).
        rewrite <- (hacspec_function_guarantees f_g_pow_xi_yi_vis).

        eassert (forall state (v : both (nseq_ _ (from_uint_size (is_pure n)))),
                    is_pure (f_g_pow_xi_yi_vis (Build_t_OvnContractState [ state ] ( f_zkp_vis := v)))
                    = is_pure (f_g_pow_xi_yi_vis (state))).
        {
          clear ; intros.
          unfold f_g_pow_xis at 1.
          unfold Build_t_OvnContractState at 1.
          simpl.
          reflexivity.
        }
        rewrite H0 ; clear H0.
        simpl.

        eassert (forall state (v : both (nseq_ _ (from_uint_size (is_pure n)))),
                    is_pure (f_g_pow_xi_yi_vis (Build_t_OvnContractState [ state ] ( f_g_pow_xi_yi_vis := v)))
                    = is_pure v).
        {
          clear ; intros.
          unfold f_g_pow_xis at 1.
          unfold Build_t_OvnContractState at 1.
          simpl.
          reflexivity.
        }
        rewrite H0 ; clear H0.

        subst b4.
        rewrite <- (hacspec_function_guarantees (fun x => array_index x _)).

        replace (cast_int (ret_both i)) with (ret_both (i : int32)).
        2:{ apply both_eq.
            simpl.
            unfold cast_int at 1, lift1_both at 1, bind_both, bind_raw_both.
            simpl.
            rewrite wrepr_unsigned.
            reflexivity.
        }

        setoid_rewrite (array_update_eq _ (ret_both _) i i_lt_n).
        simpl.
        reflexivity.
      }
      intros.
      apply rreflexivity_rule.
    }
    rewrite bind_rewrite.

    rewrite bind_assoc.
    match goal with | |- context [ ⊢ ⦃ _ ⦄ bind (is_state ?a) ?f ≈ _ ⦃ _ ⦄ ] => apply (somewhat_substitution a f) end.

    eapply r_transL.
    {
      apply r_bind_feq.
      {
        apply r_ret.
        intros.

        rewrite pair_equal_spec ; split ; [ | subst ; easy ].

        repeat set (update_at_usize _ _ _).
        rewrite (hacspec_function_guarantees (fun x => array_index x _)).
        rewrite <- (hacspec_function_guarantees f_zkp_vis).

        eassert (forall state (v : both (nseq_ _ (from_uint_size (is_pure n)))),
                    is_pure (f_zkp_vis (Build_t_OvnContractState [ state ] ( f_zkp_vis := v)))
                    = is_pure v).
        {
          clear ; intros.
          unfold f_g_pow_xis at 1.
          unfold Build_t_OvnContractState at 1.
          simpl.
          reflexivity.
        }
        rewrite H0 ; clear H0.
        rewrite <- (hacspec_function_guarantees (fun x => array_index x _)).
        simpl.

        subst b5.
        replace (cast_int (ret_both i)) with (ret_both (i : int32)).
        2:{ apply both_eq.
            simpl.
            unfold cast_int at 1, lift1_both at 1, bind_both, bind_raw_both.
            simpl.
            rewrite wrepr_unsigned.
            reflexivity.
        }

        setoid_rewrite (array_update_eq _ (ret_both _) i i_lt_n).
        simpl.
        reflexivity.
      }
      intros.
      apply rreflexivity_rule.
    }
    rewrite bind_rewrite.
    rewrite bind_rewrite.
    apply r_ret.
    intros.
    split ; [ | easy ].

    repeat rewrite pair_equal_spec ; repeat split.
    {
      simpl.
      clear -i_lt_n.
      repeat set (update_at_usize _ _ _).
      unfold Build_t_OvnContractState at 1 ; simpl.
      subst b2.

      setoid_rewrite (array_update_eq _ (ret_both _) i i_lt_n).
      reflexivity.
    }
    {
      unfold compute_group_element_for_vote at 1.
      rewrite !FieldToWitnessCancel.
      (* rewrite mulrC. *)
      (* rewrite trunc_pow. *)
      (* rewrite expgM. *)
      (* rewrite inv_is_inv. *)

        simpl.
        (* rewrite hacspec_function_guarantees2. *)
        (* rewrite (hacspec_function_guarantees2 f_pow). *)
        subst b.

        replace (cast_int (ret_both i)) with (ret_both (i : int32)).
        2:{ apply both_eq.
            simpl.
            unfold cast_int at 1, lift1_both at 1, bind_both, bind_raw_both.
            simpl.
            rewrite wrepr_unsigned.
            reflexivity.
        }


        rewrite hacspec_function_guarantees.

        eassert (forall state (v : both (nseq_ _ (from_uint_size (is_pure n)))),
                    is_pure (f_g_pow_xis (Build_t_OvnContractState [ state ] ( f_g_pow_xis := v)))
                    = is_pure v).
        {
          clear ; intros.
          unfold f_g_pow_xis at 1.
          unfold Build_t_OvnContractState at 1.
          simpl.
          reflexivity.
        }

        eassert (forall state (v : both (nseq_ _ (from_uint_size (is_pure n)))),
                    is_pure (f_g_pow_xis (Build_t_OvnContractState [ state ] ( f_zkp_xis := v)))
                    =
                      is_pure (f_g_pow_xis (state))).
        {
          clear ; intros.
          unfold f_g_pow_xis at 1.
          unfold Build_t_OvnContractState at 1.
          simpl.
          reflexivity.
        }

        eassert (forall state (v : both (nseq_ _ (from_uint_size (is_pure n)))),
                    is_pure (f_g_pow_xis (Build_t_OvnContractState [ state ] ( f_round1 := v)))
                    = is_pure (f_g_pow_xis (state))).
        {
          clear ; intros.
          unfold f_g_pow_xis at 1.
          unfold Build_t_OvnContractState at 1.
          simpl.
          reflexivity.
        }

        eassert (forall state (v : both (nseq_ _ (from_uint_size (is_pure n)))),
                    is_pure (f_g_pow_xis (Build_t_OvnContractState [ state ] ( f_commit_vis := v)))
                    = is_pure (f_g_pow_xis (state))).
        {
          clear ; intros.
          unfold f_g_pow_xis at 1.
          unfold Build_t_OvnContractState at 1.
          simpl.
          reflexivity.
        }

        rewrite (hacspec_function_guarantees (compute_g_pow_yi (ret_both i))).
        rewrite H3.
        rewrite H2.
        rewrite H1.
        rewrite H0.
        clear H0 H1 H2 H3.
        rewrite <- (hacspec_function_guarantees (compute_g_pow_yi (ret_both i))).

        rewrite compute_g_pow_yi_update_eq. 2: apply i_lt_n.
        Misc.push_down_sides.
        rewrite <- pow_witness_to_field.
        rewrite <- conversion_is_true.
        destruct vi ; [ rewrite rmorph1 | rewrite rmorph0 ] ; reflexivity.
    }
   Qed. (* Fail Timeout 5 Qed. Admitted. (* 319.394 secs *) *)

  Lemma real_protocol_is_maximum_balloc_secrecy_hiding :
    forall state (i : nat),
      (Z.to_nat (unsigned (i: int32)) < from_uint_size (is_pure n))%coq_nat ->
    ∀ (LA : {fset Location}) (A : raw_package),
      ValidPackage LA [interface #val #[ FULL_PROTOCOL_INTERFACE ] : 'unit → chSingleProtocolTranscript ] A_export A →
      LA :#: Schnorr_ZKP.Schnorr.MyAlg.Sigma_locs ->
      LA :#: Schnorr_ZKP.Schnorr.MyAlg.Simulator_locs ->
      LA :#: OR_ZKP.proof_args.MyAlg.Sigma_locs ->
      LA :#: fset [:: DL_loc] ->
      LA :#: fset [:: DDH_loc1; DDH_loc2] ->
    forall (ϵ : _),
    (forall P, ϵ_DL P <= ϵ)%R →
    forall (ψ : _),
    (forall P, ϵ_COMMIT P <= ψ)%R ->
    forall (ν : _),
    (forall P, ϵ_GPOWYINOTZERO i state P <= ν)%R →
    forall (ζ : _),
    (forall P, ϵ_DDH P <= ζ)%R →
    (AdvantageE
       (real_protocol i state true)
       (real_protocol i state false) A <= ((ψ + ν) + (ϵ + ζ)) + ((ψ + ν) + (ϵ + ζ)))%R.
  Proof.
    intros.

    (* Close in from the left *)
    eapply Order.le_trans ; [ eapply Advantage_triangle with (R := _) | ].

    replace (AdvantageE _ _ _) with (@GRing.zero R) ; [ rewrite add0r | symmetry ] ; revgoals.

    1: eapply (real_to_full_protocol_advantage state i true H) ; eassumption.

    rewrite Advantage_sym.

    eapply Order.le_trans ; [ eapply Advantage_triangle with (R := _) | ].

    replace (AdvantageE _ _ _) with (@GRing.zero R) ; [ rewrite add0r | symmetry ] ; revgoals.
    1: eapply (real_to_full_protocol_advantage state i false) ; eassumption.

    rewrite Advantage_sym.

    eapply all_step_advantage ; try eassumption.
  Qed.

  (*** /Solution *)

End OVN_proof.
