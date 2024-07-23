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
  (* Module Schnorr_ZKP := OVN_schnorr_proof HOP HOGaFP HOGaFE HGPA. *)
  (* Module OR_ZKP := OVN_or_proof HOP HOGaFP HOGaFE HGPA. *)

  (* Import Schnorr_ZKP. *)
  (* Import OR_ZKP. *)

  Include HGPA.

  From OVN Require Import OVN.

  Module OVN_GroupParam <: OVN.GroupParam.

    Definition n : nat := 55.
    Lemma n_pos : Positive n. Proof. easy. Qed.

    Include HacspecGroup.
  End OVN_GroupParam.

  Module OVN_Param <: OVNParam.
    Definition N : nat := 55.
    Lemma N_pos : Positive N. Proof. easy. Qed.
  End OVN_Param.

  Module OVN_proofs := OVN OVN_GroupParam OVN_Param.

  Module OVN_or <: OVN_proofs.CDSParams(* SigmaProtocolParams *).

    Definition Witness : finType := OVN_proofs.Secret.
    Definition Statement : finType := prod (prod OVN_proofs.Public OVN_proofs.Public) OVN_proofs.Public.
    Definition Message : finType :=  prod (prod (prod gT gT) gT) gT.
    Definition Challenge : finType := Finite.clone _ 'Z_q.
    Definition Response : finType :=  (prod (prod (prod (Finite.clone _ 'Z_q) (Finite.clone _ 'Z_q)) (Finite.clone _ 'Z_q)) (Finite.clone _ 'Z_q)).

    Definition w0 : Witness := 0%R.
    Definition e0 : Challenge := 0%R.
    Definition z0 : Response := 0%R.

    (* * OR relation *)
    Definition R : Statement -> Witness -> bool :=
      (λ (h : Statement) (x : Witness),
        let '(gx, gy, gyxv) := h in
        (gy^+x * g^+0 == gyxv) || (gy^+x * g^+1 == gyxv))%g.

    (* begin details : Sanity checks *)
    Lemma relation_valid_left:
      (∀ (x : OVN_proofs.Secret) (gy : OVN_proofs.Public),
        R (g^+x, gy, gy^+x * g^+ 0) x)%g.
    Proof.
      intros x gy.
      unfold R.
      apply /orP ; left.
      done.
    Qed.

    Lemma relation_valid_right:
      (∀ (x : OVN_proofs.Secret) (gy : OVN_proofs.Public),
          R (g^+x, gy, gy^+x * g^+ 1) x)%g.
    Proof.
      intros x y.
      unfold R.
      apply /orP ; right.
      done.
    Qed.
    (* end details *)

    (* begin details : size of protocol elements is positive *)
    Instance Witness_pos : Positive #|Witness| := OVN_proofs.Secret_pos.
    Definition Statement_pos : Positive #|Statement| := _.
    Definition Message_pos : Positive #|Message| := _.
    Definition Challenge_pos : Positive #|Challenge| := _.
    Definition Response_pos : Positive #|Response| := _.
    Definition Bool_pos : Positive #|'bool| := _.

    Definition State : finType := 'unit.
    Instance State_pos : Positive #|State| := eq_ind_r [eta Positive] (erefl : Positive 1) card_unit.
    (* end details *)
  End OVN_or.

  Module OVN_or_alg <: SigmaProtocolAlgorithms OVN_or.

    Import OVN_or.

    (* begin details : define (choice) type from size of protocol elements *)
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
    (* end details *)

    Definition HIDING : nat := 0.
    Definition SOUNDNESS : nat := 1.

    Definition commit_loc : Location := (('fin #|Finite.clone _ 'Z_q| × 'fin #|Finite.clone _ 'Z_q| × 'fin #|Finite.clone _ 'Z_q| : choice_type); 2%N).

    Definition Sigma_locs : {fset Location} := fset [:: commit_loc].
    Definition Simulator_locs : {fset Location} := fset0.

    (** Actual code for protocol, validator, simulator and extractor and key gen *)
    Definition Commit (hy : choiceStatement) (xv : choiceWitness):
      code Sigma_locs [interface] choiceMessage :=
      {code
         w ← sample uniform i_witness ;;
       d ← sample uniform i_witness ;;
       r ← sample uniform i_witness ;;
       #put commit_loc := (w, r, d) ;;
                          let '(x, h, y) := (otf hy) in
                          let m (* '(m, v, _) *) := (otf xv) in
                          if (y == h^+m * g)
                          then
                            (
                              let r1 := r in
                              let d1 := d in

                              let a1 := (g ^+ (otf r1 : 'Z_q) * x ^+ (otf d1 : 'Z_q))%g in
                              let b1 := (h ^+ (otf r1 : 'Z_q) * y ^+ (otf d1 : 'Z_q))%g in

                              let a2 := (g ^+ (otf w : 'Z_q))%g in
                              let b2 := (h ^+ (otf w : 'Z_q))%g in
                              ret (fto (a1, b1, a2, b2)))
                          else
                            (let r2 := r in
                             let d2 := d in

                             let a1 := (g ^+ (otf w : 'Z_q))%g in
                             let b1 := (h ^+ (otf w : 'Z_q))%g in

                             let a2 := (g ^+ (otf r2 : 'Z_q) * x ^+ (otf d2 : 'Z_q))%g in
                             let b2 := (h ^+ (otf r2 : 'Z_q) * (y * g^-1) ^+ (otf d2 : 'Z_q))%g in
                             ret (fto (a1, b1, a2, b2)))
      }%g.

    Definition Verify (xhy : choiceStatement) (a : choiceMessage)
      (c : choiceChallenge) (z : choiceResponse) : choiceBool :=
      let '(x, h, y) := otf xhy in
      let '(a1, b1, a2, b2) := (otf a) in
      let '(r1, d1, r2, d2) := (otf z) in
      fto ((otf c == d1 + d2)%R &&
             (a1 == (g ^+ r1) * (x ^+ d1)) &&
             (b1 == (h ^+ r1) * (y ^+ d1)) &&
             (a2 == (g ^+ r2) * (x ^+ d2)) &&
             (b2 == (h ^+ r2) * ((y * (g ^-1)) ^+ d2)))%g.


    Definition Response (xhy : choiceStatement) (xv : choiceWitness) (_ : choiceMessage) (c : choiceChallenge) :
      code Sigma_locs [interface] choiceResponse :=
      {code
         '(w, r, d) ← get commit_loc ;;
       let '(x, h, y) := (otf xhy) in
       let m (* '(m, v, _) *) := (otf xv) in
       if (* v *) y == h ^+ m * g
       then
         (let d2 := (otf c - otf d) in
          let r2 := (otf w - (m * d2)) in
          ret (fto (otf r, otf d, r2, d2)))%R
       else
         (let d1 := (otf c - otf d) in
          let r1 := (otf w - (m * d1)) in
          ret (fto (r1, d1, otf r, otf d)))%R
      }%g.

    Definition Simulate (xhy : choiceStatement) (c : choiceChallenge) :
      code Simulator_locs [interface] choiceTranscript :=
      {code
         d ← sample uniform i_witness ;;
       r ← sample uniform i_witness ;;
       r_other ← sample uniform i_witness ;;
       let '(x, h, y) := otf xhy in
       let d2 := otf d in
       let r2 := otf r in
       let r1 := otf r_other in
       let d1 := (otf c - d2)%R in
       let a1 := (g ^+ r1 * x ^+ d1)%g in
       let b1 := (h ^+ r1 * y ^+ d1)%g in
       let a2 := (g ^+ r2 * x ^+ d2)%g in
       let b2 := (h ^+ r2 * (y * invg g) ^+ d2)%g in
       ret (xhy , fto (a1,b1,a2,b2), c , fto (r1,d1,r2,d2))
      }.

    Definition Extractor (xhy : choiceStatement) (a : choiceMessage)
      (c : choiceChallenge) (c' : choiceChallenge)
      (z : choiceResponse)  (z' : choiceResponse) : 'option choiceWitness :=
      let '(
              (x, h, y),
              (a1, b1, a2, b2),
              (r1,d1,r2,d2),
              (r1',d1',r2',d2')
            ) :=
        (otf xhy, otf a, otf z, otf z') in

      let m := if (d1 - d1' != 0)%R
               then ((r1' - r1) / (d1 - d1'))%R
               else ((r2' - r2) / ((d2 - d2')))%R in
      (* let v := ~~ (d1 - d1' != 0)%R (* y == h ^+ m * g *) in *)
      Some (fto (m(* , v, h *))).
    Fail Next Obligation.

    Definition KeyGen (xv : choiceWitness) :=
      let '(m(* , v, h *)) := otf xv in
      fto (g, g, g).
      (* fto (g ^+ m, h ^+ m, h ^+ m * g ^+ v)%g. *)

  End OVN_or_alg.

  Module OVN_old_proofs := OVN_proofs.OVN OVN_or OVN_or_alg.

  Check OVN_old_proofs.Exec_i_realised_code_runnable.
  

  Notation " 'chInpOvn' " :=
    ('bool)
    (in custom pack_type at level 2).

  Notation " 'chOut' " :=
    ((OVN_proofs.public))
    (in custom pack_type at level 2).

  Definition MAXIMUM_BALLOT_SECRECY : nat := 12.
        (* ('bool, OVN_proofs.public) *)

  Program Definition maximum_ballot_secrecy_ovn (cvp_i : int32) (cvp_xi : f_Z) (cvp_vote : 'bool) (state : both t_OvnContractState) :
    package
      (fset [::])
      [interface]
      [interface #val #[ (15 + (unsigned cvp_i))%nat ] : chInpOvn → chOut ]
    :=
    [package
       #def #[ (15 + (unsigned cvp_i))%nat ] (_ : chInpOvn) : chOut
      {
        (* Setup and inputs for algorithm *)
        cvp_zkp_random_w ← sample (uniform #|'Z_q|) ;;
        cvp_zkp_random_d ← sample (uniform #|'Z_q|) ;;
        cvp_zkp_random_r ← sample (uniform #|'Z_q|) ;;

        let ctx := prod_b (
                       ret_both cvp_i,
                       ret_both cvp_xi,
                       ret_both (WitnessToField (otf cvp_zkp_random_w : 'Z_q)),
                       ret_both (WitnessToField (otf cvp_zkp_random_r : 'Z_q)),
                       ret_both (WitnessToField (otf cvp_zkp_random_d : 'Z_q)),
                       ret_both (cvp_vote : 'bool)
                     ) : both t_CastVoteParam in

        temp ← is_state (cast_vote (ctx) (state : both t_OvnContractState)) ;;
        ret (fto (is_pure f_group_one : gT))
        (* match temp : t_Result (v_A × t_OvnContractState) _ with *)
        (* | Result_Ok_case (_, s) => ret None *)
        (*     (* temp ← is_state ((f_g_pow_xis s).a[ret_both cvp_i]) ;; *) *)
        (*     (* ret (Some temp) *) *)
        (* | Result_Err_case _ => ret None *)
        (* end *)
    }].
  Next Obligation.
    intros.
    eapply (valid_package_cons _ _ _ _ _ _ [] []).
    - apply valid_empty_package.
    - intros ?.
      simpl.
      rewrite <- !fset0E.
      ssprove_valid'_2.
      all: try apply (ChoiceEquality.is_valid_code (both_prog_valid _)).
      all: repeat (apply valid_sampler ; intros).
      all: repeat (rewrite !otf_fto ; ssprove_valid'_2).
      all: ssprove_valid'_2.
      all: try (apply (valid_injectMap (I1 := fset0)) ; [ apply fsub0set | rewrite <- fset0E ]).
      all: try apply (ChoiceEquality.is_valid_code (both_prog_valid _)).
      all: repeat (apply valid_sampler ; intros).
      all: try rewrite <- !fset0E.
    - unfold "\notin".
      rewrite <- !fset0E.
      rewrite imfset0.
      rewrite in_fset0.
      easy.
  Qed.
  Fail Next Obligation.

  Program Definition hacspec_args_old_ovn_pkg (cvp_i : int32) (cvp_xi : f_Z) (cvp_vote : 'bool) (state : both t_OvnContractState) (j : OVN_proofs.pid) (schnorr_r : v_G) : package _ [interface] _ :=
    (OVN_old_proofs.Exec_i_realised cvp_vote
         (mkfmapf
            (fun n =>
               let ni := ret_both (Hacspec_Lib_Pre.repr U32 (nat_of_ord (otf n)) : uint_size) in
               (fto (is_pure ((f_g_pow_xis state).a[ ni ]) : v_G_type),
                 let '(r1, r2, r3) := (is_pure ((f_zkp_xis state).a[ ni ]) : t_SchnorrZKPCommit) in
                 (fto (schnorr_r : v_G_type),
                   fto (r1 : v_G_type) ,
                   fto (FieldToWitness r2) ,
                   fto (FieldToWitness r3)))
            )
            (seq.map (fun n => fto (inZp n)) (iota 0 (55))))
         (fto (inZp (unsigned cvp_i)))
         j).
  Solve All Obligations with now intros ; destruct from_uint_size.
  Fail Next Obligation.

  Lemma maximum_ballot_secrecy_old : forall (cvp_i : int32) (cvp_xi : f_Z) (cvp_vote : 'bool) (state : both t_OvnContractState) (j : OVN_proofs.pid) (schnorr_r : v_G) (H_cvp_i : (unsigned cvp_i < 55)%N),
    ∀ (LA : {fset Location}) A,
      ValidPackage LA [interface #val #[(15 + unsigned cvp_i)%N] : chInpOvn → chOut ] A_export A →
      fdisjoint LA (OVN_old_proofs.P_i_locs (unsigned cvp_i) :|: OVN_old_proofs.combined_locations) →
      AdvantageE
        (maximum_ballot_secrecy_ovn cvp_i cvp_xi cvp_vote state)
      (hacspec_args_old_ovn_pkg cvp_i cvp_xi cvp_vote state j schnorr_r)
      A = 0%R.
  Proof.
    intros ? ? ? ? ? ? ?.

    epose (@fto (fintype_ordinal__canonical__fintype_Finite 55) (@inZp 54 (unsigned cvp_i))).
    epose (unsigned cvp_i).

    assert (fto_inZp : (nat_of_ord (fto (inZp (p' := 54) (unsigned cvp_i)))
            = uint_size_to_nat (Z_to_int (unsigned cvp_i)))%N).
    {
      unfold fto.
      rewrite enum_rank_ord.
      now setoid_rewrite modn_small.
    }

    intros.
    apply: eq_rel_perf_ind_eq.
    all: fold chElement.
    1: apply (maximum_ballot_secrecy_ovn cvp_i cvp_xi cvp_vote).
    1: rewrite <- fto_inZp ; apply (hacspec_args_old_ovn_pkg cvp_i cvp_xi cvp_vote state j schnorr_r).
    2: apply H.
    2: rewrite <- fset0E ; apply fdisjoints0.
    2: rewrite fto_inZp ; apply H0.

    {
      clear H0 H.
      unfold eq_up_to_inv.

      intros.
      unfold get_op_default.

      rewrite <- fset1E in H.
      apply (ssrbool.elimT (fset1P _ _)) in H.
      inversion H. subst. clear H.

      unfold lookup_op.
      set (getm (pack (maximum_ballot_secrecy_ovn _ _ _ _)) _).
      simpl in o0.
      subst o0.
      rewrite setmE.
      rewrite eqxx.
      unfold mkdef.

      set (getm (pack (hacspec_args_old_ovn_pkg _ _ _ _ _ _)) _).
      simpl in o0.

      unfold mkdef in o0.
      simpl in o0.
      subst o0.
      rewrite mapmE.
      rewrite setmE.

      rewrite fto_inZp.
      rewrite eqxx.

      unfold omap, obind, oapp.

      destruct choice_type_eqP ; [ | subst ; contradiction ] ; try rewrite !cast_fun_K.
      destruct choice_type_eqP ; [ | subst ; contradiction ] ; try rewrite !cast_fun_K.
      clear e e0.

      unfold code_link.

      unfold lookup_op at 1.
      unfold mkopsig.

      set (getm _ _).
      simpl in o0.
      unfold par in o0.
      unfold unionm in o0.
      unfold OVN_old_proofs.INIT in o0.
      unfold foldr in o0.
      simpl in o0.
      subst o0.
      rewrite setmE.
      rewrite eqxx.

      destruct choice_type_eqP ; [ | subst ; contradiction ] ; try rewrite !cast_fun_K.
      destruct choice_type_eqP ; [ | subst ; contradiction ] ; try rewrite !cast_fun_K.
      clear e e0.

      (* sampler *)
      eapply r_uniform_bij with (f := (λ x0 : Arit (uniform #|'Z_q|), _)).
      Unshelve. 3:{ apply x0. } 1: now apply inv_bij.
      intros cvp_zkp_random_w.
      fold @bind.

      (* put *)
      apply better_r_put_rhs.

      (* match *)
      destruct choice_type_eqP ; [ | subst ; contradiction ] ; try rewrite !cast_fun_K.
      destruct choice_type_eqP ; [ | subst ; contradiction ] ; try rewrite !cast_fun_K.
      clear e e0.

      (* assert *)
      replace (OVN_old_proofs.Sigma1.MyParam.R _ _) with true.
      2:{
        symmetry.
        rewrite otf_fto.
        unfold OVN_old_proofs.Sigma1.MyParam.R.
        rewrite eqxx.
        reflexivity.
      }
      unfold assertD at 1.

      (* sampler *)
      eapply r_uniform_bij with (f := (λ x0 : Arit (uniform #|'Z_q|), _)).
      Unshelve. 3:{ apply x0. } 1: now apply inv_bij.
      intros cvp_zkp_random_d.
      fold @bind.
      
      (* put *)
      apply better_r_put_rhs.

      (* unfold lookup *)
      unfold lookup_op at 1.

      set (getm _ _).
      simpl in o0.
      subst o0.
      rewrite setmE.

      rewrite eqxx.

      (* match *)
      destruct choice_type_eqP ; [ | subst ; contradiction ] ; try rewrite !cast_fun_K.

      (* unfold lookup *)
      unfold lookup_op at 1.

      set (getm _ _).
      simpl in o0.
      subst o0.
      rewrite setmE.

      replace (_ == _) with false by reflexivity.

      rewrite setmE.
      rewrite eqxx.

      destruct choice_type_eqP ; [ | subst ; contradiction ] ; try rewrite !cast_fun_K.
      destruct choice_type_eqP ; [ | subst ; contradiction ] ; try rewrite !cast_fun_K.
      clear e e0 e1.

      (* put *)
      apply better_r_put_rhs.
      fold @bind.
      
      (* get *)
      apply better_r.
      apply r_get_remind_rhs with (v := emptym).
      {
        unfold Remembers_rhs.
        intros.
        unfold set_rhs in H.
        destruct H.
        destruct H.
        destruct H.
        destruct H.
        destruct H.
        destruct H.

        unfold rem_rhs.
        subst.

        rewrite get_set_heap_eq.
        reflexivity.
      }
      fold @bind.
      apply better_r.

      rewrite emptymE.

      (* sampler *)
      eapply r_uniform_bij with (f := (λ x0 : Arit (uniform #|'Z_q|), _)).
      Unshelve. 3:{ apply x0. } 1: now apply inv_bij.
      intros cvp_zkp_random_r.
      fold @bind.
      
      (* put *)
      apply better_r_put_rhs.
      fold @bind.

      (* get *)
      apply better_r.
      eapply r_get_remind_rhs with (v := cvp_zkp_random_d).
      {
        unfold Remembers_rhs.
        intros.
        unfold set_rhs in H.
        destruct H.
        destruct H.
        destruct H.
        destruct H.
        destruct H.
        destruct H.
        destruct H.
        destruct H.

        unfold rem_rhs.
        subst.

        rewrite get_set_heap_neq ; [ | reflexivity ].
        rewrite get_set_heap_neq ; [ | reflexivity ].
        rewrite get_set_heap_eq.
        reflexivity.
      }
      fold @bind.
      apply better_r.

      (* sample *)
      apply r_const_sample_R ; [ apply LosslessOp_uniform | intros ].

      (* unfold lookup *)
      unfold lookup_op at 1.

      set (getm _ _).
      simpl in o0.
      unfold par in o0.
      unfold unionm in o0.
      unfold OVN_old_proofs.INIT in o0.
      unfold foldr in o0.
      simpl in o0.
      subst o0.
      rewrite setmE.
      replace (_ == _) with false by reflexivity.

      rewrite setmE.
      replace (_ == _) with false by reflexivity.
      rewrite setmE.
      replace (_ == _) with false by reflexivity.

      rewrite mapmE.
      rewrite setmE.
      
      replace (_ == _) with false by reflexivity.
      unfold omap, obind, oapp.

      rewrite setmE.
      rewrite eqxx.

      destruct choice_type_eqP ; [ | subst ; contradiction ] ; try rewrite !cast_fun_K.
      destruct choice_type_eqP ; [ | subst ; contradiction ] ; try rewrite !cast_fun_K.
      clear e e0.

      (* assert *)
      replace (OVN_old_proofs.Sigma1.MyParam.R _ _) with true.
      2:{
        symmetry.
        rewrite otf_fto.
        unfold OVN_old_proofs.Sigma1.MyParam.R.
        rewrite eqxx.
        reflexivity.
      }
      unfold assertD at 1.

      (* sample *)
      apply r_const_sample_R ; [ apply LosslessOp_uniform | intros ].
      fold @bind.

      (* put *)
      apply better_r_put_rhs.
      fold @bind.

      (* unfold lookup *)
      unfold lookup_op at 1.

      set (getm _ _).
      simpl in o0.
      subst o0.
      rewrite setmE.
      rewrite eqxx.

      destruct choice_type_eqP ; [ | subst ; contradiction ] ; try rewrite !cast_fun_K.
      clear e.

      (* put *)
      apply better_r_put_rhs.
      fold @bind.

      (* unfold lookup *)
      unfold lookup_op at 1.

      set (getm _ _).
      simpl in o0.
      subst o0.
      rewrite setmE.
      replace (_ == _) with false by reflexivity.
      rewrite setmE.
      rewrite eqxx.

      destruct choice_type_eqP ; [ | subst ; contradiction ] ; try rewrite !cast_fun_K.
      destruct choice_type_eqP ; [ | subst ; contradiction ] ; try rewrite !cast_fun_K.
      clear e e0.

      (* get *)
      apply better_r.
      apply r_get_remind_rhs with (v := emptym).
      {
        unfold Remembers_rhs.
        intros.
        unfold set_rhs in H.
        destruct H.
        destruct H.
        destruct H.
        destruct H.
        destruct H.
        destruct H.
        destruct H.
        destruct H.
        destruct H.
        destruct H.
        destruct H.
        destruct H.

        unfold rem_rhs.
        subst.

        rewrite get_set_heap_eq.
        reflexivity.
      }
      fold @bind.
      apply better_r.

      rewrite emptymE.

      (* sample *)
      apply r_const_sample_R ; [ apply LosslessOp_uniform | intros ].
      fold @bind.

      (* put *)
      apply better_r_put_rhs.
      fold @bind.

      (* unfold lookup *)
      unfold lookup_op at 1.

      set (getm _ _).
      simpl in o0.
      subst o0.
      rewrite setmE.
      replace (_ == _) with false by reflexivity.
      rewrite setmE.
      replace (_ == _) with false by reflexivity.
      rewrite setmE.
      rewrite eqxx.

      unfold ".2" at 1.
      unfold ".2" at 1.
      
      destruct choice_type_eqP ; [ | subst ; contradiction ] ; try rewrite !cast_fun_K.
      destruct choice_type_eqP ; [ | subst ; contradiction ] ; try rewrite !cast_fun_K.
      clear e e0.

      (* get *)
      apply better_r.
      eapply r_get_remind_rhs (* with (v := emptym) *).
      {
        unfold Remembers_rhs.
        intros.
        unfold set_rhs in H.
        destruct H.
        destruct H.
        destruct H.
        destruct H.
        destruct H.
        destruct H.
        destruct H.
        destruct H.
        destruct H.
        destruct H.
        destruct H.
        destruct H.
        destruct H.
        destruct H.

        unfold rem_rhs.
        subst.

        repeat (rewrite get_set_heap_neq ; [ | reflexivity ]).
        rewrite get_set_heap_eq.
        reflexivity.
      }
      fold @bind.
      apply better_r.

      (* assert *)
      replace (_ == _) with true.
      2:{
        clear -fto_inZp.
        symmetry.
        (* simpl. *)

        rewrite domm_set.
        rewrite domm_set.
        rewrite domm_mkfmapf.

        set (l := ([:: _, _ & _])).
        rewrite <- (map_id l).
        change ([seq x | x <- l]) with ([seq (fto (inZp (p' := 54) x)) | x <- iota 0 55]).
        subst l.

        assert (forall (v : 'I_#|'I_55|), (v \in fset [seq fto (inZp x) | x <- iota 0 55])).
        {
          intros v.
          assert (exists n0, v = fto (inZp n0)).
          1:{
            rewrite <- (fto_otf v).
            destruct (otf v).
            exists m.
            f_equal.
            apply ord_ext.
            now rewrite modn_small.
          }
          destruct H as [n0 ?].
          subst.
          
          rewrite in_fset.

          set 54%nat in * |- *.
          generalize dependent n1.
          intros.
          
          assert (forall n0 n1, exists k r, (r < n1.+1) /\ n0 = k * n1.+1 + r)%nat.
          {
            clear.
            intros n0 n1.
            now induction n0 as [ | ? [k [r []]] ] ;
              [ exists 0%nat , 0%nat |
                destruct (r.+1 == n1.+1) eqn:overflow ;
                [ exists k.+1, 0%nat | exists k, r.+1 ]
              ].
          }
          specialize (H n0 n1).
          destruct H as [k [r []]].
          rewrite H0.

          replace (inZp (k * n1.+1 + r)) with (inZp (p' := n1) r).
          2:{
            unfold inZp.
            apply ord_ext.
            rewrite <- modnDm.
            rewrite modnMl.
            rewrite add0n.
            rewrite modn_mod.
            reflexivity.
          }

          clear H0.


          set (fto _). pattern (r) in o. subst o.
          rewrite map_f ; [ reflexivity | ].
          rewrite mem_iota.
          easy.
        }

        rewrite sizesU1.
        replace (_ \notin _) with false.
        2:{
          unfold "\notin".
          rewrite in_fset.
          rewrite in_cons.
          rewrite H.
          now rewrite Bool.orb_true_r.
        }

        rewrite sizesU1.
        replace (_ \notin _) with false.
        2:{
          unfold "\notin".
          now rewrite H.
        }

        rewrite !add0n.

        eassert (forall f a n, (forall x y, ((a <= x < a + n) /\ (a <= y < a + n))%nat -> f x = f y -> x = y) ->
                          size (fset [seq (f x) | x <- iota a n]) == n).
        {
          intros.
          induction n0.
          {
            cbn.
            rewrite <- fset0E.
            simpl.
            reflexivity.
          }
          rewrite <- addn1.
          rewrite iotaD.
          rewrite map_cat.
          rewrite fset_cat.
          rewrite sizesU.

          2:{
            apply /fdisjointP.
            intros.
            simpl.
            rewrite <- fset1E.
            apply /fset1P.
            red ; intros.
            subst.
            erewrite in_fset in H1.
            epose (ssrbool.elimT mapP H1).
            destruct e.
            rewrite mem_iota in H2.
            apply H0 in H3.
            2:{
              split ; [ easy | ].
              easy.
            }
            easy.
          }

          apply (ssrbool.elimT eqP) in IHn0.
          2: intros ; apply H0 ; easy.

          rewrite IHn0.
          
          cbn.
          rewrite <- fset1E.
          now apply /eqP.
        }
        rewrite H0.
        1: reflexivity.
        intros.

        Set Printing Coercions.

        (* clear -H1 H2. *)

        apply (enum_rank_inj) in H2.
        inversion H2.
        
        rewrite <- !Zp_nat in H2.

        rewrite !add0n in H1.
        destruct H1.
        
        rewrite !modn_small in H4.
        2,3: easy.
        assumption.
      }
      unfold assertD at 1.

      (* put *)
      apply better_r_put_rhs.
      fold @bind.

      (* unfold lookup *)
      unfold lookup_op at 1.

      set (getm _ _).
      simpl in o0.
      subst o0.
      rewrite setmE.
      replace (_ == _) with false by reflexivity.
      rewrite setmE.
      rewrite eqxx.

      unfold ".2" at 1.
      unfold ".2" at 1.
      
      destruct choice_type_eqP ; [ | subst ; contradiction ] ; try rewrite !cast_fun_K.
      destruct choice_type_eqP ; [ | subst ; contradiction ] ; try rewrite !cast_fun_K.
      clear e e0.

      (* get *)
      apply better_r.
      eapply r_get_remind_rhs (* with (v := emptym) *).
      {
        unfold Remembers_rhs.
        intros.
        unfold set_rhs in H.
        destruct H.
        destruct H.
        destruct H.
        destruct H.
        destruct H.
        destruct H.
        destruct H.
        destruct H.
        destruct H.
        destruct H.
        destruct H.
        destruct H.
        destruct H.
        destruct H.
        destruct H.
        destruct H.

        unfold rem_rhs.
        subst.

        repeat (rewrite get_set_heap_neq ; [ | reflexivity ]).
        rewrite get_set_heap_neq. 2: admit.
        repeat (rewrite get_set_heap_neq ; [ | reflexivity ]).
        rewrite get_set_heap_neq. 2: admit.
        repeat (rewrite get_set_heap_neq ; [ | reflexivity ]).
        rewrite get_set_heap_neq. 2: admit.
        repeat (rewrite get_set_heap_neq ; [ | reflexivity ]).
        rewrite get_set_heap_eq.
        reflexivity.
      }
      fold @bind.
      apply better_r.

      (* get *)
      apply better_r.
      eapply r_get_remind_rhs (* with (v := emptym) *).
      {
        unfold Remembers_rhs.
        intros.
        unfold set_rhs in H.
        destruct H.
        destruct H.
        destruct H.
        destruct H.
        destruct H.
        destruct H.
        destruct H.
        destruct H.
        destruct H.
        destruct H.
        destruct H.
        destruct H.
        destruct H.
        destruct H.
        destruct H.
        destruct H.

        unfold rem_rhs.
        subst.

        repeat (rewrite get_set_heap_neq ; [ | reflexivity ]).
        rewrite get_set_heap_eq. 
        reflexivity.
      }
      fold @bind.
      apply better_r.

      simpl.

      destruct cvp_vote.
      1:{
        
  Qed.

  Solve All Obligations with now intros ; destruct from_uint_size.
  Qed.

  Check OVN_old_proofs.vote_hiding.
  Check OVN_old_proofs.vote_hiding_bij.

  (* begin details : helper defintions *)

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

  Lemma somewhat_let_substitution :
             forall {A C : choice_type} {B : choiceType} (f : C -> raw_code B) (c : raw_code B) (y : both A) (r : both A -> both C),
               ⊢ ⦃ λ '(s₀, s₁), s₀ = s₁ ⦄ b_temp ← is_state y ;; temp ← is_state (r (ret_both b_temp)) ;; f temp ≈ c ⦃ λ '(b₀, s₀) '(b₁, s₁), b₀ = b₁ ∧ s₀ = s₁ ⦄ ->
               ⊢ ⦃ λ '(s₀, s₁), s₀ = s₁ ⦄ temp ← is_state (letb 'b := y in r ((b))) ;; f temp ≈ c ⦃ λ '(b₀, s₀) '(b₁, s₁), b₀ = b₁ ∧ s₀ = s₁ ⦄.
  Proof.
    intros.
    unfold let_both at 1.
    eapply r_transR ; [ eapply rpost_weaken_rule ; [ apply H | now intros [] [] [] | .. ] | ].
    rewrite <- bind_assoc.
    apply r_bind_feq.
    2:intros ; eapply rpost_weaken_rule ; [ apply rreflexivity_rule | now intros [] [] H0 ; inversion H0 ].

    pose (determ := (fun (y : both A) => both_deterministic y)).
    pose (y_det := both_deterministic y).

    pose (hd₀ := determ ).
    pose (hd₁ := deterministic_bind _ _ y_det (fun x => determ (ret_both x))).
    simpl in hd₁.

    eapply r_transL.
    2:{
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
        c ⦃ Logic.eq ⦄ ->
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
    eapply r_transR with (c₁ := '(a,r) ← _ ;; f a r).
    2: apply r_bind_feq ; [ apply rsamplerC | intros [] ].
    2: apply rreflexivity_rule.
    rewrite !bind_assoc.
    simpl.
    setoid_rewrite bind_assoc.
    simpl.
    apply H.
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
  (* end details *)

  Notation " 'chState' " :=
    t_OvnContractState
    (in custom pack_type at level 2).

  Notation " 'chCastVoteCtx' " :=
    t_CastVoteParam
    (in custom pack_type at level 2).

  Notation " 'chInp' " :=
    (t_OvnContractState × (int32 × f_Z × 'bool))
    (in custom pack_type at level 2).

  Notation " 'chAuxInp' " :=
    (OR_ZKP.MyAlg.choiceStatement × OR_ZKP.MyAlg.choiceWitness)
    (in custom pack_type at level 2).

  Notation " 'chAuxOut' " :=
    (OR_ZKP.MyAlg.choiceTranscript)
    (in custom pack_type at level 2).

  Definition MAXIMUM_BALLOT_SECRECY_SETUP : nat := 10.
  Definition MAXIMUM_BALLOT_SECRECY_RETURN : nat := 11.
  
  Program Definition maximum_ballot_secrecy_real_setup :
    package (fset [::])
      [interface]
      [interface
         #val #[ MAXIMUM_BALLOT_SECRECY_SETUP ] : chInp → chAuxInp
      ] :=
    [package
      #def #[ MAXIMUM_BALLOT_SECRECY_SETUP ] ('(state_inp, (cvp_i, cvp_xi, cvp_vote)) : chInp) : chAuxInp
      {
        let state := ret_both (state_inp :
                         t_OvnContractState) in

        g_pow_yi ← is_state (compute_g_pow_yi (cast_int (WS2 := _) (ret_both cvp_i)) (f_g_pow_xis state)) ;;

        let cStmt : OR_ZKP.MyAlg.choiceStatement :=
          fto ((
                is_pure (f_g_pow (ret_both cvp_xi)),
                g_pow_yi : gT ,
                is_pure (f_prod (f_pow (ret_both g_pow_yi) (ret_both cvp_xi)) (if cvp_vote then f_g else f_group_one)) : gT
              ) : OR_ZKP.MyParam.Statement) in (* x, h , y *)
        let cWitn : OR_ZKP.MyAlg.choiceWitness :=
          fto ((
                FieldToWitness (is_pure (ret_both cvp_xi)) : 'Z_q,
                is_pure (ret_both (cvp_vote : 'bool)),
                  g_pow_yi) : OR_ZKP.MyParam.Witness) in (* xi, vi, h *)

        (* #put setup_loc := cStmt ;; ret (Datatypes.tt : 'unit) *)
        ret (cStmt, cWitn)
    }].
  Next Obligation.
    eapply (valid_package_cons _ _ _ _ _ _ [] []).
    - apply valid_empty_package.
    - intros [].
      simpl.
      ssprove_valid'_2.
      all: repeat (apply valid_sampler ; intros).
      all: ssprove_valid'_2.
      all: try (apply (valid_injectMap (I1 := fset0)) ; [ apply fsub0set | rewrite <- fset0E ]).
      all: try apply (ChoiceEquality.is_valid_code (both_prog_valid _)).
      all: repeat (apply valid_sampler ; intros).
      all: repeat (rewrite !otf_fto ; ssprove_valid'_2).
      all: try (apply valid_scheme ; rewrite <- fset0E ; apply (ChoiceEquality.is_valid_code (both_prog_valid _))).
      all: setoid_rewrite <- fset1E ; rewrite in_fset1 ; apply eqxx.
    - unfold "\notin".
      rewrite <- !fset0E.
      rewrite imfset0.
      rewrite in_fset0.
      easy.
  Qed.
  Fail Next Obligation.

  Notation " 'chMidInp' " :=
    (t_OvnContractState × (int32 × f_Z × 'bool) × OR_ZKP.MyAlg.choiceTranscript)
    (in custom pack_type at level 2).

  Program Definition maximum_ballot_secrecy_real_return :
    package (fset [])
      [interface]
      [interface
         #val #[ MAXIMUM_BALLOT_SECRECY_RETURN ] : chMidInp → chOut
      ] :=
    [package
       #def #[ MAXIMUM_BALLOT_SECRECY_RETURN ] ('(state_inp, (cvp_i, cvp_xi, cvp_vote), transcript) : chMidInp) : chOut
       {
         let state := ret_both (state_inp : t_OvnContractState) in

         (* before zkp_vi *)

         let zkp_vi := ret_both (OR_ZKP.or_sigma_ret_to_hacspec_ret transcript) in

        (* after zkp_vi *)
        temp ← is_state (
            letb g_pow_xi_yi_vi := compute_group_element_for_vote (ret_both cvp_xi) (ret_both (cvp_vote : 'bool)) (ret_both ((otf transcript.1.1.1).1.2)) in
            letb cast_vote_state_ret := f_clone state in
            letb cast_vote_state_ret := Build_t_OvnContractState[cast_vote_state_ret] (f_g_pow_xi_yi_vis := update_at_usize (f_g_pow_xi_yi_vis cast_vote_state_ret) (cast_int (WS2 := _) (ret_both cvp_i)) g_pow_xi_yi_vi) in
            letb cast_vote_state_ret := Build_t_OvnContractState[cast_vote_state_ret] (f_zkp_vis := update_at_usize (f_zkp_vis cast_vote_state_ret) (cast_int (WS2 := _) (ret_both cvp_i)) zkp_vi) in
            (prod_b (f_accept,cast_vote_state_ret))) ;;
        ret (Some temp.2)
       }].
  Next Obligation.
    eapply (valid_package_cons _ _ _ _ _ _ [] []).
    - apply valid_empty_package.
    - intros [].
      simpl.
      ssprove_valid'_2.
      all: repeat (apply valid_sampler ; intros).
      all: ssprove_valid'_2.
      all: try (apply (valid_injectMap (I1 := fset0)) ; [ apply fsub0set | rewrite <- fset0E ]).
      all: try apply (ChoiceEquality.is_valid_code (both_prog_valid _)).
      all: repeat (apply valid_sampler ; intros).
      all: repeat (rewrite !otf_fto ; ssprove_valid'_2).
      all: now rewrite in_fset ; repeat (rewrite in_cons ; simpl) ; rewrite eqxx.
    - unfold "\notin".
      rewrite <- !fset0E.
      rewrite imfset0.
      rewrite in_fset0.
      easy.
  Qed.
  Fail Next Obligation.

  Program Definition maximum_ballot_secrecy :
    package (fset [::])
      [interface
         #val #[ Sigma.RUN ] : chAuxInp → chAuxOut ;
         #val #[ MAXIMUM_BALLOT_SECRECY_RETURN ] : chMidInp → chOut ;
         #val #[ MAXIMUM_BALLOT_SECRECY_SETUP ] : chInp → chAuxInp
      ]
      [interface
         #val #[ MAXIMUM_BALLOT_SECRECY ] : chInp → chOut
      ] :=
    [package
      #def #[ MAXIMUM_BALLOT_SECRECY ] ('(state_inp, (cvp_i, cvp_xi, cvp_vote)) : chInp) : chOut
      {
        #import {sig #[ MAXIMUM_BALLOT_SECRECY_SETUP ] : chInp → chAuxInp } as SETUP ;;
        #import {sig #[ Sigma.RUN ] : chAuxInp → chAuxOut } as RUN ;;
        #import {sig #[ MAXIMUM_BALLOT_SECRECY_RETURN ] : chMidInp → chOut } as OUTPUT ;;

        '(cStmt, cWitn) ← SETUP (state_inp, (cvp_i, cvp_xi, cvp_vote)) ;;
        (* cStmt ← get setup_loc ;; *)
        (* let cWitn : OR_ZKP.MyAlg.choiceWitness := *)
        (*   fto (( *)
        (*         FieldToWitness (is_pure (ret_both cvp_xi)) : 'Z_q, *)
        (*         is_pure (ret_both (cvp_vote : 'bool)), *)
        (*           (otf cStmt).1.2) : OR_ZKP.MyParam.Witness) in *)
        transcript ← RUN (cStmt, cWitn) ;;
        res ← OUTPUT (state_inp, (cvp_i, cvp_xi, cvp_vote), transcript) ;;
        ret res
      }
    ].
  Next Obligation.
    eapply (valid_package_cons _ _ _ _ _ _ [] []).
    - apply valid_empty_package.
    - intros [].
      simpl.
      ssprove_valid'_2.
      all: repeat (apply valid_sampler ; intros).
      all: ssprove_valid'_2.
      all: try (apply (valid_injectMap (I1 := fset0)) ; [ apply fsub0set | rewrite <- fset0E ]).
      all: try apply (ChoiceEquality.is_valid_code (both_prog_valid _)).
      all: repeat (apply valid_sampler ; intros).
      all: repeat (rewrite !otf_fto ; ssprove_valid'_2).
      all: try now rewrite in_fset ; repeat (rewrite in_cons ; simpl) ; rewrite eqxx.
    - unfold "\notin".
      rewrite <- !fset0E.
      rewrite imfset0.
      rewrite in_fset0.
      easy.
  Qed.
  Fail Next Obligation.

  Notation " 'chAuxSimInp' " :=
    (OR_ZKP.MyAlg.choiceStatement × OR_ZKP.MyAlg.choiceChallenge)
    (in custom pack_type at level 2).

  Notation " 'chAuxSimOut' " :=
    (OR_ZKP.MyAlg.choiceTranscript)
      (in custom pack_type at level 2).

  Program Definition maximum_ballot_secrecy_ideal_setup:
    package fset0 (* (fset [setup_loc]) *)
      [interface]
      [interface #val #[ MAXIMUM_BALLOT_SECRECY_SETUP ] : chInp → chAuxInp] :=
    [package
      #def #[ MAXIMUM_BALLOT_SECRECY_SETUP ] ('(state, (cvp_i, cvp_xi, cvp_vote)) : chInp) : chAuxInp
      {
        let state := ret_both (state : t_OvnContractState) in
        let p_i := ret_both cvp_i : both int32 in
        h ← is_state (compute_g_pow_yi (cast_int (WS2 := U32) p_i) (f_g_pow_xis state)) ;;

        (* z_i ← sample uniform #|'Z_q| ;; *)
        (* let y := ((g : gT) ^+ otf z_i)%g in *)

        (* m_i ← sample uniform #|'Z_q| ;; *)
        (* let x := ((g : gT) ^+ otf m_i)%g in *)

        let y := ((h : gT) ^+ (FieldToWitness cvp_xi) * g ^+ (if cvp_vote then 1 else 0)%R)%g in
        let x := g ^+ (FieldToWitness cvp_xi) in
        
        (* (* #put setup_loc := fto (x, h : gT, y) ;; *) ret (Datatypes.tt : 'unit) *)
        ret (fto (x, h : gT, y), fto ( FieldToWitness cvp_xi, cvp_vote, h : gT ))
      }].
  Next Obligation.
    eapply (valid_package_cons _ _ _ _ _ _ [] []).
    - apply valid_empty_package.
    - intros [].
      simpl.
      destruct s0 as [[? ?] ?].
      ssprove_valid'_2.
      all: repeat (apply valid_sampler ; intros).
      all: ssprove_valid'_2.
      all: try destruct (otf s8), s12, (otf s11), s15 as [[? ?] ?], (otf s9), s19 as [[? ?] ?].
      all: try (apply (valid_injectMap (I1 := fset0)) ; [ apply fsub0set | rewrite <- fset0E ]).
      all: try apply (ChoiceEquality.is_valid_code (both_prog_valid _)).
      all: repeat (apply valid_sampler ; intros).
      all: repeat (rewrite !otf_fto ; ssprove_valid'_2).
      all: ssprove_valid'_2.
      all: try (apply valid_scheme ; rewrite <- fset0E ; apply (ChoiceEquality.is_valid_code (both_prog_valid _))).
      all: setoid_rewrite <- fset1E ; rewrite in_fset1 ; apply eqxx.
    - unfold "\notin".
      rewrite <- !fset0E.
      rewrite imfset0.
      rewrite in_fset0.
      easy.
  Qed.
  Fail Next Obligation.

  Program Definition maximum_ballot_secrecy_ideal_return :
    package (fset [])
      [interface]
      [interface
         #val #[ MAXIMUM_BALLOT_SECRECY_RETURN ] : chMidInp → chOut
      ] :=
    [package
       #def #[ MAXIMUM_BALLOT_SECRECY_RETURN ] ('(state, (cvp_i, cvp_xi, cvp_vote), transcript) : chMidInp) : chOut
      {
        let state := ret_both (state : t_OvnContractState) in

        let p_i := ret_both cvp_i : both int32 in
        let '(zkp_xhy, zkp_abab, zkp_c, zkp_rdrd) := transcript in
        let '(x,h,y) := otf zkp_xhy in
        let '(zkp_a1, zkp_b1, zkp_a2, zkp_b2) := otf zkp_abab in
        let '(zkp_r1, zkp_d1, zkp_r2, zkp_d2) := otf zkp_rdrd in

        let zkp_c := WitnessToField (otf zkp_c : 'Z_q) : f_Z in

        let zkp_r1 := WitnessToField (zkp_r1 : 'Z_q) : f_Z in
        let zkp_d1 := WitnessToField (zkp_d1 : 'Z_q) : f_Z in
        let zkp_r2 := WitnessToField (zkp_r2 : 'Z_q) : f_Z in
        let zkp_d2 := WitnessToField (zkp_d2 : 'Z_q) : f_Z in

        res ← is_state (
            letb zkp_vi :=
              Build_t_OrZKPCommit
                (f_or_zkp_x := ret_both x)
                (f_or_zkp_y := ret_both y)
                (f_or_zkp_a1 := ret_both zkp_a1)
                (f_or_zkp_b1 := ret_both zkp_b1)
                (f_or_zkp_a2 := ret_both zkp_a2)
                (f_or_zkp_b2 := ret_both zkp_b2)
                (f_or_zkp_c := ret_both zkp_c)
                (f_or_zkp_d1 := ret_both zkp_d1)
                (f_or_zkp_d2 := ret_both zkp_d2)
                (f_or_zkp_r1 := ret_both zkp_r1)
                (f_or_zkp_r2 := ret_both zkp_r2)
              in
            letb g_pow_xi_yi_vi_list := update_at_usize (f_g_pow_xi_yi_vis state) (cast_int (WS2 := U32) (p_i)) (ret_both (is_pure (compute_group_element_for_vote (ret_both cvp_xi) (ret_both (cvp_vote : 'bool)) (ret_both ((otf transcript.1.1.1).1.2))))) in
            letb state := (Build_t_OvnContractState[state] (f_g_pow_xi_yi_vis := g_pow_xi_yi_vi_list)) in
            letb zkp_vi_list := update_at_usize (f_zkp_vis state) (cast_int (WS2 := U32) (p_i)) (zkp_vi) in
            letb state := (Build_t_OvnContractState[state] (f_zkp_vis := zkp_vi_list))
        in
        state) ;;
        ret (Some res)
    }].
    Next Obligation.
    eapply (valid_package_cons _ _ _ _ _ _ [] []).
    - apply valid_empty_package.
    - intros [].
      simpl.
      ssprove_valid'_2.
      all: repeat (apply valid_sampler ; intros).
      all: ssprove_valid'_2.
      all: try destruct (otf s0), s13, (otf s6), s16 as [[? ?] ?], (otf s1), s20 as [[? ?] ?].
      all: try (apply (valid_injectMap (I1 := fset0)) ; [ apply fsub0set | rewrite <- fset0E ]).
      all: try apply (ChoiceEquality.is_valid_code (both_prog_valid _)).
      all: repeat (apply valid_sampler ; intros).
      all: repeat (rewrite !otf_fto ; ssprove_valid'_2).
      all: ssprove_valid'_2.
    - unfold "\notin".
      rewrite <- !fset0E.
      rewrite imfset0.
      rewrite in_fset0.
      easy.
  Qed.
  Fail Next Obligation.

  Program Definition maximum_ballot_secrecy_real_par0 : package
      (MyAlg.Sigma_locs)
      [interface]
      [interface
         #val #[Sigma.RUN] : chAuxInp → chAuxSimOut ;
         #val #[MAXIMUM_BALLOT_SECRECY_RETURN] : chMidInp → chOut
      ] :=
    mkpackage (par hacspec_or_run maximum_ballot_secrecy_real_return) _.
  Next Obligation.
    eapply valid_package_inject_export.
    2:{
      pose (valid_par _ _ _ _ _ _ _ _ _ (pack_valid hacspec_or_run) (pack_valid maximum_ballot_secrecy_real_return) ).
      rewrite <- fset0E in v.
      rewrite fsetU0 in v.
      rewrite <- fset0E in v.
      rewrite fset0U in v.
      rewrite fset0E in v.

      apply v.
    }

    rewrite <- !fset_cat.
    apply fsubsetxx.
  Qed.

  Lemma maximum_ballot_secrecy_real_parable : Parable maximum_ballot_secrecy_real_par0 maximum_ballot_secrecy_real_setup.
  Proof.
    unfold Parable.
    rewrite !domm_set ; unfold ".1".
    rewrite domm0.
    rewrite !fsetU0.
    rewrite fdisjointUl.
    rewrite !fdisjoint1s.
    easy.
  Qed.

  Program Definition maximum_ballot_secrecy_real :
    package
      (MyAlg.Sigma_locs)
      [interface]
      [interface #val #[MAXIMUM_BALLOT_SECRECY] : chInp → chOut ]
    :=
    mkpackage (maximum_ballot_secrecy ∘ (par (par hacspec_or_run maximum_ballot_secrecy_real_return) maximum_ballot_secrecy_real_setup)) _.
  Next Obligation.
    (* rewrite <- fset0U. rewrite fset0U. *)
    (* setoid_rewrite <- (fsetUid (fset [::])). *)
    eapply valid_link_upto.
    1: apply maximum_ballot_secrecy.
    1: eapply (valid_par_upto
             _ _ _ _ _ _ _ _ _ _ _
             maximum_ballot_secrecy_real_parable
           ).
    1: apply maximum_ballot_secrecy_real_par0.
    1: apply maximum_ballot_secrecy_real_setup.
    1: rewrite <- fset0E ; rewrite fsetU0 ; (* rewrite fsetUC ; *) apply fsubsetxx.
    1: rewrite <- !fset0E, fsetU0 ; apply fsub0set.
    1: rewrite <- !fset_cat ; simpl ; apply fsubsetxx.
    1: rewrite <- fset0E ; apply fsub0set.
    1: apply fsubsetxx.
  Qed.
  Fail Next Obligation.

  Notation " 'SHVZK_chInput' " :=
    (chProd (chProd MyAlg.choiceStatement MyAlg.choiceWitness) MyAlg.choiceChallenge)
      (in custom pack_type at level 2).

  Notation " 'SHVZK_chTranscript' " :=
    (OR_ZKP.MyAlg.choiceTranscript)
      (in custom pack_type at level 2).

  Notation " 'SHVZK_chRelation' " :=
    (chProd MyAlg.choiceStatement MyAlg.choiceWitness)
      (in custom pack_type at level 2).

  Definition SHVZK_ideal_aux : package (fset [::]) [interface #val #[ Sigma.TRANSCRIPT ] : SHVZK_chInput → SHVZK_chTranscript ] [interface #val #[Sigma.RUN] : SHVZK_chRelation → SHVZK_chTranscript ]
    :=
    [package
        #def #[ Sigma.RUN ] (hw : SHVZK_chRelation) : SHVZK_chTranscript
        {
          #import {sig #[ Sigma.TRANSCRIPT ] : SHVZK_chInput → SHVZK_chTranscript } as SHVZK ;;
          e ← sample uniform #|MyParam.Challenge| ;;
          t ← SHVZK (hw, e) ;;
          ret t
        }
    ].

  Program Definition maximum_ballot_secrecy_ideal_par0 : package
      (MyAlg.Simulator_locs)
      [interface]
      [interface
         #val #[Sigma.RUN] : chAuxInp → chAuxSimOut ;
         #val #[MAXIMUM_BALLOT_SECRECY_RETURN] : chMidInp → chOut
      ] :=
    mkpackage (par (SHVZK_ideal_aux ∘ Sigma.SHVZK_ideal) maximum_ballot_secrecy_ideal_return) _.
  Next Obligation.
    eapply valid_package_inject_export.
    2:{
      epose (valid_par _ _ _ _ _ _ (SHVZK_ideal_aux ∘ Sigma.SHVZK_ideal) _ _ _ (pack_valid maximum_ballot_secrecy_ideal_return) ).
      rewrite <- fset0E in v.
      rewrite fsetU0 in v.
      rewrite <- fset0E in v.
      rewrite fset0U in v.
      rewrite fset0E in v.

      rewrite fsetUid in v.

      apply v.
    }

    rewrite <- !fset_cat.
    apply fsubsetxx.
  Qed.

  Lemma maximum_ballot_secrecy_ideal_parable : Parable maximum_ballot_secrecy_ideal_par0 maximum_ballot_secrecy_ideal_setup.
  Proof.
    unfold Parable.
    rewrite !domm_set ; unfold ".1".
    rewrite domm0.
    rewrite !fsetU0.
    rewrite fdisjointUl.
    rewrite !fdisjoint1s.
    easy.
  Qed.

  Program Definition maximum_ballot_secrecy_ideal :
    package
      (MyAlg.Simulator_locs)
      [interface ]
      [interface #val #[MAXIMUM_BALLOT_SECRECY] : chInp → chOut ] :=
    mkpackage (maximum_ballot_secrecy ∘ par (par (SHVZK_ideal_aux ∘ Sigma.SHVZK_ideal) maximum_ballot_secrecy_ideal_return) maximum_ballot_secrecy_ideal_setup) _.
  Next Obligation.
    rewrite <- fset0U. rewrite fset0U.
    setoid_rewrite <- (fsetUid (fset [::])).
    rewrite <- fsetU0.
    eapply valid_link_upto.
    1: apply maximum_ballot_secrecy.
    1: {
      eapply (valid_par_upto
             _ _ _ _ _ _ _ _ _ _ _
             maximum_ballot_secrecy_ideal_parable
        ).
      1: apply maximum_ballot_secrecy_ideal_par0.
      1: apply maximum_ballot_secrecy_ideal_setup.
      1: apply fsubsetxx.
      1: apply fsubsetxx.
      1: rewrite <- !fset_cat ; apply fsubsetxx.
    }
    1: rewrite <- !fset0E, fsetU0 ; apply fsub0set.
    1: apply fsubsetxx.
  Qed.
  Fail Next Obligation.


  Definition ɛ_maximum_ballot_secrecy_OVN A :=
    AdvantageE
      (maximum_ballot_secrecy_ovn)
      (maximum_ballot_secrecy_real)
      A.

  Definition r_bind_to_post :
    forall {A B} (a b : raw_code A) (f g : A -> raw_code B) P post,
      ⊢ ⦃ P ⦄ a ≈ b ⦃ pre_to_post P ⦄
      → (∀ (a₀ : A), ⊢ ⦃ P ⦄ f a₀ ≈ g a₀ ⦃ post ⦄) →
      ⊢ ⦃ P ⦄ x ← a ;; f x ≈ x ← b ;; g x ⦃ post ⦄.
  Proof.
    intros.
    eapply r_bind with (mid := pre_to_post P) ;
      [eapply rpost_weaken_rule ; [ apply H | now intros [] [] ? ]
      | intros ].
    apply rpre_hypothesis_rule ; intros ? ? [] ; eapply rpre_weaken_rule with (pre := P) ; [ subst ; apply H0 | now simpl ; intros ? ? [] ; subst ].
  Qed.

  Definition r_refl_alt :
    forall {A} (a : both A) P, ⊢ ⦃ P ⦄ is_state a ≈ is_state a ⦃ pre_to_post P ⦄.
  Proof.
    intros.
    apply better_r.
    refine (r_reflexivity_alt (L := fset0) P _ _ _ _) ; [ rewrite <- !fset0E ; apply (ChoiceEquality.is_valid_code (both_prog_valid _)) | easy.. ].
  Qed.

  Lemma ovn_bind_lhs :
    forall P,
    forall (xi : v_Z)
      ((* w *) d r : Arit (uniform #|'Z_q|)),
    forall (a₀ : v_G)
      (a₀0 a₀1 a₀2 : v_Z)
      (a₀3 a₀4 a₀5 a₀6 : v_G),
      (⊢ ⦃ P ⦄
         x ← is_state (f_prod (f_pow (ret_both a₀) (ret_both xi)) f_g) ;;
       x0 ← is_state (f_g_pow (ret_both xi)) ;;
       ret ((x0, x, a₀6, a₀5, a₀4, a₀3, a₀2, WitnessToField (otf d), a₀1, WitnessToField (otf r), a₀0) : t_OrZKPCommit) ≈
         x ← is_state (f_prod (f_pow (ret_both a₀) (ret_both xi)) f_g) ;;
       x0 ← is_state (f_g_pow (ret_both xi)) ;;
       ret ((x0, x, a₀6, a₀5, a₀4, a₀3, a₀2, WitnessToField (otf d), a₀1, WitnessToField (otf r), a₀0) : t_OrZKPCommit)
         ⦃ (fun '(a,b) '(c, d) =>
              and (P (b, d))
                (and (@Logic.eq t_OrZKPCommit a c)
                   (c.1.1.1.1.1.1.1.1.1 =
                      (is_pure (f_g_pow (ret_both xi)), is_pure (f_prod (f_pow (ret_both a₀) (ret_both xi)) f_g))))) ⦄).
  Proof.
    intros.
    apply r_bind with (mid := fun '(a,b) '(c,d) => P (b, d) /\ a = c /\ c = (is_pure (f_prod (f_pow (ret_both a₀) (ret_both xi)) f_g)))  ; [  | intros ].
    1:{
      eapply r_transR.
      1:{
        apply r_nice_swap_rule ; [ easy | easy | ].
        eapply rpost_weaken_rule.
        1: apply (p_eq _ (fun '(a, b) => a = b)).
        now intros [] [] [[] ?].
      }

      eapply r_transL.
      1:{
        apply r_nice_swap_rule ; [ easy | easy | ].
        eapply rpost_weaken_rule.
        1: apply (p_eq _ (fun '(a, b) => a = b)).
        now intros [] [] [[] ?].
      }

      now apply r_ret.
    }

    apply rpre_hypothesis_rule ; intros ? ? [? []].
    apply rpre_weaken_rule with (pre := P) ; [ | now simpl ; intros ? ? [] ].

    apply r_bind with (mid := fun '(a,b) '(c,d) => P (b, d) /\ a = c /\ c = (is_pure (f_g_pow (ret_both xi)))) ; [ | intros ].
    1:{
      eapply r_transR.
      1:{
        apply r_nice_swap_rule ; [ easy | easy | ].
        eapply rpost_weaken_rule.
        1: apply (p_eq _ (fun '(a, b) => a = b)).
        now intros [] [] [[] ?].
      }

      eapply r_transL.
      1:{
        apply r_nice_swap_rule ; [ easy | easy | ].
        eapply rpost_weaken_rule.
        1: apply (p_eq _ (fun '(a, b) => a = b)).
        now intros [] [] [[] ?].
      }

      now apply r_ret.
    }

    apply rpre_hypothesis_rule ; intros ? ? [? []].
    eapply rpre_weaken_rule with (pre := P) ; [ | now simpl ; intros ? ? [] ].

    apply r_ret.
    now intros ? ? ? ; subst.
  Qed.

  Lemma ovn_bind_rhs :
    forall P,
    forall (xi : v_Z)
      ((* w *) d r : Arit (uniform #|'Z_q|)),
    forall (a₀ : v_G)
      (a₀0 a₀1 a₀2 : v_Z)
      (a₀3 a₀4 a₀5 a₀6 : v_G),
      (⊢ ⦃ P ⦄
            x ← is_state (f_pow (ret_both a₀) (ret_both xi)) ;;
     x0 ← is_state (f_g_pow (ret_both xi)) ;;
     ret ((x0, x, a₀6, a₀5, a₀4, a₀3, a₀2, a₀1, WitnessToField (otf d), a₀0, WitnessToField (otf r)) : t_OrZKPCommit) ≈
     x ← is_state (f_pow (ret_both a₀) (ret_both xi)) ;;
     x0 ← is_state (f_g_pow (ret_both xi)) ;;
     ret ((x0, x, a₀6, a₀5, a₀4, a₀3, a₀2, a₀1, WitnessToField (otf d), a₀0, WitnessToField (otf r)): t_OrZKPCommit) 
         ⦃ (fun '(a,b) '(c, d) =>
              and (P (b, d))
                (and (@Logic.eq t_OrZKPCommit a c)
                   (c.1.1.1.1.1.1.1.1.1 =
                      (is_pure (f_g_pow (ret_both xi)),
           is_pure (f_prod (f_pow (ret_both a₀) (ret_both xi)) f_group_one))))) ⦄).
  Proof.
    intros.
    apply r_bind with (mid := fun '(a,b) '(c,d) => P (b,d) /\ a = c /\ c = is_pure (f_prod (f_pow (ret_both a₀) (ret_both xi)) f_group_one))  ; [ | intros ].
    1:{
      eapply r_transR.
      1:{
        apply r_nice_swap_rule ; [ easy | easy | ].
        eapply rpost_weaken_rule.
        1: apply (p_eq _ (fun '(a, b) => a = b)).
        now intros [] [] [[] ?].
      }

      eapply r_transL.
      1:{
        apply r_nice_swap_rule ; [ easy | easy | ].
        eapply rpost_weaken_rule.
        1: apply (p_eq _ (fun '(a, b) => a = b)).
        now intros [] [] [[] ?].
      }

      apply r_ret.
      intros ? ? ?.
      split ; [ assumption | split ; [ reflexivity | ] ].

      Misc.push_down_sides.
      setoid_rewrite (@mulg1 v_G_is_group).
      reflexivity.
    }

    apply rpre_hypothesis_rule ; intros ? ? [? []].
    apply rpre_weaken_rule with (pre := P) ; [ | now simpl ; intros ? ? [] ].

    apply r_bind with (mid := fun '(a,b) '(c,d) => P (b,d) /\ a = c /\ c = (is_pure (f_g_pow (ret_both xi)))) ; [ | intros ].
    1:{
      eapply r_transR.
      1:{
        apply r_nice_swap_rule ; [ easy | easy | ].
        eapply rpost_weaken_rule.
        1: apply (p_eq _ (fun '(a, b) => a = b)).
        now intros [] [] [[] ?].
      }

      eapply r_transL.
      1:{
        apply r_nice_swap_rule ; [ easy | easy | ].
        eapply rpost_weaken_rule.
        1: apply (p_eq _ (fun '(a, b) => a = b)).
        now intros [] [] [[] ?].
      }

      now apply r_ret.
    }

    apply rpre_hypothesis_rule ; intros ? ? [? []].
    eapply rpre_weaken_rule with (pre := P) ; [ | now simpl ; intros ? ? [] ].

    apply r_ret.
    now intros ? ? ? ; subst.
  Qed.

  Lemma maximum_ballot_secrecy_success_ovn_bind :
    forall P,
    forall     (xi : v_Z)
         (vote : 'bool)
         (w d r : Arit (uniform #|'Z_q|)),
          forall (a₀ : v_G),
            (
                ⊢ ⦃ P ⦄
    is_state
       (zkp_one_out_of_two (ret_both (WitnessToField (otf w))) (ret_both (WitnessToField (otf r)))
          (ret_both (WitnessToField (otf d))) (ret_both a₀) (ret_both xi) 
          (ret_both vote)) ≈
     is_state
       (zkp_one_out_of_two (ret_both (WitnessToField (otf w))) (ret_both (WitnessToField (otf r)))
          (ret_both (WitnessToField (otf d))) (ret_both a₀) (ret_both xi) 
          (ret_both vote)) 
  ⦃ (fun '(a,b) '(c, d) =>
     and (P (b, d))
       (and (@Logic.eq (Choice.sort (chElement t_OrZKPCommit)) a c)
          (c.1.1.1.1.1.1.1.1.1 =
          (is_pure (both_prog (f_g_pow (ret_both xi))),
           is_pure
             (both_prog
                (f_prod (f_pow (ret_both a₀) (ret_both xi)) (if vote then f_g else f_group_one))))))) ⦄).
  Proof.
    intros.

    unfold zkp_one_out_of_two at 1 2.
    repeat unfold let_both at 1.

    cbn.

    destruct vote.
    - cbn.
      unfold Build_t_OrZKPCommit at 1 2.
      cbn.
      do 7 (apply r_bind_to_post ; [ apply r_refl_alt | intros ]).
      apply (ovn_bind_lhs P xi (* w *) d r a₀ a₀0 a₀1 a₀2 a₀3 a₀4 a₀5 a₀6 ).
    - cbn.
      unfold Build_t_OrZKPCommit at 1 2.
      cbn.
      do 7 (apply r_bind_to_post ; [ apply r_refl_alt | intros ]).
      apply (ovn_bind_rhs P xi (* w *) d r a₀ a₀0 a₀1 a₀2 a₀3 a₀4 a₀5 a₀6 ).
  Fail Timeout 3 Qed. Admitted. (* 195 secs *) (* Slow *)

  Lemma r_transR_ignore :
    ∀ {A : ord_choiceType}
      (c₀ : raw_code A) (c₁ c₁' : raw_code A) L,
      ⊢ ⦃ heap_ignore L ⦄ c₁ ≈ c₁' ⦃ Logic.eq ⦄ →
      ⊢ ⦃ heap_ignore L ⦄ c₀ ≈ c₁ ⦃ pre_to_post (heap_ignore L) ⦄ →
      ⊢ ⦃ heap_ignore L ⦄ c₀ ≈ c₁' ⦃ pre_to_post (heap_ignore L) ⦄.
  Proof.
    intros A c₀ c₁ c₁' L he h.
    eapply rrewrite_eqDistrR. 1: exact h.
    intro s.
    eapply rcoupling_eq.
    1: exact he.
    apply heap_ignore_refl.
  Qed.

  Lemma maximum_ballot_secrecy_success_ovn:
    ∀ LA A,
      ValidPackage (LA) [interface
                         #val #[ MAXIMUM_BALLOT_SECRECY ] : chInp → chOut
        ] A_export A →
      fdisjoint LA (MyAlg.Sigma_locs) →
      ɛ_maximum_ballot_secrecy_OVN A = 0%R.
  Proof.
    intros.

    (**********)
    (* Unfold *)
    (**********)
    (* { *)

      apply: (eq_rel_perf_ind_eq).
      (* 1: rewrite <- fset0E ; rewrite fset0U ; apply fsubsetUl. *)
      2: rewrite <- fset0E ; apply fdisjoints0.
      2: apply H0.
      rename H0 into H_disj.
      clear H.

      unfold eq_up_to_inv.

      intros.
      unfold get_op_default.

      rewrite <- fset1E in H.
      apply (ssrbool.elimT (fset1P _ _)) in H.
      inversion H.

      subst.
      simpl.

      destruct choice_type_eqP ; [ | subst ; contradiction ].
      destruct choice_type_eqP ; [ | subst ; contradiction ].
      subst.
      rewrite !cast_fun_K.

      clear e e0.

      destruct x as [? [[i xi] vote]].
      fold chElement.

      unfold code_link at 1. fold @code_link.

      unfold lookup_op.
      simpl.

      destruct choice_type_eqP ; [ | subst ; contradiction ].
      destruct choice_type_eqP ; [ | subst ; contradiction ].
      subst.
      rewrite !cast_fun_K.

      clear e e0.

      rewrite bind_assoc.
      simpl (bind (ret _) _).

      destruct choice_type_eqP ; [ | subst ; contradiction ].
      destruct choice_type_eqP ; [ | subst ; contradiction ].
      subst.
      rewrite !cast_fun_K.

      clear e e0.

      destruct choice_type_eqP ; [ | subst ; contradiction ].
      destruct choice_type_eqP ; [ | subst ; contradiction ].
      subst.
      rewrite !cast_fun_K.

      clear e e0.

      unfold cast_vote at 1.
      fold chElement.

      simpl (bind (putr _ _ _)). hnf.

      eapply r_transR.
      1:{
        apply r_bind_feq ; [ apply rreflexivity_rule | intros ].
        (* apply better_r_put_get_rhs. *)
        rewrite !otf_fto.
        replace (MyParam.R _ _) with (true).
        2:{
          symmetry.
          unfold MyParam.R.
          simpl.
          (* symmetry. *)
          repeat (apply /andP ; split).
          - apply /eqP.
            rewrite pow_witness_to_field.
            rewrite !(proj1 both_equivalence_is_pure_eq (pow_base _)).
            unfold HGPA.HacspecGroup.g.
            rewrite WitnessToFieldCancel.
            now Misc.push_down_sides.
          - apply eqxx.
          - apply /eqP.
            unfold HGPA.HacspecGroup.g.
            unfold "_ * _"%g ; simpl ; unfold setoid_lower2 , F , sg_prod, U ; simpl.
            rewrite pow_witness_to_field.
            rewrite WitnessToFieldCancel.
            Misc.push_down_sides.
            now destruct vote.
        }
        unfold assertD.
        apply rreflexivity_rule.
      }
      hnf.

      (* eapply r_transR ; [ | ]. *)
      (* { *)
      (*   apply r_nice_swap_rule ; [ easy | easy | ]. *)
      (*   apply r_bind_feq ; [ apply rreflexivity_rule | intros ]. *)

      (*   unfold bind ; fold @bind. *)
      (*   (* apply (bobble_sample_uniform_putr (ℓ := setup_loc) #|'Z_q|). *) *)
      (*   (* 1: { *) *)
      (*   (*   intros. *) *)
      (*   (*   all: repeat (apply valid_sampler ; intros). *) *)
      (*   (*   all: apply valid_bind ; intros. *) *)
      (*   (*   all: apply valid_bind ; intros. *) *)
      (*   (*   all: try apply valid_bind ; intros. *) *)
      (*   (*   all: try apply (ChoiceEquality.is_valid_code (both_prog_valid _)). *) *)
      (*   (*   all: try (apply valid_scheme ; apply valid_ret). *) *)
      (*   (*   set (let_both _ _). *) *)
      (*   (*   apply (ChoiceEquality.is_valid_code (both_prog_valid b)). *) *)
      (*   (* } *) *)
      (*   (* eapply r_uniform_bij with (f := id) ; [ now apply inv_bij | intros w ]. *) *)

      (*   apply (bobble_sample_uniform_putr (ℓ := setup_loc) #|'Z_q|). *)
      (*   1: { *)
      (*     intros. *)
      (*     all: repeat (apply valid_sampler ; intros). *)
      (*     all: apply valid_bind ; intros. *)
      (*     all: apply valid_bind ; intros. *)
      (*     all: try apply valid_bind ; intros. *)
      (*     all: try apply (ChoiceEquality.is_valid_code (both_prog_valid _)). *)
      (*     all: try (apply valid_scheme ; apply valid_ret). *)
      (*     set (let_both _ _). *)
      (*     apply (ChoiceEquality.is_valid_code (both_prog_valid b)). *)
      (*   } *)
      (*   eapply r_uniform_bij with (f := id) ; [ now apply inv_bij | intros d ]. *)

      (*   apply (bobble_sample_uniform_putr (ℓ := setup_loc) #|'Z_q|). *)
      (*   1: { *)
      (*     intros. *)
      (*     all: repeat (apply valid_sampler ; intros). *)
      (*     all: apply valid_bind ; intros. *)
      (*     all: apply valid_bind ; intros. *)
      (*     all: try apply valid_bind ; intros. *)
      (*     all: try apply (ChoiceEquality.is_valid_code (both_prog_valid _)). *)
      (*     all: try (apply valid_scheme ; apply valid_ret). *)
      (*     set (let_both _ _). *)
      (*     apply (ChoiceEquality.is_valid_code (both_prog_valid b)). *)
      (*   } *)
      (*   eapply r_uniform_bij with (f := id) ; [ now apply inv_bij | intros r ]. *)

      (*   apply rreflexivity_rule. *)
      (* } *)
      (* hnf. *)
      
      eapply r_transR ; [ | ].
      {
        apply r_nice_swap_rule ; [ easy | easy | ].
        
        apply bobble_sampleC ; fold @bind.
        eapply r_uniform_bij with (f := id) ; [ now apply inv_bij | intros w ].
        apply bobble_sampleC ; fold @bind.
        eapply r_uniform_bij with (f := id) ; [ now apply inv_bij | intros d ].
        apply bobble_sampleC ; fold @bind.
        eapply r_uniform_bij with (f := id) ; [ now apply inv_bij | intros r ].

        apply rreflexivity_rule.
      }
      hnf.

      eapply r_uniform_bij with (f := id) ; [ now apply inv_bij | intros w ].
      eapply r_uniform_bij with (f := id) ; [ now apply inv_bij | intros d ].
      eapply r_uniform_bij with (f := id) ; [ now apply inv_bij | intros r ].

      (rewrite !bind_rewrite || rewrite !bind_assoc).
      (rewrite !bind_rewrite || rewrite !bind_assoc).
      fold chElement.
      (rewrite !bind_rewrite || rewrite !bind_assoc).
      fold chElement.
      rewrite bind_rewrite.
      rewrite bind_rewrite.
      unfold f_parameter_cursor.
      do 5 unfold prod_both at 1.
      simpl (is_pure _).

      rewrite bind_rewrite.
      rewrite bind_assoc.

      replace (f_cvp_i (solve_lift ret_both _)) with (ret_both i) by now apply both_eq.
      replace (f_cvp_xi (solve_lift ret_both _)) with (ret_both xi) by now apply both_eq.
      replace (f_cvp_vote (solve_lift ret_both _)) with (ret_both vote) by now apply both_eq.
      replace (f_cvp_zkp_random_w (solve_lift ret_both _)) with (ret_both (WitnessToField (otf w))) by now apply both_eq.
      replace (f_cvp_zkp_random_d (solve_lift ret_both _)) with (ret_both (WitnessToField (otf d))) by now apply both_eq.
      replace (f_cvp_zkp_random_r (solve_lift ret_both _)) with (ret_both (WitnessToField (otf r))) by now apply both_eq.

      set (b := zkp_one_out_of_two (ret_both (WitnessToField (otf w))) (ret_both (WitnessToField (otf r))) (ret_both (WitnessToField (otf d)))  ).

      simpl (is_state _) at 2.
      setoid_rewrite bind_rewrite.
      unfold Hacspec_Lib_Pre.Ok.
      simpl (is_state _) at 2.
      setoid_rewrite bind_rewrite.

      assert (forall {A B C} (y : both A) (g : both B -> both C) (f : both A -> both B),
                 (letb ' x := y in g (f x)) = (g (letb 'x := y in f x))) by reflexivity.
      set (let_both _ _).
      assert (b0 = ControlFlow_Continue (letb ' g_pow_yi := compute_g_pow_yi (cast_int (WS2 := U32) (ret_both i)) (f_g_pow_xis (ret_both s))
                                           in letb ' zkp_vi
                                         := zkp_one_out_of_two (ret_both (WitnessToField (otf w)))
                                              (ret_both (WitnessToField (otf r))) (ret_both (WitnessToField (otf d))) g_pow_yi
                                              (ret_both xi) (ret_both vote)
                                           in letb ' g_pow_xi_yi_vi
                                         := compute_group_element_for_vote (ret_both xi) (ret_both vote) g_pow_yi
                                           in letb ' cast_vote_state_ret := f_branch (ret_both s)
                                           in letb ' cast_vote_state_ret0
                                         := Build_t_OvnContractState [cast_vote_state_ret]
                                              ( f_g_pow_xi_yi_vis := update_at_usize (f_g_pow_xi_yi_vis cast_vote_state_ret)
                                                                       (cast_int (WS2 := U32) (ret_both i)) g_pow_xi_yi_vi)
                                           in letb ' cast_vote_state_ret1
                                         := Build_t_OvnContractState [cast_vote_state_ret0]
                                              ( f_zkp_vis := update_at_usize (f_zkp_vis cast_vote_state_ret0)
                                                               (cast_int (WS2 := U32) (ret_both i)) zkp_vi)
                                           in prod_b (f_accept, cast_vote_state_ret1))) by reflexivity.
      subst b0.
      rewrite H1. clear H0 H1.

      rewrite bind_assoc.
      setoid_rewrite bind_rewrite.
      unfold Hacspec_Lib_Pre.Ok.
      simpl (is_state _) at 2.
      
      match goal with
      | |- context [ bind (is_state _) ?f ] => set (lhs := f)
      end.

      replace (lhs) with (fun (temp : (v_A × t_OvnContractState)%pack) => ret (Option_Some temp.2)) by now apply functional_extensionality ; intros []. subst lhs. hnf.

    (* } *)

    (* apply (maximum_ballot_secrecy_success_ovn_unfold LA A H H0). *)

    (*****************)
    (* End of Unfold *)
    (*****************)

    (***************************)
    (* Actual equality of code *)
    (***************************)

      assert (r_swap_eq : forall {A} (a b : raw_code A),
                 ⊢ ⦃ λ '(s₀, s₁), s₀ = s₁ ⦄ a ≈ b ⦃ λ '(b₀, s₀) '(b₁, s₁), b₀ = b₁ ∧ s₀ = s₁ ⦄ <->
                 ⊢ ⦃ λ '(s₀, s₁), s₀ = s₁ ⦄ a ≈ b ⦃ Logic.eq ⦄).
      {
        clear ; intros.
        split ; intros.
        - eapply rpost_weaken_rule.
          1: apply H.
          now intros [] [] ?.
        - eapply rpost_weaken_rule.
          1: apply H.
          now intros [] [] ?.
      }


    eapply r_transL.
    1:{
      apply r_nice_swap_rule ; [ easy | easy | ].
      apply r_swap_eq ; apply somewhat_let_substitution ; apply r_swap_eq.
      apply rreflexivity_rule.
    }
    apply r_bind_to_post ; [ apply r_refl_alt | intros ].
    
    (* apply better_r_put_rhs. *)

    rewrite !WitnessToFieldCancel.

    eapply r_transR.
    1:{
      apply r_nice_swap_rule ; [ easy | easy | ];
      rewrite bind_assoc;
      setoid_rewrite bind_rewrite ;
      apply r_nice_swap_rule ; [ easy | easy | ].
      simpl.
      apply rreflexivity_rule.
    }

    replace (_ == _) with vote.
    2:{
      symmetry.
      apply /eqP.
      unfold HGPA.HacspecGroup.g.

      unfold "_ * _"%g ; simpl ; unfold setoid_lower2 , F , sg_prod, U ; simpl.

      rewrite pow_witness_to_field.
      rewrite WitnessToFieldCancel.
      Misc.push_down_sides.

      destruct vote.
      - reflexivity.
      - red ; intros.
        apply generator_is_not_one.
        apply both_equivalence_is_pure_eq.
        set (ret_both _) in H0.

        rewrite <- (@mul1g v_G_is_group).
        rewrite <- mulVg.
        rewrite <- mulgA.
        rewrite hacspec_function_guarantees2 in H0.
        setoid_rewrite H0.

        rewrite mulgA.
        rewrite mulVg.
        rewrite (@mul1g v_G_is_group).
        reflexivity.
    }

    eapply r_transL.
    1:{
      apply r_nice_swap_rule ; [ easy | easy | ].
      apply r_swap_eq ; set (f := fun _ => _) at 3 ; apply (somewhat_let_substitution _ _ _ f) ; subst f ; hnf ; apply r_swap_eq.
      apply rreflexivity_rule.
    }

    set (m0 := is_state _) ;
      match goal with | |- context [ ⊢ ⦃ ?pre ⦄ ?lhs ≈ ?rhs ⦃ ?post ⦄ ] => set (P := pre) end.
    eapply r_bind ; [apply (maximum_ballot_secrecy_success_ovn_bind P xi vote w d r a₀) | ].
    intros [[[[[[[[[[]]]]]]]]]] [[[[[[[[[[]]]]]]]]]].
    apply rpre_hypothesis_rule ; intros ? ? [? []].
    eapply rpre_weaken_rule with (pre := P) ; [ | now simpl ; intros ? ? [] ].
    rewrite ret_cancel.
    2,3: now simpl ; simpl in H2 ; inversion H2.
    fold chElement in *.
    simpl ; simpl in H2. inversion H2. inversion_clear H1. clear H2.
    clear H0.

    eapply r_transR.
    1:{
      apply r_nice_swap_rule ; [ easy | easy | ];
      rewrite bind_assoc;
      setoid_rewrite bind_rewrite ;
      apply r_nice_swap_rule ; [ easy | easy | ].
      apply rreflexivity_rule.
    }
    subst P.
    eapply r_bind_to_post.
    2:{
      intros [].
      apply r_ret.
      now simpl ; intros ? ? [] ; subst.
    }
    simpl.
    rewrite !otf_fto.

    Misc.pattern_lhs_approx ;
      Misc.pattern_rhs_approx ;
    assert (H0 = H1) ; [ subst H0 H1 | rewrite H2 ].
    2:{
      match goal with | |- context [ ⊢ ⦃ ?pre ⦄ ?lhs ≈ ?rhs ⦃ ?post ⦄ ] => set (P := pre) end.
      subst H1.
      set (let_both _ _).
      apply (r_refl_alt b0 P).
    }
    now repeat (apply f_equal || (apply functional_extensionality ; intros) || f_equal).
  Qed. (* Slow? *)

  Definition ɛ_maximum_ballot_secrecy A :=
    AdvantageE
      (maximum_ballot_secrecy_real)
      (maximum_ballot_secrecy_ideal)
      A.

  Section better_eq_upto_inv_perf_ind.
    #[local] Open Scope rsemantic_scope.

    #[local] Open Scope fset.
    #[local] Open Scope fset_scope.
    #[local] Open Scope type_scope.
    #[local] Open Scope package_scope.
    #[local] Open Scope ring_scope.
    #[local] Open Scope real_scope.

    Lemma eq_upto_inv_perf_ind :
      ∀ {L_pub₀ L₀ L_pub₁ L₁ LA E} (p₀ p₁ : raw_package) (I : precond) (A : raw_package)
        `{ValidPackage (L_pub₀ :|: L₀) Game_import E p₀}
        `{ValidPackage (L_pub₁ :|: L₁) Game_import E p₁}
        `{ValidPackage ((L_pub₀ :|: L_pub₁) :|: LA) E A_export A},
        INV' L₀ L₁ I →
        I (empty_heap, empty_heap) →
        fdisjoint ((L_pub₀ :|: L_pub₁) :|: LA) L₀ →
        fdisjoint ((L_pub₀ :|: L_pub₁) :|: LA) L₁ →
        eq_up_to_inv E I p₀ p₁ →
        AdvantageE p₀ p₁ A = 0%R.
    Proof.
      intros L_pub₀ L₀ L_pub₁ L₁ LA E p₀ p₁ I A vp₀ vp₁ vA hI' hIe hd₀ hd₁ hp.
      unfold AdvantageE, Pr.
      pose r := get_op_default A RUN Datatypes.tt.
      assert (hI : INV ((L_pub₀ :|: L_pub₁) :|: LA) I).
      { unfold INV. intros s₀ s₁. split.
        - intros hi l hin. apply hI'.
          + assumption.
          + move: hd₀ => /fdisjointP hd₀. apply hd₀. assumption.
          + move: hd₁ => /fdisjointP hd₁. apply hd₁. assumption.
        - intros hi l v hin. apply hI'.
          + assumption.
          + move: hd₀ => /fdisjointP hd₀. apply hd₀. assumption.
          + move: hd₁ => /fdisjointP hd₁. apply hd₁. assumption.
      }
      unshelve epose proof (eq_up_to_inv_adversary_link p₀ p₁ I r hI hp) as h.
      1:{
        eapply valid_get_op_default.
        - eauto.
        - auto_in_fset.
      }
      assert (
          ∀ x y : tgt RUN * heap_choiceType,
            (let '(b₀, s₀) := x in λ '(b₁, s₁), b₀ = b₁ ∧ I (s₀, s₁)) y →
            (fst x == true) ↔ (fst y == true)
        ) as Ha.
      { intros [b₀ s₀] [b₁ s₁]. simpl.
        intros [e ?]. rewrite e. intuition auto.
      }
      unfold Pr_op.
      Locate thetaFstd.
      unshelve epose (rhs := StateTransfThetaDens.thetaFstd _ (repr (code_link r p₀)) empty_heap).
      simpl in rhs.
      epose (lhs := Pr_op (A ∘ p₀) RUN Datatypes.tt empty_heap).
      assert (lhs = rhs) as he.
      { subst lhs rhs.
        unfold Pr_op. unfold Pr_code.
        unfold StateTransfThetaDens.thetaFstd. simpl. apply f_equal2. 2: reflexivity.
        apply f_equal. apply f_equal.
        rewrite get_op_default_link. reflexivity.
      }
      unfold lhs in he. unfold Pr_op in he.
      rewrite he.
      unshelve epose (rhs' := StateTransfThetaDens.thetaFstd _ (repr (code_link r p₁)) empty_heap).
      simpl in rhs'.
      epose (lhs' := Pr_op (A ∘ p₁) RUN Datatypes.tt empty_heap).
      assert (lhs' = rhs') as e'.
      { subst lhs' rhs'.
        unfold Pr_op. unfold Pr_code.
        unfold StateTransfThetaDens.thetaFstd. simpl. apply f_equal2. 2: reflexivity.
        apply f_equal. apply f_equal.
        rewrite get_op_default_link. reflexivity.
      }
      unfold lhs' in e'. unfold Pr_op in e'.
      rewrite e'.
      unfold rhs', rhs.
      unfold SDistr_bind. unfold SDistr_unit.
      rewrite !dletE.
      assert (
          ∀ x : Datatypes_bool__canonical__choice_Choice * heap_choiceType,
            ((let '(b, _) := x in dunit (R:=R) (T:=Datatypes_bool__canonical__choice_Choice) b) true) ==
              (x.1 == true)%:R
        ) as h1.
      { intros [b s].
        simpl. rewrite dunit1E. apply/eqP. reflexivity.
      }
      assert (
          ∀ y,
            (λ x : Datatypes_prod__canonical__choice_Choice (tgt RUN) heap_choiceType, (y x)%R * ((let '(b, _) := x in dunit (R:=R) (T:=tgt RUN) b) true)) =
              (λ x : Datatypes_prod__canonical__choice_Choice (tgt RUN) heap_choiceType, (x.1 == true)%:R * (y x))
        ) as Hrew.
      { intros y. extensionality x.
        destruct x as [x1 x2].
        rewrite dunit1E.
        simpl. rewrite GRing.mulrC. reflexivity.
      }
      rewrite !Hrew.
      unfold TransformingLaxMorph.rlmm_from_lmla_obligation_1. simpl.
      unfold SubDistr.SDistr_obligation_2. simpl.
      unfold OrderEnrichedRelativeAdjunctionsExamples.ToTheS_obligation_1.
      rewrite !SDistr_rightneutral. simpl.
      pose proof (Pr_eq_empty _ _ _ _ h hIe Ha) as Heq.
      simpl in Heq.
      unfold θ_dens in Heq.
      simpl in Heq. unfold pr in Heq.
      simpl in Heq.
      rewrite Heq.
      rewrite /StateTransfThetaDens.unaryStateBeta'_obligation_1.
      assert (∀ (x : R), `|x - x| = 0%R) as Hzero.
      { intros x.
        assert (x - x = 0%R) as H3.
        { apply /eqP. rewrite GRing.subr_eq0. intuition. }
        rewrite H3. apply Num.Theory.normr0.
      }
      apply Hzero.
    Qed.

    Lemma heap_ignore_is_pred : forall L,
        (heap_ignore_pred (fun ℓ => ℓ \in L)) =
          (heap_ignore (L)).
    Proof.
      intros.
      apply functional_extensionality.
      intros [].
      unfold heap_ignore_pred, heap_ignore.
      rewrite boolp.propeqE.
      split ; intros ; apply H ; now destruct (in_mem) in H0 |- *.
    Qed.

  End better_eq_upto_inv_perf_ind.

  Lemma maximum_ballot_secrecy_setup_success:
    ∀ LA A,
      ValidPackage LA [interface #val #[ MAXIMUM_BALLOT_SECRECY_SETUP ] : chInp → chAuxInp
        ] A_export A →
      fdisjoint LA (fset [::]) →
    AdvantageE (maximum_ballot_secrecy_real_setup) (maximum_ballot_secrecy_ideal_setup) A = 0%R
    (* maximum_ballot_secrecy_real_setup ≈₀ maximum_ballot_secrecy_ideal_setup *).
  Proof.
    intros ? ? H_valid_package H_disj.

    eapply (eq_rel_perf_ind_eq).
    1: apply maximum_ballot_secrecy_real_setup.
    1: apply maximum_ballot_secrecy_ideal_setup.
    2: apply H_valid_package.
    2,3: now try rewrite fset0E.
    1:{
      unfold eq_up_to_inv.
      intros ? ? ? ? H_id.
      unfold get_op_default.

      Opaque MyAlg.Simulate.

      unfold lookup_op.

      rewrite !setmE.
      rewrite <- fset1E in H_id.
      rewrite in_fset1 in H_id.
      apply (ssrbool.elimT eqP) in H_id.
      inversion H_id ; subst.

      rewrite eqxx.
      unfold ".2".
      unfold mkdef.

      destruct choice_type_eqP ; [ | now apply r_ret ].
      destruct choice_type_eqP ; [ | now apply r_ret ].
      subst.
      rewrite !cast_fun_K.
      clear e e0.

      destruct x as [state [[cvp_i cvp_xi] cvp_vote]].

      (* Actual protocol *)

      eapply r_bind_to_post ; [ apply r_refl_alt | intros ].

      (* apply r_const_sample_R ; [ apply LosslessOp_uniform | intros ]. *)
      (* apply r_const_sample_R ; [ apply LosslessOp_uniform | intros ]. *)

      (* apply better_r_put_lhs. *)
      (* apply better_r_put_rhs. *)

      apply r_ret.
      intros ? ? ?. subst.

      split ; [ | reflexivity ].
      f_equal.
      f_equal.
      repeat (rewrite pair_equal_spec ; split).
      - rewrite !(proj1 both_equivalence_is_pure_eq (pow_base _)).
        rewrite pow_witness_to_field.
        rewrite WitnessToFieldCancel.
        unfold g.
        now Misc.push_down_sides.
      - reflexivity.
      - rewrite pow_witness_to_field.
        rewrite WitnessToFieldCancel.
        destruct cvp_vote ; [ rewrite expg1 | rewrite expg0 ] ; now Misc.push_down_sides.
    }
  Qed.

  Lemma maximum_ballot_secrecy_return_success:
    maximum_ballot_secrecy_real_return ≈₀ maximum_ballot_secrecy_ideal_return.
  Proof.
    intros.
    unfold ɛ_maximum_ballot_secrecy.
    unfold maximum_ballot_secrecy_real.
    unfold maximum_ballot_secrecy_ideal.
    apply: eq_rel_perf_ind_eq.
    all: ssprove_valid.
    1:{
      unfold eq_up_to_inv.
      intros.
      unfold get_op_default.

      Opaque MyAlg.Simulate.

      simpl (lookup_op _ _) ; fold chElement.

      rewrite !setmE.
      rewrite <- fset1E in H.
      rewrite in_fset1 in H.
      apply (ssrbool.elimT eqP) in H.
      inversion H ; subst.

      rewrite eqxx.
      simpl.

      destruct choice_type_eqP ; [ | now apply r_ret ].
      destruct choice_type_eqP ; [ | now apply r_ret ].
      subst.
      rewrite !cast_fun_K.
      clear e e0.

      destruct x as [[state [[cvp_i cvp_xi] cvp_vote]] transcript].

      destruct transcript as [[[zkp_xhy zkp_abab] zkp_c] zkp_rdrd].
      destruct (otf zkp_xhy) as [[x h] y] eqn:zkp_xhy_eq.
      destruct (otf zkp_abab) as [[[zkp_a1 zkp_b1] zkp_a2] zkp_b2] eqn:zkp_abab_eq.
      destruct (otf zkp_rdrd) as [[[zkp_r1 zkp_d1] zkp_r2] zkp_d2] eqn:zkp_rdrd_eq.
      
      repeat (set (f := fun _ => _) at 3 ; apply (somewhat_let_substitution _ _ _ f) ; subst f ; hnf ; apply (somewhat_substitution _) ; rewrite bind_rewrite).
      apply (somewhat_substitution _) ; rewrite bind_rewrite.

      apply r_nice_swap_rule ; [ easy | easy | ].
      repeat (set (f := fun _ => _) at 3 ; apply (somewhat_let_substitution _ _ _ f) ; subst f ; hnf ; apply (somewhat_substitution _) ; rewrite bind_rewrite).
      apply (somewhat_substitution _) ; rewrite bind_rewrite.

      apply r_ret.
      split ; [ | easy ].
      unfold prod_both at 1.
      simpl.

      rewrite !zkp_xhy_eq.
      rewrite !zkp_abab_eq.
      rewrite !zkp_rdrd_eq.
      simpl.

      reflexivity.
    }
  Qed. (* 9.051 secs.. *)

  Lemma swap_two_fset :
    (forall T a b, fset (T := T) [a;b] = fset [b;a]).
  Proof.
    intros.
    rewrite !fset_cons.
    fset_equality.
  Qed.

  Lemma swap_three_fset :
    (forall T a b c, fset (T := T) [a;b;c] = fset [c;a;b]).
  Proof.
    intros.
    rewrite !fset_cons.
    fset_equality.
  Qed.

  From Crypt Require Import SigmaProtocol.

  Lemma maximum_ballot_secrecy_success:
    ∀ LA A,
      ValidPackage (LA) [interface
                         #val #[ MAXIMUM_BALLOT_SECRECY ] : chInp → chOut
        ] A_export A →
      fdisjoint LA (MyAlg.Sigma_locs) →
      ɛ_maximum_ballot_secrecy A = 0%R.
  Proof.
    intros.

    unfold ɛ_maximum_ballot_secrecy.
    
    apply (AdvantageE_le_0 _ _ _ ).
    unfold maximum_ballot_secrecy_real, maximum_ballot_secrecy_ideal, pack.
    unfold maximum_ballot_secrecy_real_setup.
    unfold mkdef.
    rewrite <- Advantage_link.

    (* Setup is equal *)
    eapply Order.le_trans ; [ apply Advantage_triangle with (R := (par (par OR_ZKP.hacspec_or_run maximum_ballot_secrecy_real_return) maximum_ballot_secrecy_ideal_setup)) | ].

    set (AdE := AdvantageE _ _) at 2.
    rewrite (Advantage_par maximum_ballot_secrecy_real_par0 maximum_ballot_secrecy_real_setup maximum_ballot_secrecy_ideal_setup).
    2: apply (flat_valid_package _ _ _ _ (pack_valid maximum_ballot_secrecy_real_setup)).
    2, 3, 4: repeat (apply trimmed_empty_package || apply trimmed_package_cons).
    subst AdE.

    epose (maximum_ballot_secrecy_setup_success (fset [::]) A).

    rewrite (maximum_ballot_secrecy_setup_success (LA :|: MyAlg.Sigma_locs) (* ((LA :|: fset [::]) :|: (MyAlg.Sigma_locs :|: fset [::])) *) _ _ _ ) ; [ rewrite add0r | .. ].
    2:{
      eapply valid_link_upto.
      1:{
        eapply valid_link_upto.
        1: apply H.
        1: apply maximum_ballot_secrecy.
        1: apply fsubsetxx.
        1: rewrite <- fset0E ; apply fsub0set.
      }
      2: apply fsubsetUl.
      2: apply fsubsetUr.
      1:{
        eapply valid_par_upto.
        {
          unfold Parable.
          rewrite <- !fset1E.
          rewrite !domm_set ; unfold ".1".
          rewrite domm0.
          rewrite !fsetU0.
          rewrite fdisjointUl.
          rewrite !fdisjoint1s.
          reflexivity.
        }
        1: apply maximum_ballot_secrecy_real_par0.
        {
          apply (valid_ID (fset [::])).
          apply (flat_valid_package _ _ _ _ (pack_valid maximum_ballot_secrecy_real_setup)).
        }
        2:{
          rewrite <- fset0E.
          rewrite fset0U.
          apply fsubsetxx.
        }
        2:{
          rewrite <- fset_cat.
          apply fsubsetxx.
        }
        1: rewrite <- fset0E, fsetU0 ; apply fsubsetxx.
      }
    }
    2:rewrite <- fset0E ; apply fdisjoints0.

    do 2 rewrite <- (par_commut maximum_ballot_secrecy_ideal_setup _ _).
    rewrite (Advantage_par maximum_ballot_secrecy_ideal_setup maximum_ballot_secrecy_real_par0 maximum_ballot_secrecy_ideal_par0).
    2: apply (flat_valid_package _ _ _ _ (pack_valid maximum_ballot_secrecy_real_par0)).
    2, 3, 4: repeat (apply trimmed_empty_package || apply trimmed_package_cons).

    unfold maximum_ballot_secrecy_real_par0, maximum_ballot_secrecy_ideal_par0, pack.


    (* Return is equal *)
    eapply Order.le_trans ; [ apply Advantage_triangle with (R := (par OR_ZKP.hacspec_or_run maximum_ballot_secrecy_ideal_return)) | ].

    set (AdE := AdvantageE _ _) at 2.
    rewrite (Advantage_par hacspec_or_run maximum_ballot_secrecy_real_return maximum_ballot_secrecy_ideal_return).
    2: apply (flat_valid_package _ _ _ _ (pack_valid maximum_ballot_secrecy_real_return)).
    2, 3, 4: repeat (apply trimmed_empty_package || apply trimmed_package_cons).
    subst AdE.

    erewrite maximum_ballot_secrecy_return_success with (LA := ((LA  :|: fset [::]) :|: fset [::]) :|: (MyAlg.Sigma_locs :|: fset [::])) ; [ rewrite add0r | .. ].
    3,4: rewrite <- fset0E ; rewrite fsetU0 ; apply fdisjoints0.
    2:{
      eapply valid_link.
      2:{
        eapply valid_par_upto.
        {
          unfold Parable.
          rewrite !domm_set ; unfold ".1".
          rewrite domm0.
          rewrite !fsetU0.
          rewrite domm_ID_fset.
          rewrite !fdisjoint1s.
          rewrite notin_fset.
          reflexivity.
        }
        {
          apply hacspec_or_run.
        }
        {
          apply valid_ID.
          apply (flat_valid_package _ _ _ _ (pack_valid maximum_ballot_secrecy_real_return)).
        }
        {
          apply fsubsetxx.
        }
        {
          rewrite <- fset0E.
          rewrite fset0U.
          apply fsubsetxx.
        }
        {
          rewrite <- fset_cat.
          simpl.
          apply fsubsetxx.
        }
      }
      1:{
        eapply valid_link.
        1:{
          eapply valid_link.
          1: apply H.
          apply maximum_ballot_secrecy.
        }

        eapply valid_par_upto.
        {
          unfold Parable.
          rewrite !domm_set ; unfold ".1".
          rewrite domm0.
          rewrite !fsetU0.
          rewrite domm_ID_fset.
          rewrite !fdisjoint1s.
          rewrite notin_fset.
          reflexivity.
        }
        {
          apply maximum_ballot_secrecy_ideal_setup.
        }
        {
          apply valid_ID.
          apply (flat_valid_package _ _ _ _ (pack_valid maximum_ballot_secrecy_real_par0)).
        }
        {
          rewrite <- fset0E.
          rewrite fset0U.
          apply fsubsetxx.
        }
        {
          rewrite <- fset0E.
          rewrite fset0U.
          apply fsubsetxx.
        }
        {
          rewrite <- fset_cat.
          simpl.

          rewrite swap_three_fset.
          apply fsubsetxx.
        }
      }
    }

    do 2 rewrite <- (par_commut maximum_ballot_secrecy_ideal_return _ _).
    rewrite (Advantage_par maximum_ballot_secrecy_ideal_return hacspec_or_run (pack Sigma.SHVZK_real_aux ∘ pack Sigma.SHVZK_ideal)).
    2: apply (flat_valid_package _ _ _ _ (pack_valid hacspec_or_run)).
    4: unfold trimmed ; rewrite <- link_trim_commut ; f_equal.
    2, 3, 4: repeat (apply trimmed_empty_package || apply trimmed_package_cons).

    (* OR zkp is equal *)
    eapply Order.le_trans ; [
        eapply (Advantage_triangle_chain (hacspec_or_run)
                 [
                   (pack Sigma.RUN_interactive);
                   ((Sigma.SHVZK_real_aux ∘ Sigma.SHVZK_real))
                 ]
                (SHVZK_ideal_aux ∘ Sigma.SHVZK_ideal) _)
        | unfold advantage_sum ].

    erewrite (hacspec_vs_RUN_interactive) with (LA := ((LA  :|: fset [::]) :|: fset [::]) :|: (fset [::] :|: fset [::])) ; [ rewrite add0r | .. ].
    3: rewrite <- !fset0E ; rewrite !fsetU0 ; apply H0.
    2:{
      eapply valid_link.
      2:{
        eapply valid_par_upto.
        {
          unfold Parable.
          rewrite !domm_set ; unfold ".1".
          rewrite domm0.
          rewrite !fsetU0.
          rewrite domm_ID_fset.
          rewrite !fdisjoint1s.
          rewrite notin_fset.
          reflexivity.
        }
        {
          apply maximum_ballot_secrecy_ideal_return.
        }
        {
          apply valid_ID.
          apply (flat_valid_package _ _ _ _ (pack_valid hacspec_or_run)).
        }
        {
          apply fsubsetxx.
        }
        {
          rewrite <- fset0E.
          rewrite fset0U.
          apply fsubsetxx.
        }
        {
          rewrite <- fset_cat.
          simpl.
          apply fsubsetxx.
        }
      }
      1:{
        eapply valid_link.
        1:{
          eapply valid_link.
          1: apply H.
          apply maximum_ballot_secrecy.
        }

        eapply valid_par_upto.
        {
          unfold Parable.
          rewrite !domm_set ; unfold ".1".
          rewrite domm0.
          rewrite !fsetU0.
          rewrite domm_ID_fset.
          rewrite !fdisjoint1s.
          rewrite notin_fset.
          reflexivity.
        }
        {
          apply maximum_ballot_secrecy_ideal_setup.
        }
        {
          apply valid_ID.
          apply (flat_valid_package _ _ _ _ (pack_valid maximum_ballot_secrecy_real_par0)).
        }
        {
          rewrite <- fset0E.
          rewrite fset0U.
          apply fsubsetxx.
        }
        {
          rewrite <- fset_cat.
          simpl.

          rewrite swap_two_fset.
          apply fsubsetxx.
        }
        {
          rewrite <- fset_cat.
          simpl.

          rewrite swap_three_fset.
          apply fsubsetxx.
        }
      }
    }

    erewrite (Sigma.run_interactive_shvzk MyAlg.Simulator_locs (fun x => {code r ← sample uniform #|MyParam.Challenge| ;; MyAlg.Simulate x r })) with (LA := ((LA  :|: fset [::]) :|: fset [::]) :|: (fset [::] :|: fset [::])) ; [ rewrite add0r | .. ].
    3: rewrite <- !fset0E ; rewrite !fsetU0 ; apply H0.
    2:{
      eapply valid_link.
      2:{
        eapply valid_par_upto.
        {
          unfold Parable.
          rewrite !domm_set ; unfold ".1".
          rewrite domm0.
          rewrite !fsetU0.
          rewrite domm_ID_fset.
          rewrite !fdisjoint1s.
          rewrite notin_fset.
          reflexivity.
        }
        {
          apply maximum_ballot_secrecy_ideal_return.
        }
        {
          apply valid_ID.
          apply (flat_valid_package _ _ _ _ (pack_valid hacspec_or_run)).
        }
        {
          apply fsubsetxx.
        }
        {
          rewrite <- fset0E.
          rewrite fset0U.
          apply fsubsetxx.
        }
        {
          rewrite <- fset_cat.
          simpl.
          apply fsubsetxx.
        }
      }
      1:{
        eapply valid_link.
        1:{
          eapply valid_link.
          1: apply H.
          apply maximum_ballot_secrecy.
        }

        eapply valid_par_upto.
        {
          unfold Parable.
          rewrite !domm_set ; unfold ".1".
          rewrite domm0.
          rewrite !fsetU0.
          rewrite domm_ID_fset.
          rewrite !fdisjoint1s.
          rewrite notin_fset.
          reflexivity.
        }
        {
          apply maximum_ballot_secrecy_ideal_setup.
        }
        {
          apply valid_ID.
          apply (flat_valid_package _ _ _ _ (pack_valid maximum_ballot_secrecy_real_par0)).
        }
        {
          rewrite <- fset0E.
          rewrite fset0U.
          apply fsubsetxx.
        }
        {
          rewrite <- fset_cat.
          simpl.
          rewrite swap_two_fset.
          apply fsubsetxx.
        }
        {
          rewrite <- fset_cat.
          simpl.
          rewrite swap_three_fset.
          apply fsubsetxx.
        }
      }
    }

    rewrite <- Advantage_link.

    erewrite OR_ZKP.shvzk_success with (LA := ((((LA  :|: fset [::])  :|: fset [::])  :|: fset [::]) :|: fset [::])) ; [ | .. ].
    3: rewrite <- !fset0E ; rewrite !fsetU0.
    3: apply H0.
    2:{
      eapply valid_link.
      1:{
        eapply valid_link.
        1:{
          eapply valid_link.
          1:{
            eapply valid_link.
            1: apply H.
            apply maximum_ballot_secrecy.
          }

          eapply valid_par_upto.
          {
            unfold Parable.
            rewrite !domm_set ; unfold ".1".
            rewrite domm0.
            rewrite !fsetU0.
            rewrite domm_ID_fset.
            rewrite !fdisjoint1s.
            rewrite notin_fset.
            reflexivity.
          }
          {
            apply maximum_ballot_secrecy_ideal_setup.
          }
          {
            apply valid_ID.
            apply (flat_valid_package _ _ _ _ (pack_valid maximum_ballot_secrecy_ideal_par0)).
          }
          {
            rewrite <- fset0E.
            rewrite fset0U.
            apply fsubsetxx.
          }
          {
            rewrite <- fset_cat.
            simpl.
            apply fsubsetxx.
          }
          {
            rewrite <- fset_cat.
            simpl.
            rewrite swap_three_fset.
            apply fsubsetxx.
          }
        }
        eapply valid_par_upto.
        {
          unfold Parable.
          rewrite !domm_set ; unfold ".1".
          rewrite domm0.
          rewrite !fsetU0.
          rewrite domm_ID_fset.
          rewrite !fdisjoint1s.
          rewrite notin_fset.
          reflexivity.
        }
        {
          apply maximum_ballot_secrecy_ideal_return.
        }
        {
          apply valid_ID.
          apply (flat_valid_package _ _ _ _ (pack_valid hacspec_or_run)).
        }
        {
          rewrite <- fset0E.
          rewrite fset0U.
          apply fsubsetxx.
        }
        {
          rewrite <- fset_cat.
          simpl.
          apply fsubsetxx.
        }
        {
          rewrite <- fset_cat.
          simpl.
          rewrite swap_two_fset.
          apply fsubsetxx.
        }
      }

      apply SHVZK_ideal_aux.
    }
    easy.
  Qed.

  Lemma maximum_ballot_secrecy_success_final :
    ∀ LA A,
      ValidPackage LA [interface
                         #val #[ MAXIMUM_BALLOT_SECRECY ] : chInp → chOut
        ] A_export A →
      fdisjoint LA MyAlg.Sigma_locs →
      AdvantageE
        (maximum_ballot_secrecy_ovn)
        (maximum_ballot_secrecy_ideal)
        A = 0%R.
  Proof.
    intros.
    apply (AdvantageE_le_0 _ _ _ ).
    (* Setup is equal *)
    eapply Order.le_trans ; [ apply Advantage_triangle with (R := pack maximum_ballot_secrecy_real) | ].
    epose (maximum_ballot_secrecy_success _ _ _ _).
    epose (maximum_ballot_secrecy_success_ovn _ _ _ _).
    unfold ɛ_maximum_ballot_secrecy in e.
    unfold ɛ_maximum_ballot_secrecy_OVN in e0.
    rewrite e e0.
    rewrite add0r.
    easy.
    Unshelve. all: assumption.
  Qed.
  
End OVN_proof.

