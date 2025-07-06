
(* begin details: Imports *)
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
From OVN Require Import Hacspec_ovn_group_and_field.

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

(** * OVN Group and Field *)
(* Given OVN over some t_Group and t_Field typeclasses, if we can proof group and field laws. And some minor extra properties, is enough to instantiate the full proofs. *)

(* Most of this is just boiler-plate instantiation *)
Module HacspecOvnGroupAndFieldPre (HOP : HacspecOvnParameter).
  Module OVN := HacspecOvn HOP.

  (* Include OVN. *)
  (* Export OVN. *)

  (** Group instantiation *)
  Definition both_v_G : Type := both OVN.v_G.
  Definition v_G_type : Type := OVN.v_G.

  HB.instance Definition _ : is_eq_rel both_v_G :=
    is_eq_rel.Build (both_v_G) both_equivalence _ _ _.

  #[local] Existing Instance OVN.v_G_t_Group.
  #[local] Existing Instance OVN.v_A_t_Sized.
  #[local] Existing Instance OVN.v_A_t_HasActions.
  #[local] Existing Instance OVN.v_G_t_Sized.
  #[local] Existing Instance copy.
  #[local] Existing Instance partial_eq.
  #[local] Existing Instance is_eq.
  #[local] Existing Instance clone.
  #[local] Existing Instance serialize.

  HB.instance Definition _ : is_group_op both_v_G :=
    is_group_op.Build (both_v_G)
      (f_prod)
      (f_group_inv)
      (f_group_one)
      (f_g).

  (* Hint Resolve (@f_Z _ copy partial_eq is_eq clone serialize _). *)

  Definition both_Z : Type := both f_Z.
  Definition Z_type : Type := f_Z.

  HB.instance Definition _ : is_eq_rel both_Z :=
    is_eq_rel.Build (both_Z) both_equivalence _ _ _.

  HB.instance Definition _ : is_field_op both_Z :=
    is_field_op.Build
      both_Z
      f_mul
      f_inv
      f_field_one
      f_add
      f_opp
      f_field_zero.

End HacspecOvnGroupAndFieldPre.

Module Type HacspecOvnGroupAndFieldParameter (HOP : HacspecOvnParameter).
  Module GroupAndFieldPre := HacspecOvnGroupAndFieldPre HOP.
  (* Include GroupAndFieldPre. *)
  (* Export GroupAndFieldPre. *)

  (* A proof of the group laws *)
  Parameter both_group_properties :
    is_setoid_group_properties.axioms_
      (GroupAndFieldPre.both_v_G)
      (group_op.class GroupAndFieldPre.HacspecOvnGroupAndFieldPre_both_v_G__canonical__Hacspec_ovn_group_and_field_group_op)
      (eqR.class GroupAndFieldPre.HacspecOvnGroupAndFieldPre_both_v_G__canonical__Hacspec_ovn_group_and_field_eqR).

  (* A proof of the field laws *)
  Parameter both_field_properties :
    is_setoid_field_properties.axioms_
      (GroupAndFieldPre.both_Z)
      (field_op.class GroupAndFieldPre.HacspecOvnGroupAndFieldPre_both_Z__canonical__Hacspec_ovn_group_and_field_field_op)
      (eqR.class GroupAndFieldPre.HacspecOvnGroupAndFieldPre_both_Z__canonical__Hacspec_ovn_group_and_field_eqR).
End HacspecOvnGroupAndFieldParameter.

Module HacspecOvnGroupAndField (HOP : HacspecOvnParameter) (HOGP : HacspecOvnGroupAndFieldParameter HOP).
  (* Include HOGP. *)
  (* Export HOGP. *)
  Include HOGP.GroupAndFieldPre.

  HB.instance Definition _ : is_setoid_group_properties.axioms_ _ _ _ := HOGP.both_group_properties.

  (* Any both type has a setoid lowering structure, as we have pointwise equality on [is_pure] *)
  HB.instance Definition _ : is_setoid_lower HOGP.GroupAndFieldPre.both_v_G :=
    is_setoid_lower.Build HOGP.GroupAndFieldPre.both_v_G HOGP.GroupAndFieldPre.v_G_type (fun x => is_pure x) ret_both ret_both_is_pure_cancel (fun x => erefl)  (fun x y H => proj1 both_equivalence_is_pure_eq H)  (fun x y H => both_eq_fun_ext _ _ _).

  (* We can thus define the group on [v_G] *)
  HB.instance Definition _ : fingroup.FinGroup v_G_type := fingroup.FinGroup.class (Hacspec_ovn_group_and_field_T__canonical__fingroup_FinGroup GroupAndFieldPre_both_v_G__canonical__Hacspec_ovn_group_and_field_setoid_lower_to_group).

  (* and add a notation for it *)
  Notation v_G_is_group := HacspecOvnGroupAndField_v_G_type__canonical__fingroup_FinGroup.
  Check v_G_is_group : finGroupType.

  (* Field *)
  HB.instance Definition _ := HOGP.both_field_properties.

  (* Same lowering structure as for groups, but for [Z] instead of [v_G] *)
  HB.instance Definition _ : is_setoid_lower both_Z :=
    is_setoid_lower.Build both_Z Z_type (fun x => is_pure x) ret_both ret_both_is_pure_cancel (fun x => erefl)  (fun x y H => proj1 both_equivalence_is_pure_eq H)  (fun x y H => both_eq_fun_ext _ _ _).

  HB.instance Definition _ : GRing.Field Z_type := GRing.Field.class (Hacspec_ovn_group_and_field_T__canonical__FinRing_Field HacspecOvnGroupAndField_both_Z__canonical__Hacspec_ovn_group_and_field_setoid_lower_to_field).

  Notation v_Z_is_field := HacspecOvnGroupAndField_Z_type__canonical__GRing_Field.
  Check v_Z_is_field : fieldType.
End HacspecOvnGroupAndField.

Module Type HacspecOvnGroupAndFieldExtra (HOP : HacspecOvnParameter) (HOGaFP : HacspecOvnGroupAndFieldParameter HOP).
  Module GroupAndField := HacspecOvnGroupAndField HOP HOGaFP.
  (* Include GroupAndField. *)
  (* Export GroupAndField. *)

  #[local] Existing Instance GroupAndField.OVN.v_G_t_Group.
  #[local] Existing Instance GroupAndField.OVN.v_A_t_Sized.
  #[local] Existing Instance GroupAndField.OVN.v_A_t_HasActions.
  #[local] Existing Instance GroupAndField.OVN.v_G_t_Sized.
  #[local] Existing Instance copy.
  #[local] Existing Instance partial_eq.
  #[local] Existing Instance is_eq.
  #[local] Existing Instance clone.
  #[local] Existing Instance serialize.

  (* Additional requirements and defintions *)
  Parameter pow_base : forall x, f_g_pow x ≈both f_pow f_g x. (* TODO: just have this as a definition *)
  (* Instance f_Z_t_Field' : t_Field f_Z := _. *)

  (* A secure group is of prime order and has a generator *)
  Parameter v_G_prime_order : prime #[ is_pure f_g : GroupAndField.v_G_is_group].
  Parameter v_G_g_gen : [set : GroupAndField.v_G_is_group] = <[ is_pure f_g : GroupAndField.v_G_is_group]>.
End HacspecOvnGroupAndFieldExtra.

Module Type FieldType.
  Parameter equivalent_field : fieldType.
End FieldType.

(** * Field equality *)
Module FieldEquality (SG : GroupParam) (FT : FieldType).
  (* order of g *)
  Definition q : nat := #[SG.g].

  (** Field equality *)
  Parameter WitnessToField : {rmorphism 'Z_q -> FT.equivalent_field}.
  Parameter FieldToWitness : {rmorphism FT.equivalent_field -> 'Z_q}.
  Parameter WitnessToFieldCancel :
    cancel FieldToWitness WitnessToField.
  Parameter FieldToWitnessCancel :
    cancel WitnessToField FieldToWitness.

End FieldEquality.

(** * Hacspec Group Param *)
(* Make an instance of [GroupParam] such that we can use the Schnorr framework in SSProve *)
Module HacspecGroupParam (HOP : HacspecOvnParameter) (HOGaFP : HacspecOvnGroupAndFieldParameter HOP) (HOGaFE : HacspecOvnGroupAndFieldExtra HOP HOGaFP) <: GroupParam.

  #[local] Existing Instance HOGaFE.GroupAndField.OVN.v_G_t_Group.
  #[local] Existing Instance HOGaFE.GroupAndField.OVN.v_A_t_Sized.
  #[local] Existing Instance HOGaFE.GroupAndField.OVN.v_A_t_HasActions.
  #[local] Existing Instance HOGaFE.GroupAndField.OVN.v_G_t_Sized.
  #[local] Existing Instance copy.
  #[local] Existing Instance partial_eq.
  #[local] Existing Instance is_eq.
  #[local] Existing Instance clone.
  #[local] Existing Instance serialize.

  (* The finite group type is the ovn group *)
  Definition gT : finGroupType := HOGaFE.GroupAndField.v_G_is_group.
  Definition ζ : {set gT} := [set : gT].
  Definition g :  gT := is_pure (f_g (t_Group := HOGaFE.GroupAndField.OVN.v_G_t_Group)).

  Definition g_gen : ζ = <[g]> := HOGaFE.v_G_g_gen.
  Definition prime_order : prime #[g] := HOGaFE.v_G_prime_order.
End HacspecGroupParam.

(** * Assumptions *)
(* Collection of all modules and assumptions to do the Σ Protocols *)
Module HacspecGroupAndFieldParam (HOP : HacspecOvnParameter) (HOGaFP : HacspecOvnGroupAndFieldParameter HOP) (HOGaFE : HacspecOvnGroupAndFieldExtra HOP HOGaFP).
  (* Include HOGaFE. *)
  (* Export HOGaFE. *)

  Module HacspecGroup := HacspecGroupParam HOP HOGaFP HOGaFE.
  (* Include HacspecGroup. *)
  (* Export HacspecGroup. *)

  Module FT.
    Definition equivalent_field : fieldType := HOGaFE.GroupAndField.v_Z_is_field.
  End FT.
  Module field_equality := FieldEquality HacspecGroup FT.

  Include field_equality.
  Export field_equality.

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
    destruct (Logic.eq_sym (pdiv_id (p:=q) HacspecGroup.prime_order)).
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
    destruct (Logic.eq_sym (pdiv_id (p:=q) HacspecGroup.prime_order)).
    reflexivity.
  Qed.

  (** Extra helper definitions *)
  (* pow spec, could be omitted by using iterated mul in hax code instead *)
  Theorem one_is_not_a_generator : generator HacspecGroup.ζ 1 -> False.
  Proof.
    intros.
    assert (generator HacspecGroup.ζ HacspecGroup.g) by now unfold generator ; rewrite HacspecGroup.g_gen.
    pose (generator_coprime (gT := HacspecGroup.gT) HacspecGroup.g 0).
    rewrite <- HacspecGroup.g_gen in e.
    rewrite expg0 in e.
    rewrite e in H.
    simpl in H.
    epose (prime_coprime 0 HacspecGroup.prime_order).
    rewrite e0 in H.
    unfold "_ %| _"%N in H.
    simpl in H.

    apply (ssrbool.elimN eqP H) ; clear.
    rewrite mod0n.
    reflexivity.
  Qed.

  #[local] Existing Instance HOGaFE.GroupAndField.OVN.v_G_t_Group.
  #[local] Existing Instance HOGaFE.GroupAndField.OVN.v_A_t_Sized.
  #[local] Existing Instance HOGaFE.GroupAndField.OVN.v_A_t_HasActions.
  #[local] Existing Instance HOGaFE.GroupAndField.OVN.v_G_t_Sized.
  #[local] Existing Instance copy.
  #[local] Existing Instance partial_eq.
  #[local] Existing Instance is_eq.
  #[local] Existing Instance clone.
  #[local] Existing Instance serialize.

  Theorem generator_is_not_one : f_group_one ≈both f_g -> False.
  Proof.
    intros.
    apply one_is_not_a_generator.
    setoid_rewrite (proj1 H).
    now unfold generator ; rewrite HacspecGroup.g_gen.
  Qed.

  (** * Helper properties *)

  Lemma order_ge1 : succn (succn (Zp_trunc q)) = q.
  Proof.
    rewrite <- (@pdiv_id q HacspecGroup.prime_order) at 1.
    apply Fp_cast, HacspecGroup.prime_order.
  Qed.

  Lemma trunc_pow : forall (h : HacspecGroup.gT) x, h ^+ (x %% (Zp_trunc q).+2) = h ^+ x.
    intros.
    destruct (ssrbool.elimT (cycleP HacspecGroup.g h)) ; [ | subst ].
    - unfold HacspecGroup.g.
      setoid_rewrite <- HOGaFE.v_G_g_gen.
      simpl.
      apply in_setT.
    - rewrite expgAC.
      rewrite (expgAC _ x0).
      f_equal.
      epose (@expg_mod_order HacspecGroup.gT HacspecGroup.g x).
      fold q in e.
      rewrite <- order_ge1 in e.
      intros.
      apply e ; clear e.
  Qed.

  Lemma invg_id : (forall (x : HacspecGroup.gT), x ^-1 = x ^- 1%R).
  Proof. reflexivity. Qed.

  Lemma trunc_extra : forall (h : HacspecGroup.gT), h ^+ (Zp_trunc q).+2 = 1%g.
    intros.
    rewrite <- trunc_pow.
    now rewrite modnn.
  Qed.

  Lemma reverse_opp : (forall (x : HacspecGroup.gT) (n : 'Z_q), x ^+ ((Zp_trunc (pdiv q)).+2 - n) = x ^+ GRing.opp n).
  Proof.
    intros.
    rewrite (@pdiv_id q HacspecGroup.prime_order).
    now rewrite trunc_pow.
  Qed.

  Lemma neg_is_opp : (forall (x : HacspecGroup.gT) (n : 'Z_q), x ^- n = x ^+ GRing.opp n).
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

  Lemma mulg_cancel : forall (x : HacspecGroup.gT) (y : 'Z_q),
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
    forall a b (x : HacspecGroup.gT) (y : 'Z_q),
      (a * x ^- y = b <-> a = b * x ^+ y)%g
      /\ (x ^- y * a = b <-> a = x ^+ y * b)%g.
  Proof.
    repeat split ;
      [ eapply (canRL (f := mulg^~ _) (g := mulg^~ _))
      | eapply (canLR (f := mulg^~ _) (g := mulg^~ _))
      | eapply (canRL)
      | eapply (canLR) ] ; apply (mulg_cancel x y).
  Qed.

  Lemma mulg_invg_sub : (forall (x : HacspecGroup.gT) (y z : 'Z_q), x ^+ y * x ^- z = x ^+ nat_of_ord (y - z)%R)%g.
  Proof.
    intros.
    rewrite neg_is_opp.
    rewrite <- expgD.
    now rewrite trunc_pow.
  Qed.

  Lemma mulg_invg_left_sub : (forall (x : HacspecGroup.gT) (y z : 'Z_q), x ^- y * x ^+ z = x ^+ nat_of_ord (z - y)%R)%g.
  Proof.
    intros.
    rewrite neg_is_opp.
    rewrite <- expgD.
    now rewrite trunc_pow.
  Qed.

  Lemma cyclic_always_commute : forall (x y : HacspecGroup.gT), commute x y.
  Proof.
    intros.
    destruct (ssrbool.elimT (cycleP HacspecGroup.g x)) ; [ | subst ].
    {
      unfold HacspecGroup.gT in x.
      unfold HacspecGroup.g.
      setoid_rewrite <- HOGaFE.v_G_g_gen.
      simpl.
      apply in_setT.
    }

    destruct (ssrbool.elimT (cycleP HacspecGroup.g y)) ; [ | subst ].
    {
      unfold HacspecGroup.g.
      setoid_rewrite <- HOGaFE.v_G_g_gen.
      simpl.
      apply in_setT.
    }

    apply commuteX2.
    apply commute_refl.
  Qed.

  Lemma div_cancel_Fq : forall (x : HacspecGroup.gT) (s : 'F_q), s <> 0%R -> x ^+ nat_of_ord (s / s)%R = x.
  Proof.
    intros.
    rewrite mulrV.
    2: now rewrite (unitfE) ; apply /eqP.
    now rewrite expg1.
  Qed.

  Lemma div_cancel : forall (x : HacspecGroup.gT) (s : 'Z_q), s <> 0%R -> x ^+ nat_of_ord (s / s)%R = x.
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

  (* begin details : Positivity checks *)
  #[export] Instance positive_gT : Positive #|HacspecGroup.gT|.
  Proof.
    apply /card_gt0P. exists HacspecGroup.g. auto.
  Qed.

  #[export] Instance Bool_pos : Positive #|'bool|.
  Proof.
    rewrite card_bool. done.
  Defined.

  #[export] Instance Zq_pos : Positive #|Finite.clone _ 'Z_q|.
  Proof.
    apply /card_gt0P. exists 0%R. auto.
  Defined.

  #[export] Instance prod_pos : forall {A B : finType}, Positive #|A| -> Positive #|B| -> Positive #|(prod A B : finType)|.
  Proof.
    intros.
    rewrite card_prod.
    now apply Positive_prod.
  Defined.
  (* end details *)
End HacspecGroupAndFieldParam.

Module Type HacspecGroupParamAxiom (HOP : HacspecOvnParameter) (HOGaFP : HacspecOvnGroupAndFieldParameter HOP) (HOGaFE : HacspecOvnGroupAndFieldExtra HOP HOGaFP).
  Module GaFP := HacspecGroupAndFieldParam HOP HOGaFP HOGaFE.
  (* Include GaFP. *)
  (* Export GaFP. *)

  #[local] Existing Instance HOGaFE.GroupAndField.OVN.v_G_t_Group.
  #[local] Existing Instance HOGaFE.GroupAndField.OVN.v_A_t_Sized.
  #[local] Existing Instance HOGaFE.GroupAndField.OVN.v_A_t_HasActions.
  #[local] Existing Instance HOGaFE.GroupAndField.OVN.v_G_t_Sized.
  #[local] Existing Instance copy.
  #[local] Existing Instance partial_eq.
  #[local] Existing Instance is_eq.
  #[local] Existing Instance clone.
  #[local] Existing Instance serialize.

  (* Parameter pow_witness_to_field : *)

  (* Lemma pow_witness_to_field : *)
  (*   forall (h : GaFP.HacspecGroup.gT) (b : 'Z_GaFP.q), *)
  (*     (h ^+ b = is_pure (f_pow (ret_both h) (ret_both (GaFP.WitnessToField b)))). *)
  (* Proof. *)
  (*   intros. *)
  (*   destruct b. *)
  (*   induction m. *)
  (*   - simpl. *)
  (*     rewrite expg0. *)

  (*     replace (Ordinal _) with (ord0 (n' := (Zp_trunc GaFP.q).+1)) by now apply ord_ext. *)
  (*     rewrite rmorph0. *)

  (* pow spec, could be omitted by using iterated mul in hax code instead *)
  Parameter pow_witness_to_field :
    forall (h : GaFP.HacspecGroup.gT) (b : 'Z_GaFP.q),
      (h ^+ b = is_pure (f_pow (ret_both h) (ret_both (GaFP.WitnessToField b)))).

  Parameter conversion_is_true :
    forall (b : both f_Z),
    (GaFP.HacspecGroup.g ^+ GaFP.FieldToWitness (is_pure b)) = is_pure (f_g_pow b).

    (* Taking the hash should be equal to sampling! *)
    Parameter hash_is_psudorandom :
      forall {A B} i (H : Positive i) f pre post (c0 : _ -> raw_code A) (c1 : _ -> raw_code B) l,
        (∀ x1 : Arit (uniform i), ⊢ ⦃ pre ⦄ c0 x1 ≈ c1 (f x1) ⦃ post ⦄) ->
        ⊢ ⦃ pre ⦄
          e ← sample uniform i ;;
        c0 e ≈
          x ← is_state
          (f_hash (t_Group := HOGaFE.GroupAndField.OVN.v_G_t_Group)
             (impl__into_vec
                (unsize
                   (box_new
                      (array_from_list l))))) ;; c1 x ⦃ post ⦄.
End HacspecGroupParamAxiom.
