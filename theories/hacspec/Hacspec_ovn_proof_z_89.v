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
  Instance n_pos : Positive (is_pure n).
  Proof. easy. Qed.

  Definition v_G_t_Sized : t_Sized v_G := id.
End OVN_Z89.

Module OVN_GroupAndFieldParameter_Z89 <: HacspecOvnGroupAndFieldParameter OVN_Z89.
  Module GroupAndFieldPre := HacspecOvnGroupAndFieldPre OVN_Z89.
  Include GroupAndFieldPre.

  From mathcomp Require Import ring.
  From mathcomp Require Import zify.

  Print HacspecOvnGroupAndFieldPre_both_v_G__canonical__Hacspec_ovn_group_and_field_group_op.
  Goal True.
    epose HacspecOvnGroupAndFieldPre_both_v_G__canonical__Hacspec_ovn_group_and_field_group_op.
    destruct t.
    destruct class.
    destruct Hacspec_ovn_group_and_field_is_group_op_mixin.
    epose HacspecOvnGroupAndFieldPre_both_v_G__canonical__Hacspec_ovn_group_and_field_eqR.
    destruct t.
    destruct class.
    destruct Hacspec_ovn_group_and_field_is_eq_rel_mixin.
    reflexivity.
  Qed.

  (* Lemma (forall (x y z : both int8), (x .* y .* z) = (x .* (y .* z))). *)
  (*     { *)
  (*       clear -H_assoc_through_bind ; intros. *)

  (*       unfold ".*" at 1. *)
  (*       unfold lift2_both at 1. *)
  (*       simpl. *)

  (*       unfold ".*" at 1. *)
  (*       unfold lift2_both at 1. *)
  (*       simpl. *)

  (*       unfold ".*" at 1. *)
  (*       unfold lift2_both at 1. *)
  (*       simpl. *)

  (*       unfold ".*" at 1. *)
  (*       unfold lift2_both at 1. *)
  (*       simpl. *)

  (*       rewrite H_assoc_through_bind ; [ reflexivity | ]. *)
  (*       clear ; intros. *)
  (*       unfold Hacspec_Lib_Pre.int_mul. *)

  (*       now rewrite mulwA. *)
  (*     } *)

  (* Any both type has a setoid lowering structure, as we have pointwise equality on [is_pure] *)
  
  (* HB.instance Definition _ : is_setoid_lower both_v_G := *)
  (*   is_setoid_lower.Build both_v_G v_G_type (fun x => is_pure x) ret_both ret_both_is_pure_cancel (fun x => erefl)  (fun x y H => proj1 both_equivalence_is_pure_eq H)  (fun x y H => both_eq_fun_ext _ _ _). *)

  (* Any both type has a setoid lowering structure, as we have pointwise equality on [is_pure] *)
  HB.instance Definition _ : is_setoid_lower both_v_G :=
    is_setoid_lower.Build both_v_G v_G_type (fun x => is_pure x) ret_both ret_both_is_pure_cancel (fun x => erefl)  (fun x y H => proj1 both_equivalence_is_pure_eq H)  (fun x y H => both_eq_fun_ext _ _ _).

  HB.instance Definition _ : setoid_lower.axioms_ both_v_G := _.
  (* Lemma setoid_lower : lower_rel. *)
  (* Proof. *)
  (*   destruct HB_unnamed_factory_8. *)
  (*   refine {| *)
  (*       setoid_lower.sort := both_v_G ; *)
  (*       setoid_lower.class := *)
  (*         {| *)
  (*           setoid_lower.Hacspec_ovn_group_and_field_is_eq_rel_mixin := _ ; *)
  (*           setoid_lower.Hacspec_ovn_group_and_field_is_setoid_lower_mixin := HB_unnamed_factory_8 *)
  (*         |} *)
  (*     |}. *)
  (* Qed. *)

  (* Lemma associative_f_prod : forall (A : choice_type), associative (fun (x y : A) => is_pure (lift2_both f_prod)). *)
  (* Proof. *)
  (*   intros x y z. *)
  (*   unfold f_prod. *)
  (*   cbn. *)
  (*   repeat unfold f_z_val at 1 *)
  (*   ;repeat unfold let_both at 1 *)
  (*   ;repeat unfold Build_t_z_89_ at 1. *)
  (*   rewrite !Build_t_g_z_89__equation_1. *)
  (*   cbn. *)
  (*   reflexivity. *)

  Lemma associative_through_bind :
    forall {A}
      (x : both A) (y : both A) (z : both A) (f : A -> A -> A),
      (associative f) ->
      (bind_both
         (bind_both x (λ x', bind_both y (fun y' => ret_both (f x' y'))))
         (λ xy', bind_both z (fun z' => ret_both (f xy' z')))) =
        (bind_both x (λ x', bind_both
                              (bind_both y (λ y', bind_both z (fun z' => ret_both (f y' z'))))
                              (fun yz' => ret_both (f x' yz')))).
  Proof.
    intros.
    apply both_eq.
    unfold bind_both ; simpl.
    unfold bind_raw_both ; simpl.
    rewrite H.
    f_equal.
    repeat setoid_rewrite bind_assoc.
    repeat setoid_rewrite bind_rewrite.
    setoid_rewrite H.
    reflexivity.
  Qed.

  Lemma associative_lift : forall {A : choice_type} {op : A -> A -> A},
      associative op ->
      associative (@lift2_both A A A op).
  Proof.
    intros A op H x y z.

    (* unfold ".*" at 1. *)
    unfold lift2_both at 1.
    simpl.

    (* unfold ".*" at 1. *)
    unfold lift2_both at 1.
    simpl.

    (* unfold ".*" at 1. *)
    unfold lift2_both at 1.
    simpl.

    (* unfold ".*" at 1. *)
    unfold lift2_both at 1.
    simpl.

    now rewrite associative_through_bind ; [ reflexivity | ].
  Qed.

  Lemma lift_assoc_to_setoid : forall {A : choice_type} (op : A -> A -> A),
      associative op ->
      setoid_associative (eq_relation := both_equivalence) (lift2_both op).
  Proof.
    intros.
    intros x y z.
    apply both_equivalence_is_pure_eq.
    rewrite (associative_lift H).
    reflexivity.
  Qed.

  Lemma translate_assoc_setoid : forall {A : choice_type} {op1 op2 : both A -> both A -> both A},
      (forall x y, op1 x y ≈both op2 x y) ->
      setoid_associative (eq_relation := both_equivalence) op1 ->
      setoid_associative (eq_relation := both_equivalence) op2.
  Proof.
    intros.
    intros x y z.

    rewrite <- H.
    rewrite (both_eq_fun_ext) ; [ | rewrite <- H ; reflexivity ].
    rewrite H0.
    rewrite H.
    rewrite (both_eq_fun_ext (fun x => op2 x _)) ; [ | rewrite H ; reflexivity ].
    reflexivity.
  Qed.

  Lemma mulA : forall {WS : wsize}, associative (int_mul (WS := WS)).
  Proof.
    intros WS.
    unfold int_mul at 1.
    apply associative_lift.
    apply mulwA.
  Qed.

  Definition int_op_mod {WS1 WS2} (op : both (Hacspec_Lib_Pre.int WS2) -> both (Hacspec_Lib_Pre.int WS2) -> both (Hacspec_Lib_Pre.int WS2)) (q x y : both (Hacspec_Lib_Pre.int WS1)) : both (Hacspec_Lib_Pre.int WS1) :=
    cast_int (WS2 := WS1) (int_mod (op (cast_int (WS2 := WS2) (int_mod x q)) (cast_int (WS2 := WS2) (int_mod y q))) (cast_int (WS2 := WS2) q)).

  Definition cast_word {WS1} WS2 (x : 'word WS1) : 'word WS2 := wrepr WS2 (wunsigned x).

  Definition int_op_mod_pure
    {WS1 WS2}
    (op : (Hacspec_Lib_Pre.int WS2) -> (Hacspec_Lib_Pre.int WS2) -> (Hacspec_Lib_Pre.int WS2))
    (q x y : Hacspec_Lib_Pre.int WS1) : Hacspec_Lib_Pre.int WS1 :=
    cast_word WS1
      (wmod (op (cast_word WS2 (wmod x q)) (cast_word WS2 (wmod y q))) (cast_word WS2 q)).

  Lemma small_word : forall x q, mkword q (x mod modulus q) = mkword q x.
  Proof.
    intros.
    apply word_ext.
    rewrite Zmod_mod.
    reflexivity.
  Qed.

  Lemma cast_wordI : forall WS1 WS2 (x : 'word WS1), cast_word WS2 (cast_word WS2 x) = cast_word WS2 x.
  Proof.
    intros.
    unfold cast_word.
    now rewrite wrepr_unsigned.
  Qed.

  Lemma cast_word0 : forall WS (x : 'word WS), cast_word WS x = x.
  Proof.
    intros.
    unfold cast_word.
    now rewrite wrepr_unsigned.
  Qed.

  Lemma modulus_ltS :
    forall b,
      modulus b < modulus b.+1.
  Proof.
    intros.
    rewrite <- addn1.
    rewrite modulusD.
    now apply Z.lt_mul_diag_r.
  Qed.
  
  Lemma modulus_lt :
    forall a b,
      (a < b)%nat ->
      modulus a < modulus b.
  Proof.
    intros.
    induction b.
    - now destruct a.
    - destruct (a == b) eqn:a_is_b.
      + move /eqP: a_is_b => a_is_b.
        subst.
        apply modulus_ltS.
      + etransitivity.
        1: apply IHb ; Lia.lia.
        clear.
        apply modulus_ltS.
  Qed.

  Lemma modulus_le :
    forall a b,
      (a <= b)%nat ->
      modulus a <= modulus b.
  Proof.
    intros.
    destruct (a == b) eqn:a_is_b.
    + move /eqP: a_is_b => a_is_b.
      now subst.
    + pose (modulus_lt a b).
      Lia.lia.
  Qed.

  Lemma cast_word_small : forall (WS1 WS2 : wsize) (x : 'word WS1), (WS1 <= WS2)%nat -> unsigned (cast_word WS2 x) = unsigned x.
  Proof.
    intros.
    unfold cast_word.
    simpl.
    cbn.
    rewrite Zmod_small.
    2:{
      split ; [ apply wunsigned_range | ].
      eapply Z.lt_le_trans.
      1: apply wunsigned_range.
      unfold wbase.
      now apply modulus_le.
    }
    reflexivity.
  Qed.

  Lemma is_word : forall {WS} (y : 'word WS), (0 <= toword y < modulus WS).
  Proof.
    intros ? y.
    now move /andP: (isword_word y) => [/lezP ? /ltzP ?].
  Qed.

  Lemma cast_mod_op :
    forall {WS1 WS2 : wsize} {q : both (Hacspec_Lib_Pre.int WS1)}
      {op1}
      (op2 : (Hacspec_Lib_Pre.int WS2) -> (Hacspec_Lib_Pre.int WS2) -> (Hacspec_Lib_Pre.int WS2)),
      (forall (x y : both (Hacspec_Lib_Pre.int WS1)),
          is_pure (lift2_both (int_op_mod_pure (WS2 := WS2) op2 (is_pure q)) x y) = is_pure (int_op_mod op1 q x y)) ->
      (forall (x y : Z),
          (0 <= x * y < modulus WS2) ->
          toword (op2 (wrepr WS2 (x mod toword (is_pure (both_prog q))))
             (wrepr WS2 (y mod toword (is_pure (both_prog q))))) mod toword (is_pure (both_prog q))
          = toword (op2 (wrepr WS2 x) (wrepr WS2 y)) mod toword (is_pure (both_prog q))
      ) ->
      (0 < toword (is_pure q) < modulus WS1) ->
      associative op2 ->
      (WS1 < WS2)%nat ->
      (forall (x y : 'word WS1),
          toword (op2 (wrepr WS2 (toword x mod toword (is_pure (both_prog q))))
       (wrepr WS2 (toword y mod toword (is_pure (both_prog q))))) < modulus WS2 / toword (is_pure (both_prog q))) ->
      setoid_associative (eq_relation := both_equivalence) (int_op_mod (WS1 := WS1) (WS2 := WS2) op1 q).
  Proof.
    intros.
    refine (translate_assoc_setoid _ (lift_assoc_to_setoid (A := @Hacspec_Lib_Pre.int WS1) (int_op_mod_pure op2 (is_pure q)) _)) ; [ now intros ; apply both_equivalence_is_pure_eq | ].
    unfold int_op_mod_pure.
    unfold Hacspec_Lib_Pre.int_mod.
    unfold wrepr.
    intros x y z.
    cbn.
    Set Printing Coercions.
    f_equal.
    f_equal.
    (* rewrite !cast_wordI. *)
    (* rewrite !cast_word0. *)
    unfold cast_word at 3.
    unfold unsigned.
    unfold mkword.
    cbn.
    unfold cast_word.
    cbn.

    repeat (rewrite (Zmod_small _ (modulus WS1)) ;
            [
            | split ; [ now apply Z_mod_lt | ] ;
              eapply Z.lt_le_trans ; [ now apply Z_mod_lt |] ;
              (lia || (transitivity (modulus WS1) ; [ | now apply modulus_le ] ; lia))
                ..
           ]).

    repeat (rewrite (Zmod_small (toword (is_pure (both_prog q))) (modulus _)) ;
            [
            | split ; [ easy | ]
              ; eapply Z.lt_le_trans ; [ apply H1 |]
              ; now apply modulus_le
                ..
           ]).

    repeat (rewrite (Zmod_small (_ mod toword (is_pure (both_prog q))) (modulus _)) ;
     [
     | split ; [ now apply Z_mod_lt | ] ;
       eapply Z.lt_le_trans ; [ now apply Z_mod_lt |] ;
       (lia || (transitivity (modulus WS1) ; [ | now apply modulus_le ] ; lia))
         ..
           ]).

    rewrite !Zmod_mod.

    set (x' := wrepr WS2 (toword x)).
    set (x'' := wrepr WS2 (toword x mod _)).
    set (y' := wrepr WS2 (toword y mod _)).
    set (z' := wrepr WS2 (toword z)).
    set (z'' := wrepr WS2 (toword z mod _)).
    set (q' := toword (is_pure (both_prog q))).

    unfold x'' at 1.
    rewrite <- (Zmod_mod (toword x)).
    rewrite (H0 _ _).
    2:{
      split.
      1: apply Z.mul_nonneg_nonneg ; (now apply is_word || now apply Z_mod_lt).
      eapply (Z.lt_le_trans _ ( _ * _)).
      1:{
        apply Z.mul_lt_mono_nonneg.
        2:{
          now apply Z_mod_lt.
          (* eapply Z.lt_trans ; [ now apply Z_mod_lt | ]. *)
          (* apply H1. *)
        }
        3: apply H4.
        all: (now apply is_word || now apply Z_mod_lt).
      }
      cbn.
      eapply Z.le_trans.
      1: now apply Z.mul_div_le.
      easy.
      (* rewrite <- modulusD. *)
      (* apply modulus_le. *)
      (* now destruct WS1 , WS2. *)
    }

    fold x''.
    rewrite !wrepr_unsigned.
    rewrite H2.

    unfold z'' at 2.
    rewrite <- (Zmod_mod (toword z)).
    rewrite (H0 _ _).
    2:{
      split.
      1: apply Z.mul_nonneg_nonneg ; (now apply is_word || now apply Z_mod_lt).
      eapply (Z.lt_le_trans _ ( _ * _)).
      1:{
        apply Z.mul_lt_mono_nonneg.
        4:{
          now apply Z_mod_lt.
          (* eapply Z.lt_trans ; [ now apply Z_mod_lt | ]. *)
          (* apply H1. *)
        }
        2: apply H4.
        all: (now apply is_word || now apply Z_mod_lt).
      }
      cbn.
      rewrite Z.mul_comm.
      eapply Z.le_trans.
      1: now apply Z.mul_div_le.
      easy.
    }

    fold z''.
    rewrite !wrepr_unsigned.
    reflexivity.
  Qed.

  Definition int_mul_mod {WS1 WS2} q (x y : both (Hacspec_Lib_Pre.int WS1)) : both (Hacspec_Lib_Pre.int WS1) :=
    int_op_mod (WS1 := WS1) (WS2 := WS2) (int_mul) q x y.
    (* cast_int (WS2 := WS1) (int_mod (WS := WS2) (int_mul (WS := WS2) (cast_int (WS2 := WS2) x) (cast_int(WS2 := WS2)  y)) q). *)

  Definition int_mul_mod_pure {WS1 WS2} q (x y : @Hacspec_Lib_Pre.int WS1)
    : Hacspec_Lib_Pre.int WS1 :=
    int_op_mod_pure (WS1 := WS1) (WS2 := WS2) (@mul_word _) q x y.

  Lemma mul_modA : forall {WS1 : wsize} {WS2 : wsize} (q : both (Hacspec_Lib_Pre.int WS1)),
      (1 < toword (is_pure q) < modulus WS1)%Z ->
      (WS1 < WS2)%N ->
      (modulus WS1 * modulus WS1 <= modulus WS2) ->
      (toword (is_pure (both_prog q)) * toword (is_pure (both_prog q)) <=
         modulus WS2 / toword (is_pure (both_prog q))) ->
      setoid_associative (eq_relation := both_equivalence) (int_mul_mod (WS1 := WS1) (WS2 := WS2) q).
  Proof.
    intros.
    refine (cast_mod_op (op1 := int_mul) (@mul_word _) _ _ _ _ _ _).
    - reflexivity.
    - intros.
      cbn.
      rewrite <- !Zmult_mod.
      rewrite (Zmod_small _ (modulus _)).
      2:{
        split.
        1: apply Z.mul_nonneg_nonneg ; now apply Z_mod_lt.
        eapply (Z.lt_le_trans _ ( _ * _)).
        1:{
          apply Z.mul_lt_mono_nonneg.
          1,3:  now apply Z_mod_lt.
          1,2: eapply Z.lt_trans ; [ now apply Z_mod_lt | ] ; apply H.
        }
        assumption.
      }
      rewrite <- !Zmult_mod.
      now rewrite (Zmod_small _ (modulus _)).
    - lia.
    - apply mulwA.
    - assumption.
    - intros.
      cbn.
      rewrite <- !Zmult_mod.
      assert (toword x mod toword (is_pure (both_prog q)) * (toword y mod toword (is_pure (both_prog q))) <
  modulus WS2 / toword (is_pure (both_prog q))).
      2:{
        rewrite Zmod_small.
        1: assumption.
        split.
        2:{
          eapply Z.lt_trans.
          1: apply H3.
          apply Z.div_lt.
          2: lia.
          1: now destruct WS2.
        }
        apply Z.mul_nonneg_nonneg ; now apply Z_mod_lt.
      }
      {
        eapply (Z.lt_le_trans _ ( _ * _)).
        1:{
          apply Z.mul_lt_mono_nonneg.
          1,3: now apply Z_mod_lt.
          1,2: now apply Z_mod_lt.
        }
        assumption.
      }
  Qed.

  Lemma both_group_properties :
    is_setoid_group_properties.axioms_ (both_v_G)
      (group_op.class HacspecOvnGroupAndFieldPre_both_v_G__canonical__Hacspec_ovn_group_and_field_group_op)
      (eqR.class HacspecOvnGroupAndFieldPre_both_v_G__canonical__Hacspec_ovn_group_and_field_eqR).
  Proof.
    constructor.
    - set (op := sg_prod) ; replace op with f_prod by reflexivity ; clear op.
      intros x y z. simpl in x, y, z.
      admit.
    - cbn.
      set (op := sg_prod) ; replace op with f_prod by reflexivity ; clear op.
      cbn.
      intros x.
      cbn.
      repeat unfold let_both at 1.
      repeat unfold Build_t_g_z_89_ at 1.
      apply both_equivalence_is_pure_eq.
      cbn.
      unfold f_g_val at 1.
      cbn.
      Misc.push_down_sides.
      cbn.
      repeat unfold ".%" at 1.
      unfold Hacspec_Lib_Pre.int_mod.
      cbn.
      repeat unfold lift2_both at 1.
      cbn.
      admit.
  Admitted.


  (* A proof of the field laws *)
  Lemma both_field_properties : is_setoid_field_properties.axioms_ (GroupAndFieldPre.both_Z) (field_op.class GroupAndFieldPre.HacspecOvnGroupAndFieldPre_both_Z__canonical__Hacspec_ovn_group_and_field_field_op) (eqR.class GroupAndFieldPre.HacspecOvnGroupAndFieldPre_both_Z__canonical__Hacspec_ovn_group_and_field_eqR).
  Proof.
    constructor.
    - (* intros x y z ; simpl in x , y , z. *)
      refine (translate_assoc_setoid _ _).
      1:{
        intros.
        cbn.
        apply both_equivalence_is_pure_eq.
        repeat unfold let_both at 1.
        cbn.
        instantiate (1 := fun x y => (((x .% @ret_both uint8 88)
                                      .+ (y .% @ret_both uint8 88))
                                     .% @ret_both uint8 88)).
        reflexivity.
      }

      refine (translate_assoc_setoid _ _).
      1:{
        instantiate (1 := ((fun x y => ret_both (wmod (Hacspec_Lib_Pre.int_add (wmod (is_pure x : t_z_89_) 88) (wmod (is_pure y : t_z_89_) 88)) 88 : t_z_89_)))).
        intros.
        cbn.
        apply both_equivalence_is_pure_eq.
        reflexivity.
      }

      intros x y z.
      
      apply both_equivalence_is_pure_eq.
      set (n0 := 88%nat).
      remember n0.
      cbn.

      admit.
  Admitted.

End OVN_GroupAndFieldParameter_Z89.

Module Ovn_GroupAndFieldExtra_Z89 : HacspecOvnGroupAndFieldExtra OVN_Z89 OVN_GroupAndFieldParameter_Z89.
  Module GroupAndField := HacspecOvnGroupAndField OVN_Z89 OVN_GroupAndFieldParameter_Z89.
  Include GroupAndField.
  Export GroupAndField.

  (* Additional requirements and defintions *)
  Definition pow_base : forall x, f_g_pow x ≈both f_pow f_g x.
  Proof.
    intros.

    (* cbn. *)
    unfold t_g_z_89__t_Group.
    unfold f_g_pow.
    unfold f_pow.
    reflexivity.
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
