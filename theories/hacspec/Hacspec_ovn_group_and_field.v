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
(*              OVN instantiation of group and field traits                   *)
(*                                                                            *)
(* - has all properties of group operations for v_G, and field operations for *)
(*   f_Z                                                                      *)
(* - ovn implementation with proofs of group operation, to                    *)
(*   instantiate HB instances for group and field using hacspec OVN impl      *)
(******************************************************************************)

(** * Setoid relations. *)
(* Define a version of relations like associativity and commutivitiy, using setoid equality instead of [=] *)
Section setoid_relations.
  Context {S T : Type}.

  Section SopSisS.
    Context {eq_relation : S -> S -> Prop}.
    Implicit Type (op :  S -> S -> S).
    Definition setoid_associative op := forall x y z,
        eq_relation (op x (op y z)) (op (op x y) z).
  End SopSisS.

  Section SopTisS.
    Context {eq_relation : S -> S -> Prop}.
    Implicit Type (op :  S -> T -> S).

    Definition setoid_left_zero z op := forall x, eq_relation (op z x) (z).
    Definition setoid_left_inverse e inv op := forall x, eq_relation (op (inv x) x) (e).
    Definition setoid_left_distributive op add :=
      forall x y z, eq_relation (op (add x y) z) (add (op x z) (op y z)).
    Definition setoid_right_id e op := forall x, eq_relation (op x e) (x).
  End SopTisS.

  Section SopTisT.
    Context {eq_relation : T -> T -> Prop}.
    Implicit Type (op :  S -> T -> T).
    Definition setoid_right_zero z op := forall x, eq_relation (op x z) (z).
    Definition setoid_left_id e op := forall x, eq_relation (op e x) (x).
    Definition setoid_right_distributive (op : S -> T -> T) add :=
      forall x y z, eq_relation (op x (add y z)) (add (op x y) (op x z)).
  End SopTisT.

  Section SopSisT.
    Context {eq_relation : T -> T -> Prop}.
    Implicit Type (op :  S -> S -> T).
    Definition setoid_commutative op := forall x y, eq_relation (op x y) (op y x).
  End SopSisT.

  Definition setoid_involutive {eq_relation : S -> S -> Prop} (op : S -> S) := forall x, eq_relation (op (op x)) x.
End setoid_relations.

(** * Setoid lowering *)
(* Given a setoid, we can construct a quotient type given an instance of [setoid_lower] *)

HB.mixin Record is_eq_rel (V : Type) := {
    eq_relation : V -> V -> Prop ;

    eqR_refl : RelationClasses.Reflexive eq_relation ;
    eqR_sym : RelationClasses.Symmetric eq_relation ;
    eqR_trans : RelationClasses.Transitive eq_relation ;
  }.

HB.structure Definition eqR := { V of is_eq_rel V }.

(* Quotiented setoid S into T given an equivalence on S *)
HB.mixin Record is_setoid_lower (S : Type) of eqR S :=
  {
    T : Type ;

    F : S -> T ;
    U : T -> S ;
    U_F_cancel : forall x, eq_relation (U (F x)) x ;
    F_U_cancel : cancel U F ;

    lower_to_eq : forall {x y}, eq_relation x y -> F x = F y ;
    lower_ext : forall {x y} (f : S -> S), eq_relation x y -> eq_relation (f x) (f y) ;
  }.

#[short(type="lower_rel")]
  HB.structure Definition setoid_lower := { V of is_setoid_lower V & eqR V }.

HB.instance Definition _ (SG : lower_rel) : Finite (T (s := SG)) :=  _.

(* Properties from setoid lowers to equality in the quotient type *)
Section setoid_lower_properties.
  Context {G : lower_rel}.

  Definition setoid_lower2 :=
    fun (op : G -> G -> G) => fun (x y : T) => F (s := G) (op (U (s := G) x) (U (s := G) y)).

  Definition setoid_lower1 :=
    fun (op : G -> G) => fun (x : T) => F (s := G) (op (U (s := G) x)).

  Definition setoid_lower0 :=
    fun (x : G) => F (s := G) x.

  Lemma setoid_lowerA :
    forall {op : G -> G -> G},
      setoid_associative (eq_relation := eq_relation) op ->
      associative (setoid_lower2 op).
  Proof.
    intros.
    intros x y z.
    apply lower_to_eq.
    unfold setoid_lower2.
    pose (H (U x) (U y) (U z)).

    eapply eqR_trans ; [ apply lower_ext ; apply U_F_cancel | ].
    eapply eqR_trans ; [ | apply eqR_sym ; eapply (lower_ext _ _ (op^~ (U z))) ; apply U_F_cancel ].
    apply e.
  Qed.

  Lemma setoid_lower_left_id :
    forall {e : G} {op : G -> G -> G},
      setoid_left_id (eq_relation := @eq_relation G) (e) (op) ->
      left_id (setoid_lower0 e) (setoid_lower2 op).
  Proof.
    intros.
    intros x.
    unfold setoid_lower2, setoid_lower0.
    replace (x) with (F (U x)) at 2 by apply F_U_cancel.
    apply lower_to_eq.
    eapply eqR_trans ; [ eapply (lower_ext _ _ (op^~ (U x))) ; apply U_F_cancel | ].
    apply (H (U x)).
  Qed.

  Lemma setoid_lower_involutive :
    forall {op : G -> G},
      setoid_involutive (eq_relation := @eq_relation G) (op) ->
      involutive (setoid_lower1 op).
  Proof.
    intros.
    intros x.
    unfold setoid_lower1.
    replace (x) with (F (U x)) at 2 by apply F_U_cancel.
    apply lower_to_eq.
    eapply eqR_trans ; [ eapply (lower_ext) ; apply U_F_cancel | ].
    apply (H (U x)).
  Qed.

  Lemma setoid_lower_prod_morph :
    forall {inv : G -> G} {op : G -> G -> G},
      (forall x y, eq_relation (inv (op x y)) (op (inv y) (inv x))) ->
      {morph (setoid_lower1 inv)  : x y / (setoid_lower2 op) x y >-> (setoid_lower2 op) y x}.
  Proof.
    intros.
    intros x y.
    unfold setoid_lower1, setoid_lower2.
    apply lower_to_eq.
    eapply eqR_trans ; [ eapply (lower_ext) ; apply U_F_cancel | ].
    eapply eqR_trans ; [ | apply (eqR_sym) ; eapply (lower_ext _ _ (op _)) ; apply U_F_cancel ].
    eapply eqR_trans ; [ | apply (eqR_sym) ; eapply (lower_ext _ _ (op^~ _)) ; apply U_F_cancel ].
    apply (H (U x) (U y)).
  Qed.

  Lemma setoid_lower_left_inverse :
    forall {e : G} {inv : G -> G} {op : G -> G -> G},
      setoid_left_inverse (eq_relation := eq_relation) e inv op -> left_inverse (setoid_lower0 e) (setoid_lower1 inv) (setoid_lower2 op).
  Proof.
    intros.
    intros x.
    unfold setoid_lower0, setoid_lower1, setoid_lower2.
    apply lower_to_eq.
    eapply eqR_trans ; [ eapply (lower_ext _ _ (op^~ _)) ; apply U_F_cancel | ].
    apply (H (U x)).
  Qed.

  Lemma setoid_lowerC :
    forall {op : G -> G -> G},
      setoid_commutative (eq_relation := eq_relation) op ->
      commutative (setoid_lower2 op).
  Proof.
    intros.
    intros x y.
    apply lower_to_eq.
    apply (H (U x) (U y)).
  Qed.

  Lemma setoid_lower_right_id :
    forall {e : G} {op : G -> G -> G},
      setoid_right_id (eq_relation := @eq_relation G) (e) (op) -> right_id (setoid_lower0 e) (setoid_lower2 op).
  Proof.
    intros.
    intros x.
    unfold setoid_lower2, setoid_lower0.
    replace (x) with (F (U x)) at 2 by apply F_U_cancel.
    apply lower_to_eq.
    eapply eqR_trans ; [ eapply (lower_ext _ _ (op (U x))) ; apply U_F_cancel | ].
    apply (H (U x)).
  Qed.

  Lemma setoid_lower_neq :
    forall x y, ¬ (@eq_relation G x y) -> setoid_lower0 x != setoid_lower0 y.
  Proof.
    intros.
    apply /eqP.
    red ; intros.
    apply H.
    eapply eqR_trans ; [ apply eqR_sym ; apply U_F_cancel | ].
    eapply eqR_trans ; [ | apply U_F_cancel ].
    unfold setoid_lower0 in H0.
    rewrite H0.
    apply eqR_refl.
  Qed.

  Lemma setoid_lower_left_zero :
    forall (z : G) (op : G -> G -> G),
      setoid_left_zero (eq_relation := @eq_relation G) z op -> left_zero (setoid_lower0 z) (setoid_lower2 op).
  Proof.
    intros.
    intros x.
    unfold setoid_lower2, setoid_lower0.
    apply lower_to_eq.
    eapply eqR_trans ; [ eapply (lower_ext _ _ (op^~ (U x))) ; apply U_F_cancel | ].
    apply (H (U x)).
  Qed.

  Lemma setoid_lower_right_zero :
    forall (z : G) (op : G -> G -> G),
      setoid_right_zero (eq_relation := @eq_relation G) z op -> right_zero (setoid_lower0 z) (setoid_lower2 op).
  Proof.
    intros.
    intros x.
    unfold setoid_lower2, setoid_lower0.
    apply lower_to_eq.
    eapply eqR_trans ; [ eapply (lower_ext _ _ (op (U x))) ; apply U_F_cancel | ].
    apply (H (U x)).
  Qed.

  Lemma setoid_lower_left_distributive :
    forall (opM : G -> G -> G) (opA : G -> G -> G),
      setoid_left_distributive (eq_relation := @eq_relation G) opM opA -> left_distributive (setoid_lower2 opM) (setoid_lower2 opA).
  Proof.
    intros.
    intros x y z.
    unfold setoid_lower2.
    apply lower_to_eq.
    eapply eqR_trans ; [ eapply (lower_ext _ _ (opM^~ (U z))) ; apply U_F_cancel | ].
    eapply eqR_trans ; [ | apply eqR_sym ; eapply (lower_ext _ _ (opA _)) ; apply U_F_cancel ].
    eapply eqR_trans ; [ | apply eqR_sym ; eapply (lower_ext _ _ (opA^~ _)) ; apply U_F_cancel ].
    apply (H (U x) (U y) (U z)).
  Qed.

  Lemma setoid_lower_right_distributive :
    forall (opM : G -> G -> G) (opA : G -> G -> G),
      setoid_right_distributive (eq_relation := @eq_relation G) opM opA -> right_distributive (setoid_lower2 opM) (setoid_lower2 opA).
  Proof.
    intros.
    intros x y z.
    unfold setoid_lower2.
    apply lower_to_eq.
    eapply eqR_trans ; [ eapply (lower_ext _ _ (opM _)) ; apply U_F_cancel | ].
    eapply eqR_trans ; [ | apply eqR_sym ; eapply (lower_ext _ _ (opA _)) ; apply U_F_cancel ].
    eapply eqR_trans ; [ | apply eqR_sym ; eapply (lower_ext _ _ (opA^~ _)) ; apply U_F_cancel ].
    apply (H (U x) (U y) (U z)).
  Qed.

End setoid_lower_properties.

(** * Group from setoid *)
(* Given group-like structure on the setoid, we can construct a group on the quotiented type. *)
(* We define group-like structure by [is_group_op] and [is_setoid_group_properties].          *)

HB.mixin Record is_group_op (V : Type) :=
  {
    sg_prod : V -> V -> V ;
    sg_inv : V -> V ;
    sg_one : V ;
    sg_g : V ;
  }.

HB.structure Definition group_op := { V of is_group_op V }.

HB.mixin Record is_setoid_group_properties (V : Type) of group_op V & eqR V :=
  {
    sg_prodA : setoid_associative (eq_relation := @eq_relation V) (sg_prod) ;
    sg_prod1 : setoid_left_id  (eq_relation := @eq_relation V) (sg_one) (sg_prod) ;
    sg_prodV : setoid_left_inverse (eq_relation := @eq_relation V) sg_one sg_inv sg_prod ;

    sg_invK : setoid_involutive (eq_relation := @eq_relation V) (sg_inv) ;
    sg_invM : forall x y, eq_relation (sg_inv ((@sg_prod V) x y)) ((@sg_prod V) (sg_inv y) (sg_inv x)) ;
  }.

HB.structure Definition setoid_group := { V of group_op V & eqR V & is_setoid_group_properties V }.

(* Given setoid lower relation and a setoid with group-like structure, we can lower to a group *)
#[short(type="lowerToGroup")]
  HB.structure Definition setoid_lower_to_group := { V of setoid_lower V & setoid_group V }.

(* We can define multiplicative group *)
HB.instance Definition _ (SG : lowerToGroup) : isMulBaseGroup T :=
  isMulBaseGroup.Build (T (s := SG))
    (setoid_lowerA sg_prodA)
    (setoid_lower_left_id sg_prod1)
    (setoid_lower_involutive sg_invK)
    (setoid_lower_prod_morph sg_invM).

(* The multiplicative group is a finite group, giving us an element of [fingroup.FinGroup] *)
(* from any setoid with group-like structure *)
HB.instance Definition _ (SG : lowerToGroup) :=
  BaseFinGroup_isGroup.Build (T (s := SG)) (setoid_lower_left_inverse sg_prodV).

(** * Field from setoid *)
(* Similarly given field-like structure on the setoid, we can construct a field on the quotiented *)
(* type. We define field-like structure by [is_field_op] and [is_setoid_field_properties].        *)

HB.mixin Record is_field_op (V : Type) :=
  {
    sf_mul : V -> V -> V ;
    sf_inv : V -> V ;
    sf_one : V ;

    sf_add : V -> V -> V ;
    sf_opp : V -> V ;
    sf_zero : V ;
  }.

HB.structure Definition field_op := { V of is_field_op V }.

HB.mixin Record is_setoid_field_properties (V : Type) of field_op V & eqR V :=
  {
    (** Guarantees about the field operations *)
    (* Addition is assoc, commutative and cancel with zero and opp *)
    sf_addA : setoid_associative (eq_relation := @eq_relation V) (sf_add) ;
    sf_addC: setoid_commutative (eq_relation := @eq_relation V) (sf_add) ;
    sf_add0: setoid_left_id (eq_relation := @eq_relation V) sf_zero sf_add ;
    sf_addN: setoid_left_inverse (eq_relation := @eq_relation V) (sf_zero) sf_opp sf_add ;

    (* Multiplication is assoc, commutative and cancel with one and div *)
    sf_mulA : setoid_associative (eq_relation := @eq_relation V) (sf_mul) ;
    sf_mulC : setoid_commutative (eq_relation := @eq_relation V) (sf_mul) ;
    sf_mul1 : setoid_left_id (eq_relation := @eq_relation V) sf_one sf_mul ;
    sf_mulN : setoid_left_inverse (eq_relation := @eq_relation V) (sf_one) sf_inv sf_mul ;

    sf_mul0 : setoid_left_zero (eq_relation := @eq_relation V) sf_zero sf_mul ;
    sf_inv0 : @eq_relation V (sf_inv sf_zero) sf_zero ;

    (* Mul distributes over addition *)
    sf_mulDl : setoid_left_distributive  (eq_relation := @eq_relation V) sf_mul sf_add ;
    sf_mulDr : setoid_right_distributive  (eq_relation := @eq_relation V) sf_mul sf_add ;

    (* One is not zero *)
    sf_one_not_zero : ¬ (@eq_relation V sf_one sf_zero) ;

    sf_mulV : forall x, ¬ (@eq_relation V x sf_zero)  -> @eq_relation V (sf_mul (sf_inv x) x) sf_one ;
  }.

(* Given setoid lower relation and a setoid with field-like structure, we can lower to a field *)
HB.structure Definition setoid_field := { V of is_field_op V & eqR V & is_setoid_field_properties V }.

#[short(type="lowerToField")]
  HB.structure Definition setoid_lower_to_field := { V of setoid_lower V & setoid_field V }.

(* begin details : mul1r and mul0r from mul1 and mul0 using mulC *)
(* We define mul1r from mul1 and mulC *)
Corollary mul1r_from_mul1_mulC :
  forall {A} {eq_relation : A -> A -> Prop} {one : A} {opM : A -> A -> A},
    RelationClasses.Transitive eq_relation ->
    setoid_left_id (eq_relation := eq_relation) one opM ->
    setoid_commutative (eq_relation := eq_relation) opM ->
    setoid_right_id (eq_relation := eq_relation) one opM.
Proof.
  intros.
  intros x.
  eapply H ; [ apply H1 | apply H0 ].
Qed.

(* We define mulr0 from mul0 and mulC *)
Corollary mul0r_from_mul0_mulC :
  forall {A} {eq_relation : A -> A -> Prop} {zero : A} {opM : A -> A -> A},
    RelationClasses.Transitive eq_relation ->
    setoid_left_zero (eq_relation := eq_relation) zero opM ->
    setoid_commutative (eq_relation := eq_relation) opM ->
    setoid_right_zero (eq_relation := eq_relation) zero opM.
Proof.
  intros.
  intros x.
  eapply H ; [ apply H1 | apply H0 ].
Qed.

Definition sf_mul1l {SG : lowerToField} :=
  (sf_mul1 (s := SG)).
Definition sf_mul1r {SG : lowerToField} :=
  (mul1r_from_mul1_mulC eqR_trans (sf_mul1 (s := SG)) (sf_mulC)).
Definition sf_mul0r {SG : lowerToField} :=
  (mul0r_from_mul0_mulC eqR_trans (sf_mul0 (s := SG)) (sf_mulC)).
(* end details *)

(* Our definitions get us an Nmodule, which is a SemiRing, with commutative multiplication, and thus we get a Zmodule, thus a ring *)
HB.instance Definition _ (SG : lowerToField) :=
  GRing.isNmodule.Build (T (s := SG))
    (setoid_lowerA sf_addA)
    (setoid_lowerC sf_addC)
    (setoid_lower_left_id sf_add0).

HB.instance Definition _ (SG : lowerToField) :=
  GRing.Nmodule_isSemiRing.Build (T (s := SG))
    (setoid_lowerA sf_mulA)
    (setoid_lower_left_id sf_mul1)
    (setoid_lower_right_id sf_mul1r)
    (setoid_lower_left_distributive _ _ sf_mulDl)
    (setoid_lower_right_distributive _ _ sf_mulDr)
    (setoid_lower_left_zero _ _ sf_mul0)
    (setoid_lower_right_zero _ _ sf_mul0r)
    (setoid_lower_neq _ _  sf_one_not_zero).

HB.instance Definition _ (SG : lowerToField) :=
  GRing.SemiRing_hasCommutativeMul.Build (T (s := SG)) (setoid_lowerC sf_mulC).

HB.instance Definition _  (SG : lowerToField) :=
  GRing.Nmodule_isZmodule.Build  (T (s := SG)) (setoid_lower_left_inverse sf_addN).

(* begin details : we lower mul inverse *)
(* Property of equality for fields ! *)
Parameter zero_to_zero : forall (SG : lowerToField), forall x, (@eq_relation _ (U (s := SG) x) sf_zero) -> x = setoid_lower0 sf_zero.

(* field has mul inverse *)
Lemma setoid_lower_mulVr :
  forall {G : lowerToField},
    (forall (x : G), ¬ (@eq_relation _ x sf_zero)  -> @eq_relation _ (sf_mul (sf_inv (s := G) x) x) sf_one) ->
    (forall (x : _), (x != setoid_lower0 sf_zero)  -> ((setoid_lower2 sf_mul) ((setoid_lower1 (sf_inv (s := G))) x) x) = setoid_lower0 sf_one).
Proof.
  intros ? ?.
  intros x Hneq.
  unfold setoid_lower0 , setoid_lower1 , setoid_lower2.
  apply lower_to_eq.
  eapply eqR_trans ; [ eapply (lower_ext _ _ (sf_mul^~ _)) ; apply U_F_cancel | ].
  apply (H (U x)).
  red ; intros.
  apply (ssrbool.elimN eqP Hneq) ; clear Hneq.
  now apply zero_to_zero.
Qed.

Definition f_lower_mulVr_subproof {G : lowerToField} : _ :=
  proj2 (classical_sets.in_setP ( fun (x : T (s := G)) => x != setoid_lower0 sf_zero ) (fun x => (setoid_lower2 sf_mul) ((setoid_lower1 sf_inv) x) x = setoid_lower0 sf_one)) (setoid_lower_mulVr sf_mulV).

Definition f_lower_mulrV_subproof {G : lowerToField} : _ :=
  proj2 (classical_sets.in_setP
           (fun (x : T (s := G)) => x != setoid_lower0 sf_zero )
           (fun x => setoid_lower2 sf_mul x ((setoid_lower1 sf_inv) x) = setoid_lower0 sf_one)) (fun x H => eq_ind_r (Logic.eq^~ (setoid_lower0 sf_one)) (setoid_lower_mulVr sf_mulV x H) ((setoid_lowerC sf_mulC) x (setoid_lower1 sf_inv x))).

Definition f_lower_unitrP_subproof{G : lowerToField} : forall (x y : T(s := G)),
    setoid_lower2 sf_mul y x = setoid_lower0 sf_one /\ setoid_lower2 sf_mul x y = setoid_lower0 sf_one ->
    classical_sets.in_set (λ x0 : _, x0 != setoid_lower0 sf_zero) x.
Proof.
  intros ? ? [].
  unfold classical_sets.in_set.
  unfold boolp.asbool.
  destruct boolp.pselect.
  - reflexivity.
  - exfalso.

    apply n.
    apply /eqP.
    red ; intros.
    subst x.
    rewrite (setoid_lower_right_zero _ _ sf_mul0r) in H.
    unfold setoid_lower0, setoid_lower2 in *.
    apply (sf_one_not_zero (s := G)).

    eapply eqR_trans ; [ apply eqR_sym ; apply (U_F_cancel (s := G)) | ].
    eapply eqR_trans ; [ | apply (U_F_cancel (s := G)) ].
    rewrite H.
    apply eqR_refl.
Qed.

Definition f_lower_invr_out{G : lowerToField} : {in [predC classical_sets.in_set (λ x0 : (T (s := G)), x0 != setoid_lower0 sf_zero)],
      setoid_lower1 sf_inv =1 id}.
Proof.
  intros ? ?.
  rewrite inE in H.
  rewrite classical_sets.notin_set in H.
  destruct (x == setoid_lower0 sf_zero) eqn:H0 ; [ clear H | now exfalso ].
  apply (ssrbool.elimT eqP) in H0.
  rewrite H0.

  unfold setoid_lower1, setoid_lower0.
  apply lower_to_eq.
  eapply eqR_trans ; [ eapply (lower_ext _ _ _) ; apply (U_F_cancel (s := G)) | ].
  apply (sf_inv0 (s := G)).
Qed.
(* end details : we lower mul inverse *)

(* We now get field, since we have a ring with multiplicative inverse *)
HB.instance Definition _ (SG : lowerToField) :=
  GRing.Ring_hasMulInverse.Build (T (s := SG)) (f_lower_mulVr_subproof) (f_lower_mulrV_subproof) (f_lower_unitrP_subproof) (f_lower_invr_out).

(* unit elements are not zero, thus a unit ring and a field *)
Lemma v_Z_fieldP {SG : lowerToField} : GRing.MathCompCompatField.Field.axiom (T (s := SG)).
Proof.
  intros x H.
  rewrite unitrE.
  unfold "/".
  simpl.
  unfold "^-1"%R.
  simpl.
  rewrite (setoid_lowerC sf_mulC).
  now rewrite (setoid_lower_mulVr sf_mulV) ; [ apply eqxx | ].
Qed.

HB.instance Definition _ (SG : lowerToField) :=
  GRing.ComUnitRing_isIntegral.Build (T (s := SG)) (GRing.IdomainMixin v_Z_fieldP).
HB.instance Definition _ (SG : lowerToField) :=
  GRing.UnitRing_isField.Build (T (s := SG)) v_Z_fieldP.

(* Finally we get a field type, given a setoid with field-like structure *)
Notation v_Z_is_field := Hacspec_ovn_group_and_field_T__canonical__FinRing_Field.
