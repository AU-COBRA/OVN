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

(******************************************************************************)
(*                   OVN instances for Sigma protocols                        *)
(*                                                                            *)
(* Module GroupOperationProperties  has all properties of group operations for*)
(* - has all properties of group operations for v_G, and field operations for f_Z *)
(* - Module HacspecGroup ovn implementation with proofs of group operation, to  *)
(*   instantiate HB instances for group and field using hacspec OVN impl      *)
(* - Module SecureGroup properties for security of group, e.g. prime fields     *)
(* - Module FieldEquality equality between group field Z/#[g]Z and OVN field and*)
(*   some properties about the equality                                       *)
(* - Module OVN_schnorr_proof instantiation of Schnorr proof                    *)
(* - Module OVN_or_proof_preconditions            *)
(*   some properties about the equality                                       *)
(******************************************************************************)

(** * GroupOperationProperties. *)
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

HB.mixin Record is_eq_rel (V : Type) := {
    eq_relation : V -> V -> Prop ;

    eqR_refl : RelationClasses.Reflexive eq_relation ;
    eqR_sym : RelationClasses.Symmetric eq_relation ;
    eqR_trans : RelationClasses.Transitive eq_relation ;
  }.

(** * Setoid lowering *)

HB.structure Definition eqR := { V of is_eq_rel V }.

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

#[short(type="lowerToGroup")]
  HB.structure Definition setoid_lower_to_group := { V of setoid_lower V & setoid_group V }.

Definition mul_base_group (SG : lowerToGroup) :=
  isMulBaseGroup.Build (T (s := SG))
    (setoid_lowerA sg_prodA)
    (setoid_lower_left_id sg_prod1)
    (setoid_lower_involutive sg_invK)
    (setoid_lower_prod_morph sg_invM).

HB.instance Definition _ (SG : lowerToGroup) : isMulBaseGroup T := mul_base_group SG.

HB.instance Definition _ (SG : lowerToGroup) :=
  BaseFinGroup_isGroup.Build (T (s := SG)) (setoid_lower_left_inverse sg_prodV).

(** * Field instation *)

HB.mixin Record is_setoid_field_op (V : Type) :=
  {
    sf_mul : V -> V -> V ;
    sf_inv : V -> V ;
    sf_one : V ;

    sf_add : V -> V -> V ;
    sf_opp : V -> V ;
    sf_zero : V ;
  }.

HB.structure Definition setoid_field_op := { V of is_setoid_field_op V }.

HB.mixin Record is_setoid_field_properties (V : Type) of setoid_field_op V & eqR V :=
  {
    (** Guarantees about the field operations *)
    (* Addition is assoc, commutative and cancel with zero and opp *)
    sf_addA : setoid_associative (eq_relation := @eq_relation V) (sf_add) ;
    sf_addC: setoid_commutative (eq_relation := @eq_relation V) (sf_add) ;
    sf_add0: setoid_left_id (eq_relation := @eq_relation V) sf_zero sf_add ;
    sf_addN: setoid_left_inverse (eq_relation := @eq_relation V) (sf_zero) sf_opp sf_add ;

    (* Multiplication is commutative *)
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

HB.structure Definition setoid_field := { V of is_setoid_field_op V & eqR V & is_setoid_field_properties V }.

#[short(type="lowerToField")]
  HB.structure Definition setoid_lower_to_field := { V of setoid_lower V & setoid_field V }.

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

Corollary mulr0_from_mul0_mulC :
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
  (mulr0_from_mul0_mulC eqR_trans (sf_mul0 (s := SG)) (sf_mulC)).

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

(* Nmodule is Zmodule *)
HB.instance Definition _  (SG : lowerToField) :=
  GRing.Nmodule_isZmodule.Build  (T (s := SG)) (setoid_lower_left_inverse sf_addN).

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

(* Use simpler notation for field *)
Notation v_Z_is_field := Hacspec_ovn_to_sigma_T__canonical__FinRing_Field.

(** * OVN instantiation *)

(** * OVN Group and Field *)
Section OVN_instantiation.
  Context { C : choice_type }.
  Definition both_C : Type := both C.
  Definition C_type : Type := C.

  (* TODO: Cannot find instance in hacspec lib? *)
  Instance copy : t_Copy C := _.
  Instance partial_eq : t_PartialEq C C := _.
  Instance eq : t_Eq C := _.
  Instance clone : t_Clone C := _.
  Instance serialize : t_Serialize C := _.

  Variable (group : @t_Group C copy partial_eq is_eq clone serialize).

  HB.instance Definition _ :=
    is_eq_rel.Build (both_C) both_equivalence _ _ _.

  HB.instance Definition _ :=
    is_group_op.Build (both_C)
      (group.(f_prod))
      (group.(f_group_inv))
      (group.(f_group_one))
      (group.(f_g)).

  Variable both_group_properties : is_setoid_group_properties.axioms_ (both_C) (group_op.class Hacspec_ovn_to_sigma_both_C__canonical__Hacspec_ovn_to_sigma_group_op) (eqR.class Hacspec_ovn_to_sigma_both_C__canonical__Hacspec_ovn_to_sigma_eqR).

  HB.instance Definition _ := both_group_properties.

  Definition both_setoid_group := Hacspec_ovn_to_sigma_both_C__canonical__Hacspec_ovn_to_sigma_group_op.

  HB.instance Definition _ : is_setoid_lower both_C :=
    is_setoid_lower.Build both_C C_type (fun x => is_pure x) ret_both ret_both_is_pure_cancel (fun x => erefl)  (fun x y H => proj1 both_equivalence_is_pure_eq H)  (fun x y H => both_eq_fun_ext _ _ _).

  HB.instance Definition _ : fingroup.FinGroup C_type := fingroup.FinGroup.class (Hacspec_ovn_to_sigma_T__canonical__fingroup_FinGroup Hacspec_ovn_to_sigma_both_C__canonical__Hacspec_ovn_to_sigma_setoid_lower_to_group).

  Notation v_G_is_group := Hacspec_ovn_to_sigma_C_type__canonical__fingroup_FinGroup.

  Definition both_Z : Type := both f_Z.
  Definition Z_type : Type := f_Z.

  HB.instance Definition _ :=
    is_eq_rel.Build (both_Z) both_equivalence _ _ _.

  HB.instance Definition _ : is_setoid_field_op both_Z :=
    is_setoid_field_op.Build
      both_Z
      (group.(f_Z_t_Field).(f_mul))
      (group.(f_Z_t_Field).(f_inv))
      (group.(f_Z_t_Field).(f_field_one))
      (group.(f_Z_t_Field).(f_add))
      (group.(f_Z_t_Field).(f_opp))
      (group.(f_Z_t_Field).(f_field_zero)).

  Variable both_field_properties : is_setoid_field_properties.axioms_ (both_Z) (setoid_field_op.class Hacspec_ovn_to_sigma_both_Z__canonical__Hacspec_ovn_to_sigma_setoid_field_op) (eqR.class Hacspec_ovn_to_sigma_both_Z__canonical__Hacspec_ovn_to_sigma_eqR).

  HB.instance Definition _ := both_field_properties.

  Definition both_setoid_field := Hacspec_ovn_to_sigma_both_Z__canonical__Hacspec_ovn_to_sigma_setoid_field.

  HB.instance Definition _ : is_setoid_lower both_Z :=
    is_setoid_lower.Build both_Z Z_type (fun x => is_pure x) ret_both ret_both_is_pure_cancel (fun x => erefl)  (fun x y H => proj1 both_equivalence_is_pure_eq H)  (fun x y H => both_eq_fun_ext _ _ _).

  HB.instance Definition _ : GRing.Field Z_type := GRing.Field.class (Hacspec_ovn_to_sigma_T__canonical__FinRing_Field Hacspec_ovn_to_sigma_both_Z__canonical__Hacspec_ovn_to_sigma_setoid_lower_to_field).

  Notation v_Z_is_field := Hacspec_ovn_to_sigma_Z_type__canonical__GRing_Field.
End OVN_instantiation.

(** * Hacspec Group *)
Module HacspecGroup.
  Context {v_G : choice_type}.

  (* TODO: Cannot find instance in hacspec lib? *)
  Instance v_G_t_copy : t_Copy v_G := _.
  Instance v_G_t_partial_eq : t_PartialEq v_G v_G := _.
  Instance v_G_t_eq : t_Eq v_G := _.
  Instance v_G_t_clone : t_Clone v_G := _.
  Instance v_G_t_serialize : t_Serialize v_G := _.

  Context {v_G_t_Group : t_Group v_G}.
  Instance v_G_t_Group_temp : t_Group v_G := v_G_t_Group.

  Instance f_Z_t_copy : t_Copy f_Z := f_Z_t_Copy.
  Instance f_Z_t_partial_eq : t_PartialEq f_Z f_Z := f_Z_t_PartialEq.
  Instance f_Z_t_eq : t_Eq f_Z := f_Z_t_Eq.
  Instance f_Z_t_clone : t_Clone f_Z := f_Z_t_Clone.
  Instance f_Z_t_serialize : t_Serialize f_Z := f_Z_t_Serialize.

  Instance f_Z_t_Field' : t_Field f_Z := _.

  Context {v_A : choice_type}.
  Context {v_A_t_Sized : t_Sized v_A}.
  Instance v_A_t_Sized_temp : t_Sized v_A := v_A_t_Sized.

  Context {v_A_t_HasActions : t_HasActions v_A}.
  Instance v_A_t_HasActions_temp : t_HasActions v_A := v_A_t_HasActions.

  Context {n : both uint_size}.

  Context {v_G_t_Sized : t_Sized v_G}.
  Instance v_G_t_Sized_temp : t_Sized v_G := v_G_t_Sized.

  #[local] Open Scope hacspec_scope.

  Parameter t : is_setoid_group_properties.axioms_ both_C
                              (group_op.class
                                 (Hacspec_ovn_to_sigma_both_C__canonical__Hacspec_ovn_to_sigma_group_op
                                    v_G_t_Group))
                              (eqR.class
                                 Hacspec_ovn_to_sigma_both_C__canonical__Hacspec_ovn_to_sigma_eqR).

  Definition v_G_is_group : finGroupType :=
    (Hacspec_ovn_to_sigma_C_type__canonical__fingroup_FinGroup (C := v_G) v_G_t_Group t).


  Parameter t2 : is_setoid_field_properties.axioms_ (both_Z v_G_t_Group) (setoid_field_op.class (Hacspec_ovn_to_sigma_both_Z__canonical__Hacspec_ovn_to_sigma_setoid_field_op v_G_t_Group)) (eqR.class (Hacspec_ovn_to_sigma_both_Z__canonical__Hacspec_ovn_to_sigma_eqR v_G_t_Group)).

  Definition v_Z_is_field : fieldType :=
    Hacspec_ovn_to_sigma_Z_type__canonical__GRing_Field (C := v_G) v_G_t_Group t2.

  Parameter pow_base : forall x, f_g_pow x ≈both f_pow f_g x. (* TODO: just have this as a definition *)
  Parameter generator_is_not_one : f_group_one ≈both f_g -> False.
End HacspecGroup.

(** * Secure Group *)
Module Type SecureGroup.
  Module Group := HacspecGroup.
  Export Group.
  Include Group.

  (* A secure group is of prime order and has a generator *)
  Parameter v_G_prime_order : prime #[ is_pure f_g : v_G_is_group].
  Parameter v_G_g_gen : [set : v_G_is_group] = <[ is_pure f_g : v_G_is_group]>.

End SecureGroup.

(** * Hacspec Group Param *)
Module HacspecGroupParam (SG : SecureGroup) <: GroupParam.
  Include SG.
  Export SG.

  (* The finite group type is the ovn group *)
  Definition gT : finGroupType := v_G_is_group.
  Definition ζ : {set gT} := [set : gT].
  Definition g :  gT := is_pure f_g.

  Definition g_gen : ζ = <[g]> := v_G_g_gen.
  Definition prime_order : prime #[g] := v_G_prime_order.

  (* order of g *)
  Definition q : nat := #[g].

End HacspecGroupParam.

(** * Field equality *)
Module Type FieldEquality (SG : SecureGroup).

  Module HacspecGroup := HacspecGroupParam SG.
  Include HacspecGroup.
  Export HacspecGroup.

  (** Field equality *)
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
    destruct (Logic.eq_sym (pdiv_id (p:=q) prime_order)).
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
    destruct (Logic.eq_sym (pdiv_id (p:=q) prime_order)).
    reflexivity.
  Qed.

  Parameter WitnessToField : {rmorphism 'Z_ HacspecGroup.q -> v_Z_is_field}.
  Parameter FieldToWitness : {rmorphism v_Z_is_field -> 'Z_ HacspecGroup.q}.
  Parameter WitnessToFieldCancel :
    cancel FieldToWitness WitnessToField.
  Parameter FieldToWitnessCancel :
    cancel WitnessToField FieldToWitness.

  (* Properties of the field isomorphism *)
  Definition WitnessToFieldAdd : forall x y, WitnessToField (x + y) = is_pure (f_add (ret_both (WitnessToField x)) (ret_both (WitnessToField y))).
  Proof.
    intros. now rewrite rmorphD.
  Qed.

  Definition WitnessToFieldMul : forall x y,
      WitnessToField (Zp_mul x y) = is_pure (f_mul (ret_both (WitnessToField x)) (ret_both (WitnessToField y))).
  Proof.
    intros. now rewrite rmorphM.
  Qed.

  Parameter conversion_is_true :
    forall (b : both (v_G_t_Group.(f_Z))),
    (HacspecGroup.g ^+ FieldToWitness (is_pure b)) = is_pure (f_g_pow b).

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

  (** Field equality *)
  (* the field is given by the Z/#[g]Z, so the OVN field should be equal to this, same as for Schnorr *)

  (* pow spec, could be omitted by using iterated mul in hax code instead *)
  Parameter pow_witness_to_field :
    forall (h : gT) (b : 'Z_q),
      (h ^+ b = is_pure (f_pow (ret_both h) (ret_both (WitnessToField b)))).

  Definition FieldToWitnessOpp : (forall (b : both _), Zp_opp (FieldToWitness (is_pure b)) = FieldToWitness (is_pure (f_opp b))).
    intros.
    setoid_rewrite <- (rmorphN FieldToWitness).
    unfold "- _"%R ; simpl.
    unfold setoid_lower1, U, F, sf_opp ; simpl.
    f_equal.
    now Misc.push_down_sides.
  Defined.

  Definition WitnessToField_f_inv : forall s, (is_pure (f_inv (ret_both (WitnessToField s))) = (WitnessToField (Zp_inv s))).
  Proof.
    intros.
    rewrite <- (F_to_Z_cancel s) at 1.

    setoid_rewrite <- (fmorphV (WitnessToField \o F_to_Z)).
    simpl.
    setoid_rewrite (fmorphV (F_to_Z)).
    now rewrite F_to_Z_cancel.
  Defined.

  Definition FieldToWitnessOne : FieldToWitness (is_pure f_field_one) = 1%R.
  Proof.
    rewrite rmorph1.
    reflexivity.
  Defined.

End FieldEquality.

Module OVN_schnorr_proof (SG : SecureGroup) (field_equality : FieldEquality SG).
  Module Schnorr := Schnorr field_equality.HacspecGroup.

  Import Schnorr.MyParam.
  Import Schnorr.MyAlg.

  Import Schnorr.Sigma.Oracle.
  Import Schnorr.Sigma.

  Include field_equality.
  Export field_equality.

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
      rewrite WitnessToFieldAdd.
      rewrite WitnessToFieldCancel.
      rewrite WitnessToFieldMul.

      (* Equality up to `ret_both (is_pure _)` *)
      now Misc.push_down_sides.
  Qed.
End OVN_schnorr_proof.

Module Type OVN_or_proof_preconditions (SG : SecureGroup) (field_equality : FieldEquality SG).

  Include field_equality.
  Export field_equality.
  (** * Helper properties *)

  Lemma order_ge1 : succn (succn (Zp_trunc q)) = q.
  Proof.
    rewrite <- (@pdiv_id q HacspecGroup.prime_order) at 1.
    apply Fp_cast, prime_order.
  Qed.

  Lemma trunc_pow : forall (h : gT) x, h ^+ (x %% (Zp_trunc q).+2) = h ^+ x.
    intros.
    destruct (ssrbool.elimT (cycleP g h)) ; [ | subst ].
    - unfold g.
      setoid_rewrite <- v_G_g_gen.
      simpl.
      apply in_setT.
    - rewrite expgAC.
      rewrite (expgAC _ x0).
      f_equal.
      epose (@expg_mod_order gT g x).
      fold q in e.
      rewrite <- order_ge1 in e.
      intros.
      apply e ; clear e.
  Qed.

  Lemma invg_id : (forall (x : gT), x ^-1 = x ^- 1%R).
  Proof. reflexivity. Qed.

  Lemma trunc_extra : forall (h : gT), h ^+ (Zp_trunc q).+2 = 1.
    intros.
    rewrite <- trunc_pow.
    now rewrite modnn.
  Qed.

  Lemma reverse_opp : (forall (x : gT) (n : 'Z_q), x ^+ ((Zp_trunc (pdiv q)).+2 - n) = x ^+ GRing.opp n).
  Proof.
    intros.
    rewrite (@pdiv_id q HacspecGroup.prime_order).
    now rewrite trunc_pow.
  Qed.

  Lemma neg_is_opp : (forall (x : gT) (n : 'Z_q), x ^- n = x ^+ GRing.opp n).
  Proof.
    intros x n.
    rewrite trunc_pow.
    destruct n as [n ?] ; simpl.
    induction n.
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
      set (subn _ _).
      now rewrite (Nat.lt_succ_pred 0 n1).
  Qed.

  Lemma mulg_cancel : forall (x : gT) (y : 'Z_q),
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

  Lemma prod_swap_iff : (forall a b (x : gT) (y : 'Z_q), (a * x ^- y = b <-> a = b * x ^+ y) /\ (x ^- y * a = b <-> a = x ^+ y * b)).
  Proof.
    repeat split ;
      [ eapply (canRL (f := mulg^~ _) (g := mulg^~ _))
      | eapply (canLR (f := mulg^~ _) (g := mulg^~ _))
      | eapply (canRL)
      | eapply (canLR) ] ; apply (mulg_cancel x y).
  Qed.

  Lemma mulg_invg_sub : (forall (x : gT) (y z : 'Z_q), x ^+ y * x ^- z = x ^+ nat_of_ord (y - z)).
  Proof.
    intros.
    rewrite neg_is_opp.
    rewrite <- expgD.
    now rewrite trunc_pow.
  Qed.

  Lemma mulg_invg_left_sub : (forall (x : gT) (y z : 'Z_q), x ^- y * x ^+ z = x ^+ nat_of_ord (z - y)).
  Proof.
    intros.
    rewrite neg_is_opp.
    rewrite <- expgD.
    now rewrite trunc_pow.
  Qed.

  Lemma cyclic_always_commute : forall (x y : gT), commute x y.
  Proof.
    intros.
    destruct (ssrbool.elimT (cycleP g x)) ; [ | subst ].
    {
      unfold gT in x.
      unfold g.
      setoid_rewrite <- v_G_g_gen.
      simpl.
      apply in_setT.
    }

    destruct (ssrbool.elimT (cycleP g y)) ; [ | subst ].
    {
      unfold g.
      setoid_rewrite <- v_G_g_gen.
      simpl.
      apply in_setT.
    }

    apply commuteX2.
    apply commute_refl.
  Qed.

  Lemma div_cancel_Fq : forall (x : gT) (s : 'F_q), s <> 0 -> x ^+ nat_of_ord (s / s)%R = x.
  Proof.
    intros.
    rewrite mulrV.
    2: now rewrite (unitfE) ; apply /eqP.
    now rewrite expg1.
  Qed.

  Lemma div_cancel : forall (x : gT) (s : 'Z_q), s <> 0 -> x ^+ nat_of_ord (s / s)%R = x.
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

  (** * OR protocol *)
  Module MyParam <: SigmaProtocolParams.

    Definition Witness : finType := prod (prod (Finite.clone _ 'Z_q) (Finite.clone _ 'bool)) gT.
    Definition Statement : finType := prod (prod gT gT) gT.
    Definition Message : finType :=  prod (prod (prod gT gT) gT) gT.
    Definition Challenge : finType := Finite.clone _ 'Z_q.
    Definition Response : finType :=  (prod (prod (prod (Finite.clone _ 'Z_q) (Finite.clone _ 'Z_q)) (Finite.clone _ 'Z_q)) (Finite.clone _ 'Z_q)).

    Definition w0 : Witness := (0, false, 1).
    Definition e0 : Challenge := 0.
    Definition z0 : Response := 0.

    (* OR relation *)
    Definition R : Statement -> Witness -> bool :=
      (λ (xhy : Statement) (mv : Witness),
        let '(x,h,y) := xhy in
        let '(m,v,h2) := mv in
        (x == g ^+ m)
        && (h == h2)
        && ((y == h^+m * g ^+ v))
      ).

    (* Sanity check *)
    Lemma relation_valid_left:
      ∀ (x : 'Z_q) (h : gT),
        R (g^+x, h, h^+x * g) (x, 1%R, h).
    Proof.
      intros x yi.
      unfold R.
      now rewrite !eqxx.
    Qed.

    (* Sanity check *)
    Lemma relation_valid_right:
      ∀ (x : 'Z_q) (h : gT),
        R (g ^+ x, h, h ^+x) (x, 0%R, h).
    Proof.
      intros x yi.
      unfold R.
      rewrite expg0.
      rewrite mulg1.
      now rewrite !eqxx.
    Qed.

    (* Positivity checks *)
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
      apply /card_gt0P. exists 0. auto.
    Defined.

    #[export] Instance prod_pos : forall {A B : finType}, Positive #|A| -> Positive #|B| -> Positive #|(prod A B : finType)|.
    Proof.
      intros.
      rewrite card_prod.
      now apply Positive_prod.
    Defined.

    Instance Witness_pos : Positive #|Witness| := _.
    Definition Statement_pos : Positive #|Statement| := _.
    Definition Message_pos : Positive #|Message| := _.
    Definition Challenge_pos : Positive #|Challenge| := _.
    Definition Response_pos : Positive #|Response| := _.

  End MyParam.

  Module MyAlg <: SigmaProtocolAlgorithms MyParam.

    Import MyParam.

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
         let '(m, v, _) := (otf xv) in
         if v
         then
           (
             let r1 := r in
             let d1 := d in

             let a1 := (g ^+ (otf r1 : 'Z_q) * x ^+ (otf d1 : 'Z_q)) in
             let b1 := (h ^+ (otf r1 : 'Z_q) * y ^+ (otf d1 : 'Z_q)) in

             let a2 := (g ^+ (otf w : 'Z_q)) in
             let b2 := (h ^+ (otf w : 'Z_q)) in
             ret (fto (a1, b1, a2, b2)))
         else
           (let r2 := r in
            let d2 := d in

            let a1 := (g ^+ (otf w : 'Z_q)) in
            let b1 := (h ^+ (otf w : 'Z_q)) in

            let a2 := (g ^+ (otf r2 : 'Z_q) * x ^+ (otf d2 : 'Z_q)) in
            let b2 := (h ^+ (otf r2 : 'Z_q) * (y * g^-1) ^+ (otf d2 : 'Z_q)) in
            ret (fto (a1, b1, a2, b2)))
      }.

    Definition Verify (xhy : choiceStatement) (a : choiceMessage)
      (c : choiceChallenge) (z : choiceResponse) : choiceBool :=
      let '(x, h, y) := otf xhy in
      let '(a1, b1, a2, b2) := (otf a) in
      let '(r1, d1, r2, d2) := (otf z) in
      fto ((otf c == d1 + d2) &&
             (a1 == (g ^+ r1) * (x ^+ d1)) &&
             (b1 == (h ^+ r1) * (y ^+ d1)) &&
             (a2 == (g ^+ r2) * (x ^+ d2)) &&
             (b2 == (h ^+ r2) * ((y * (g ^-1)) ^+ d2))).


    Definition Response (xhy : choiceStatement) (xv : choiceWitness) (_ : choiceMessage) (c : choiceChallenge) :
      code Sigma_locs [interface] choiceResponse :=
      {code
         '(w, r, d) ← get commit_loc ;;
         let '(x, h, y) := (otf xhy) in
         let '(m, v, _) := (otf xv) in
         if v (* y == h ^+ m * g *)
         then
           (let d2 := (otf c - otf d) in
            let r2 := (otf w - (m * d2)) in
            ret (fto (otf r, otf d, r2, d2)))
         else
           (let d1 := (otf c - otf d) in
            let r1 := (otf w - (m * d1)) in
            ret (fto (r1, d1, otf r, otf d)))
      }.

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
         let d1 := otf c - d2 in
         let a1 := g ^+ r1 * x ^+ d1 in
         let b1 := h ^+ r1 * y ^+ d1 in
         let a2 := g ^+ r2 * x ^+ d2 in
         let b2 := h ^+ r2 * (y * invg g) ^+ d2 in
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

      let m := if d1 - d1' != 0
               then ((r1' - r1) / (d1 - d1'))
               else ((r2' - r2) / ((d2 - d2'))) in
      let v := ~~ (d1 - d1' != 0) (* y == h ^+ m * g *) in
      Some (fto (m, v, h)).
    Fail Next Obligation.

    Definition KeyGen (xv : choiceWitness) :=
      let '(m, v, h) := otf xv in
      fto (g ^+ m, h ^+ m, h ^+ m * g ^+ v).

  End MyAlg.

  Module Sigma := SigmaProtocol MyParam MyAlg.

End OVN_or_proof_preconditions.

Module OVN_or_proof (SG : SecureGroup) (field_equality : FieldEquality SG) (proof_args : OVN_or_proof_preconditions SG field_equality).
  Import field_equality.
  Import proof_args.

  Import MyParam.
  Import MyAlg.

  Import Sigma.Oracle.
  Import Sigma.

  Include proof_args.
  Export proof_args.

  Transparent zkp_one_out_of_two.

  (* Mapping between d2, r2 and w, d for sampled randomness *)
  Definition f_d2r2_to_wd : 'Z_q -> 'I_MyAlg.i_witness -> Arit (uniform (MyAlg.i_witness * MyAlg.i_witness)) → Arit (uniform (MyAlg.i_witness * MyAlg.i_witness)) :=
    fun m c dr =>
      let '(d2, r2) := (ch2prod dr) in
      prod2ch (fto ((otf r2) + (m * (otf d2))), fto (otf c - otf d2)).

  Lemma f_d2r2_to_wd_bij : forall m c, bijective (f_d2r2_to_wd m c).
  Proof.
    intros.
    eapply (Bijective (g := fun dr =>
      let '(d2, r2) := (ch2prod dr) in
      prod2ch (fto (otf c - otf r2), fto (otf d2 - (otf c - otf r2) * m)))).
    - intros z.
      unfold f_d2r2_to_wd.
      rewrite <- prod2ch_ch2prod.
      set (ch2prod _) at 2 3.
      destruct s eqn:ch2z.
      rewrite ch2prod_prod2ch.
      rewrite !otf_fto.
      f_equal.
      rewrite subKr.
      rewrite !fto_otf.
      f_equal.
      rewrite mulrC.
      rewrite addrK.
      rewrite !fto_otf.
      reflexivity.
    - intros z.
      unfold f_d2r2_to_wd.
      rewrite <- prod2ch_ch2prod.
      set (ch2prod _) at 2 3.
      destruct s eqn:ch2z.
      rewrite ch2prod_prod2ch.
      rewrite !otf_fto.
      f_equal.
      rewrite subKr.
      rewrite !fto_otf.
      f_equal.
      rewrite mulrC.
      rewrite subrK.
      rewrite !fto_otf.
      reflexivity.
  Qed.

  (* Mapping between d1, r1 and w, d for sampled randomness *)
  Definition f_d1r1_to_wd : 'Z_q -> 'I_MyAlg.i_witness -> Arit (uniform (MyAlg.i_witness * MyAlg.i_witness)) → Arit (uniform (MyAlg.i_witness * MyAlg.i_witness)) :=
    fun m c dr =>
      let '(d2, r1) := ch2prod dr in
      prod2ch (fto ((otf r1) + (m * (otf c - otf d2))), fto (otf d2)).

  Lemma f_d1r1_to_wd_bij : forall m c, bijective (f_d1r1_to_wd m c).
  Proof.
    intros.
    eapply (Bijective (g := fun dr =>
                              let '(d2, r2) := (ch2prod dr) in
                              prod2ch (r2, fto (otf d2 - m * (otf c - otf r2))))).
    - intros z.
      unfold f_d1r1_to_wd.
      rewrite <- prod2ch_ch2prod.
      set (ch2prod _) at -1.
      destruct s eqn:ch2z.
      rewrite ch2prod_prod2ch.
      rewrite !fto_otf.
      rewrite !otf_fto.
      f_equal.
      f_equal.
      rewrite addrK.
      rewrite !fto_otf.
      reflexivity.
    - intros z.
      unfold f_d1r1_to_wd.
      rewrite <- prod2ch_ch2prod.
      set (ch2prod _) at -1.
      destruct s eqn:ch2z.
      rewrite ch2prod_prod2ch.
      rewrite !fto_otf.
      rewrite !otf_fto.
      f_equal.
      f_equal.
      rewrite subrK.
      rewrite !fto_otf.
      reflexivity.
  Qed.

  (* Mapping between return values for the two OR protocols *)
  Transparent run.
  Definition hacspec_ret_to_or_sigma_ret : Statement -> t_OrZKPCommit -> choiceTranscript.
  Proof.
    intros hy [[[[[[[[[[r1x r2y] r3a1] r4b1] r5a2] r6b2] r7c] r8d1] r9d2] r10r1] r11r2].
    refine (fto _, fto _, fto _, fto _).
    (* choiceStatement *)
    - refine hy.

    (* choiceMessage *)
    - refine (r3a1, r4b1, r5a2, r6b2).

    (* choiceChallenge = hash *)
    - refine (FieldToWitness r7c).

    (* choiceResponse *)
    - refine (FieldToWitness r10r1, FieldToWitness r8d1, FieldToWitness r11r2, FieldToWitness r9d2).
  Defined.

  Definition or_run_post_cond :
    choiceStatement ->
    tgt (RUN, (choiceStatement × choiceWitness, choiceTranscript))
    → t_OrZKPCommit → Prop.
  Proof.
    intros stmt a b.
    refine (a = hacspec_ret_to_or_sigma_ret (otf stmt) b).
  Defined.

  (* Equivalence between the two OR protocols *)
 Lemma or_run_eq  (pre : precond) :
    forall (b : Statement * Witness) c,
      Some c = lookup_op RUN_interactive (RUN, ((chProd choiceStatement choiceWitness), choiceTranscript)) ->
      ⊢ ⦃ fun '(h₁, h₀) => heap_ignore Sigma_locs (h₀, h₁) ⦄
        c (fto (fst b), fto (snd b))
        ≈
        #assert R (b.1) (b.2) ;;
        wr ← sample uniform (2^32) ;;
        dr ← sample uniform (2^32) ;;
        rr ← sample uniform (2^32) ;;
        is_state (zkp_one_out_of_two
                    (ret_both (Hacspec_Lib_Pre.repr _ (Z.of_nat (nat_of_ord wr))))
                    (ret_both (Hacspec_Lib_Pre.repr _ (Z.of_nat (nat_of_ord rr))))
                    (ret_both (Hacspec_Lib_Pre.repr _ (Z.of_nat (nat_of_ord dr))))
                    (ret_both (snd (fst (fst b))))
                    (ret_both (WitnessToField (fst (fst (snd b)))))
                    (ret_both ((snd (fst b) == (snd (fst (fst b)) ^+  (fst (fst (snd b))) * g)) : 'bool)))
          ⦃ fun '(x,h0) '(y,h1) => or_run_post_cond (fto (fst b)) x y ∧ heap_ignore Sigma_locs (h0, h1) ⦄.
  Proof.
    intros [[[x h] y] [[m v] n]] c H.

    (* Unfold lhs *)
    simpl fst ; simpl snd.

    simpl in H.
    destruct choice_type_eqP as [ e | ] ; [ | discriminate ].
    destruct choice_type_eqP as [ e1 | ] ; [ | discriminate ].
    rewrite cast_fun_K in H.
    clear e e1.
    inversion_clear H.

    (* Unfold rhs *)
    unfold zkp_one_out_of_two.

    rewrite !otf_fto; unfold R.
    apply r_assertD ; [ reflexivity | ].
    intros _ ?.
    simpl in e₁.
    repeat (apply andb_prop in e₁ ; destruct e₁ as [e₁ ?]).
    apply reflection_nonsense in e₁.
    subst.

    (* Align random sampling *)
    pose (bij_f := randomness_sample_is_bijective).
    set (f_rand := fun _ => _) in bij_f.

    eapply rsymmetry ; eapply r_uniform_bij with (f := fun x => _) ; [ apply bij_f | intros x0 ] ; apply rsymmetry ; apply better_r.
    eapply rsymmetry ; eapply r_uniform_bij with (f := fun x => _) ; [ apply bij_f | intros x1 ] ; apply rsymmetry ; apply better_r.
    eapply rsymmetry ; eapply r_uniform_bij with (f := fun x => _) ; [ apply bij_f | intros x2] ; apply rsymmetry ; apply better_r.

    (* Save value in memory *)
    apply better_r_put_lhs.

    (* Substitue random *)
    pose (f_rand_inner := fun (x : 'I_(2 ^ 32)) => (FieldToWitness
            (is_pure
               (f_random_field_elem (ret_both (Hacspec_Lib_Pre.repr _ (Z.of_nat (nat_of_ord x)))))))).
    progress repeat match goal with
    | [ |- context [ otf (f_rand ?x) ] ] =>
        replace (_ (f_rand x)) with (f_rand_inner x) by now rewrite otf_fto
      end.
    subst f_rand f_rand_inner.

    (* Case on vote *)
    destruct v.
    {
      (* Simlify to v = true case *)
      apply reflection_nonsense in H.
      subst.
      rewrite !eqxx.
      repeat unfold let_both at 1.
      simpl.
      Transparent Build_t_OrZKPCommit.
      unfold Build_t_OrZKPCommit; hnf.

      (* isolate f_hash *)
      eapply (Misc.r_transR_both (B := t_OrZKPCommit)) ; [ set (H_hash := f_hash _); Misc.pattern_lhs_both_pat H_hash ; now rewrite <- (bind_both_eta _ H_hash) |  hnf ; unfold bind_both at 1, bind_raw_both, both_prog at 1, is_state at 1; set (f_or := fun _ => is_state (bind_both _ _)) ].

      (* replace f_hash with random sampling *)
      eapply (hash_is_psudorandom _ _ (fun x => WitnessToField (otf x)) _ _ _ _ [:: _; _; _; _; _; _]).
      intros x3.

      (* get value from memory *)
      apply getr_set_lhs.
      (* get return value *)
      apply Misc.make_pure ; simpl.

      (* Compare result values *)
      apply r_ret.
      intros ? ? ?.

      unfold or_run_post_cond.
      unfold hacspec_ret_to_or_sigma_ret.

      rewrite FieldToWitnessCancel.
      rewrite !otf_fto.
      unfold lower2 ; simpl.

      set (f_random_field_elem _).
      set (f_random_field_elem _).
      set (f_random_field_elem _).

      split.
      - repeat (rewrite pair_equal_spec ; split).
        (* Statement *)
        {
          reflexivity.
        }
        (* Commit *)
        {
          apply f_equal.
          repeat rewrite pair_equal_spec ; repeat split.
          all: clear ; simpl; Misc.push_down_sides.
          all: repeat setoid_rewrite <- expgnE.

          (* TODO: some group tactic here ? *)
          - rewrite pow_witness_to_field; rewrite WitnessToFieldCancel.
            rewrite pow_witness_to_field; rewrite WitnessToFieldCancel.
            rewrite pow_witness_to_field.
            rewrite !(proj1 both_equivalence_is_pure_eq (pow_base _)).
            now Misc.push_down_sides.
          - rewrite pow_witness_to_field; rewrite WitnessToFieldCancel.
            rewrite !pow_witness_to_field; rewrite WitnessToFieldCancel.
            now Misc.push_down_sides.
          - rewrite pow_witness_to_field; rewrite WitnessToFieldCancel.
            rewrite !(proj1 both_equivalence_is_pure_eq (pow_base _)).
            now Misc.push_down_sides.
          - now rewrite pow_witness_to_field; rewrite WitnessToFieldCancel.
        }
        (* Challenges *)
        {
          now rewrite fto_otf.
        }
        (* Response *)
        {
          apply f_equal.
          repeat (rewrite pair_equal_spec ; split).
          all: clear ; simpl; Misc.push_down_sides.
          all: repeat setoid_rewrite <- expgnE.
          - reflexivity.
          - reflexivity.
          - fold (both_prog b1).
            (* assert (forall (x y : 'Z_q), (x - y)%R = (x + (GRing.opp y))%R) by reflexivity. *)
            (* rewrite H. *)
            (* rewrite !(proj1 both_equivalence_is_pure_eq (sf_sub_by_opp (s := both_setoid_field v_G_t_Group _) _ _)). *)

            Transparent Hacspec_ovn.sub.
            unfold Hacspec_ovn.sub.

            rewrite <- (FieldToWitnessCancel (GRing.opp (m * _))%R).
            setoid_rewrite <- (rmorphD FieldToWitness).
            simpl.
            rewrite hacspec_function_guarantees2.
            rewrite <- (WitnessToFieldCancel (is_pure b1)).
            setoid_rewrite <- (rmorphD WitnessToField).
            rewrite (WitnessToFieldAdd).

            setoid_rewrite (rmorphN WitnessToField).
            rewrite (rmorphM WitnessToField).
            setoid_rewrite (rmorphD WitnessToField).
            setoid_rewrite (rmorphN WitnessToField).

            rewrite !WitnessToFieldCancel.

            apply f_equal.
            now Misc.push_down_sides.
          - unfold Hacspec_ovn.sub.

            rewrite <- (FieldToWitnessCancel (otf _)%R).
            setoid_rewrite <- (rmorphN FieldToWitness).
            setoid_rewrite <- (rmorphD FieldToWitness).

            apply f_equal.
            now Misc.push_down_sides.
        }
      - clear -H.
        destruct H.
        destruct H.
        subst.
        unfold heap_ignore.
        intros.
        unfold heap_ignore in H.

        rewrite H ; [ | assumption ].
        unfold Sigma_locs in H0 ; rewrite <- fset1E in H0 ; rewrite in_fset1 in H0.
        now rewrite <- get_heap_set_heap.
    }
    {
      (* Simlify to v = false case *)
      apply reflection_nonsense in H(* , H0, H1 *).
      subst.
      set (_ == _).
      replace b with false.
      2:{
        symmetry.
        apply /eqP.
        intros ?.
        subst.

        apply generator_is_not_one.
        eapply both_equivalence_is_pure_eq.
        apply prod_swap_iff in H.
        rewrite expg0 in H.
        rewrite mulg1 in H.
        rewrite mulVg in H.

        fold g.
        rewrite <- H.
        reflexivity.
      }

      Opaque Build_t_OrZKPCommit.
      simpl.
      repeat unfold let_both at 1.
      simpl.
      Transparent Build_t_OrZKPCommit.
      unfold Build_t_OrZKPCommit; hnf.

      (* isolate f_hash *)
      eapply (Misc.r_transR_both (B := t_OrZKPCommit)) ; [ set (H_hash := f_hash _); Misc.pattern_lhs_both_pat H_hash ; now rewrite <- (bind_both_eta _ H_hash) |  hnf ; unfold bind_both at 1, bind_raw_both, both_prog at 1, is_state at 1; set (f_or := fun _ => is_state (bind_both _ _)) ].

      (* replace f_hash with random sampling *)
      eapply (hash_is_psudorandom _ _ (fun x => WitnessToField (otf x)) _ _ _ _ [:: _; _; _; _; _; _]).
      intros x3.

      (* get value from memory *)
      apply getr_set_lhs.
      (* get return value *)
      apply Misc.make_pure ; simpl.

      (* Compare result values *)
      apply r_ret.
      intros ? ? ?.

      unfold or_run_post_cond.
      rewrite !otf_fto.
      unfold lower2 ; simpl.

      set (f_random_field_elem _).
      set (f_random_field_elem _).
      set (f_random_field_elem _).

      split.
      - repeat (rewrite pair_equal_spec ; split).
        {
          reflexivity.
        }
        (* Commit *)
        {
          apply f_equal.
          repeat rewrite pair_equal_spec ; repeat split.
          all: clear ; simpl; Misc.push_down_sides.
          all: repeat setoid_rewrite <- expgnE.

          + rewrite pow_witness_to_field; rewrite WitnessToFieldCancel.
            rewrite !(proj1 both_equivalence_is_pure_eq (pow_base _)).
            now Misc.push_down_sides.
          + now rewrite pow_witness_to_field; rewrite WitnessToFieldCancel.
          + rewrite pow_witness_to_field; rewrite WitnessToFieldCancel.
            rewrite pow_witness_to_field; rewrite WitnessToFieldCancel.
            unfold g.
            rewrite !(proj1 both_equivalence_is_pure_eq (pow_base _)).
            rewrite pow_witness_to_field.
            now Misc.push_down_sides.
          + rewrite expg0.
            rewrite mulg1.
            rewrite pow_witness_to_field; rewrite WitnessToFieldCancel.
            rewrite pow_witness_to_field.
            Transparent Hacspec_ovn.div.
            unfold Hacspec_ovn.div.
            (* rewrite (proj1 both_equivalence_is_pure_eq (div_is_prod_inv _ _)). *)
            rewrite pow_witness_to_field.
            rewrite WitnessToFieldCancel.
            now Misc.push_down_sides.
        }
        (* Challenges *)
        {
          now rewrite FieldToWitnessCancel ; rewrite fto_otf.
        }
        (* Response *)
        {
          apply f_equal.
          repeat (rewrite pair_equal_spec ; split).
          all: clear ; simpl; Misc.push_down_sides.
          all: repeat setoid_rewrite <- expgnE.
          - fold (both_prog b0).
            rewrite <- (FieldToWitnessCancel (GRing.opp (m * _))%R).
            setoid_rewrite <- (rmorphD FieldToWitness).
            rewrite <- (WitnessToFieldCancel (is_pure b0)).
            setoid_rewrite <- (rmorphD WitnessToField).

            rewrite !FieldToWitnessCancel.
            rewrite <- (FieldToWitnessCancel (m * _)%R).

            setoid_rewrite <- (rmorphN FieldToWitness).
            setoid_rewrite <- (rmorphD FieldToWitness).

            setoid_rewrite (rmorphM WitnessToField).
            setoid_rewrite (rmorphD WitnessToField).
            setoid_rewrite (rmorphN WitnessToField).

            rewrite !WitnessToFieldCancel.
            apply f_equal.

            cbn.

            now repeat (Misc.push_down_sides ; apply f_equal).
          - (* rewrite !(proj1 both_equivalence_is_pure_eq (f_sub_by_opp _ _)). *)
            rewrite hacspec_function_guarantees2.
            rewrite rmorphD.
            rewrite <- FieldToWitnessOpp.
            simpl.
            now rewrite !FieldToWitnessCancel.
          - reflexivity.
          - reflexivity.
        }
      - clear -H.
        destruct H.
        destruct H.
        subst.
        unfold heap_ignore.
        intros.
        unfold heap_ignore in H.

        rewrite H ; [ | assumption ].
        unfold Sigma_locs in H0 ; rewrite <- fset1E in H0 ; rewrite in_fset1 in H0.
        now rewrite <- get_heap_set_heap.
    }
    (* Qed. *)
    Fail Timeout 5 Qed. Admitted. (* SLOW: 525.61 sec *)

  (* The packaged version for running the hacspec code *)
  Program Definition hacspec_or_run :
    package Sigma_locs
        [interface]
        [interface
          #val #[ RUN ] : chRelation → chTranscript
        ]
    :=
      [package
         #def #[ RUN ] (b : chRelation) : chTranscript
        {
          #assert R (otf b.1) (otf b.2) ;;
          wr ← sample uniform (2^32) ;;
          dr ← sample uniform (2^32) ;;
          rr ← sample uniform (2^32) ;;
          v ← is_state (zkp_one_out_of_two
                      (ret_both (Hacspec_Lib_Pre.repr _ (Z.of_nat (nat_of_ord wr))))
                      (ret_both (Hacspec_Lib_Pre.repr _ (Z.of_nat (nat_of_ord rr))))
                      (ret_both (Hacspec_Lib_Pre.repr _ (Z.of_nat (nat_of_ord dr))))
                      (ret_both (snd (fst (otf (fst b)))))
                      (ret_both (WitnessToField (fst (fst (otf (snd b))))))
                      (ret_both ((snd (otf (fst b)) == (snd (fst (otf (fst b))) ^+  (fst (fst (otf (snd b)))) * g)) : 'bool))) ;;
          ret (hacspec_ret_to_or_sigma_ret (otf b.1) v)
      }].
  (* begin hide *)
  Next Obligation.
    eapply (valid_package_cons _ _ _ _ _ _ [] []).
    - apply valid_empty_package.
    - intros.
      ssprove_valid.
      set (zkp_one_out_of_two _ _ _ _ _ _).
      apply valid_scheme.
      rewrite <- fset0E.
      apply (ChoiceEquality.is_valid_code (both_prog_valid b)).
    - try (rewrite <- fset0E ; setoid_rewrite @imfset0 ; rewrite in_fset0 ; reflexivity).
  Qed.
  Fail Next Obligation.
  (* end hide *)

  (* Adversary gets no advantage by running hacspec version *)
  Lemma hacspec_vs_RUN_interactive :
    ∀ LA A,
      ValidPackage LA [interface
                         #val #[ RUN ] : chRelation → chTranscript
        ] A_export A →
      fdisjoint LA Sigma_locs →
      AdvantageE hacspec_or_run RUN_interactive A = 0.
  Proof.
    (* Unfold statement *)
    intros LA A Va Hdisj.
    eapply eq_rel_perf_ind_ignore.
    6,7: apply Hdisj.
    5: apply Va.
    2:{
      unfold RUN_interactive.
      eapply valid_package_inject_export.
      2:{
        eapply (valid_package_cons).
        + eapply (valid_package_cons).
          * apply valid_empty_package.
          * intros.
            ssprove_valid ; apply prog_valid.
          * try (rewrite <- fset0E ; setoid_rewrite @imfset0 ; rewrite in_fset0 ; reflexivity).
        + intros.
          ssprove_valid ; apply prog_valid.
        + rewrite <- fset1E.
          rewrite imfset1.
          reflexivity.
      }
      - rewrite !fset_cons.
        apply fsubsetUr.
    }
    {
      apply hacspec_or_run.
    }
    {
      apply fsubsetUl.
    }
    unfold eq_up_to_inv.
    intros.
    unfold get_op_default.

    set (match _ with | Option_Some _ => _ | None => _ end) at 2.
    rewrite <- fset1E in H.
    apply (ssrbool.elimT (fset1P _ _)) in H.
    inversion H.
    Opaque zkp_one_out_of_two.
    simpl (lookup_op _ _).
    destruct choice_type_eqP ; [ | subst ; contradiction ].
    destruct choice_type_eqP ; [ | subst ; contradiction ].
    subst.
    rewrite cast_fun_K.
    apply rsymmetry.

    destruct x.

    set (pkg_core_definition.sampler _ _).
    eassert (r =
              (v ← (wr ← sample uniform (2 ^ 32) ;;
                    dr ← sample uniform (2 ^ 32) ;;
                    rr ← sample uniform (2 ^ 32) ;;
                    is_state
                      (zkp_one_out_of_two _
                         _
                         _
                         (ret_both ((snd (fst (otf (s, s0).1)))))
                         _
                         _)) ;;
               ret (hacspec_ret_to_or_sigma_ret (otf (s, s0).1) v))) by (now subst r ; simpl) ; rewrite H0 ; clear H0.
    clear.

    (* Proof equality *)
    eapply r_transR ; [ apply r_bind_assertD | hnf ].
    apply compute_in_post_cond_R.
    eapply rpost_weaken_rule.
    1:{
      eapply r_transL.
      2:{
        (* Apply proven equality *)
        eapply (or_run_eq (λ '(h₁, h₀), heap_ignore Sigma_locs (h₀, h₁)) (otf s, otf s0) y).
        subst y.
        simpl.
        destruct choice_type_eqP ; [ | subst ; contradiction ].
        destruct choice_type_eqP ; [ | subst ; contradiction ].
        subst.
        rewrite cast_fun_K.
        reflexivity.
      }
      {
        rewrite !fto_otf.
        apply rreflexivity_rule.
      }
    }
    {
      intros.
      destruct a₀.
      destruct a₁.
      destruct H.
      unfold or_run_post_cond in H.
      rewrite H.
      rewrite fto_otf.
      split ; [ reflexivity | ].
      unfold heap_ignore in H0.
      unfold heap_ignore.
      intros.
      specialize (H0 ℓ H1).
      easy.
    }
  Qed.

  (* Special honest verify zero knowledge *)
  (* Apply triangle inequality to get guarantees about hacspec *)
  Lemma run_interactive_or_shvzk :
    ∀ LA A,
      ValidPackage LA [interface
                         #val #[ RUN ] : chRelation → chTranscript
        ] A_export A →
      fdisjoint LA Sigma_locs →
      AdvantageE hacspec_or_run (SHVZK_real_aux ∘ SHVZK_real) A = 0.
  Proof.
    intros.
    apply (AdvantageE_le_0 _ _ _ ).
    eapply Order.le_trans ; [ eapply (Advantage_triangle _ _ RUN_interactive _) | ].
    rewrite (run_interactive_shvzk Simulator_locs (fun x => {code r ← sample uniform #|Challenge| ;; Simulate x r }) LA A H H0).
    rewrite GRing.addr0.
    now rewrite hacspec_vs_RUN_interactive.
  Qed.

  (* Extractor correctness *)
  Lemma shvzk_success:
    ∀ LA A,
      ValidPackage LA [interface
                         #val #[ TRANSCRIPT ] : chInput → chTranscript
        ] A_export A →
      fdisjoint LA Sigma_locs →
      ɛ_SHVZK A = 0.
  Proof.
    intros.
    unfold ɛ_SHVZK.
    unfold SHVZK_real.
    unfold SHVZK_ideal.
    apply: eq_rel_perf_ind.
    all: ssprove_valid.
    1:{ instantiate (1 := heap_ignore Sigma_locs).
        ssprove_invariant.
        apply fsubsetUl. }
    2: apply fdisjoints0.
    clear H0.
    1:{
      unfold eq_up_to_inv.
      intros.
      unfold get_op_default.

      rewrite <- fset1E in H0.
      apply (ssrbool.elimT (fset1P _ _)) in H0.
      inversion H0.

      subst.

      Opaque Simulate Commit Response.

      simpl (lookup_op _ _).


      destruct choice_type_eqP ; [ | subst ; contradiction ].
      destruct choice_type_eqP ; [ | subst ; contradiction ].
      subst.
      rewrite !cast_fun_K.

      clear e e1.

      destruct x as [[hy mv] c].
      ssprove_sync_eq. intros.

      Transparent Simulate.
      unfold Simulate.
      Transparent Commit.
      unfold Commit.
      Transparent Response.
      unfold Response.
      unfold prog. rewrite bind_ret.

      destruct (otf mv) as [[m vi] n] eqn:mvo.
      destruct (otf hy) as [[x h] y] eqn:hyo.

      simpl bind.

      unfold R in e.
      simpl in e.
      repeat (apply andb_prop in e ; destruct e as [e ?]).
      apply reflection_nonsense in e, H1, H2.
      symmetry in H2.
      subst.

      eapply r_transR ; [ apply r_uniform_triple ; intros ; apply rreflexivity_rule | ].
      apply rsymmetry.
      eapply r_transR ; [ apply r_uniform_triple ; intros ; apply rreflexivity_rule | ].

      eapply r_uniform_bij with
        (f := (fun t =>
                 let '(d, r, r_other) := ch3prod t in
                 let '(w, d2, r2) :=
                   if vi
                   then
                     let '(d2,r2) := (d, r) in
                     let 'w := fto ((otf r2) + (m * (otf d2))) in
                     let 'd := fto (otf c - otf d2) in
                     (w, d, r_other)
                   else
                     let '(d2,r1) := (d, r_other) in
                     (fto ((otf r1) + (m * (otf c - otf d2))), fto (otf d2), r)
                 in
                 prod3ch (w, d2, r2) (* w d r *)
        )).
      {
        eapply Bijective with
          (g :=  fun (wdr : Arit (uniform (_ * _ * _))) =>
                   let '(w, d2, r2) := ch3prod wdr in
                   let '(d, r, r_other) :=
                     if vi
                     then
                       let d := fto (otf c - otf d2) in
                       let r := fto (otf w - (otf c - otf d2) * m) in
                       (d, r, r2)
                     else
                       let r := fto (otf w - m * (otf c - otf d2)) in
                       let r2 := r2 in
                       (d2, r2, r)
                   in
                   prod3ch (d, r, r_other)).
        {
          intros xyz.
          rewrite -[RHS](prod3ch_ch3prod xyz).
          simpl.
          set (ch3prod _) at 2.
          destruct s as [[d r] r_other] eqn:wrd_eq.
          subst s.
          rewrite wrd_eq.

          rewrite (if_bind (fun '(x,y,z) => _)).
          rewrite if_bind.
          rewrite !ch3prod_prod3ch.
          rewrite !(if_bind (fun '(x,y,z) => _)).

          rewrite if_if.

          rewrite !otf_fto !fto_otf.

          rewrite !subKr.
          rewrite mulrC.
          rewrite !addrK.
          rewrite !fto_otf.

          rewrite if_const.
          reflexivity.
        }
        {
          intros xyz.
          rewrite -[RHS](prod3ch_ch3prod xyz).
          simpl.
          set (ch3prod _) at 2.
          destruct s as [[w d] r] eqn:wrd_eq.
          subst s.
          rewrite wrd_eq.

          rewrite (if_bind (fun '(x,y,z) => _)).
          rewrite if_bind.
          rewrite !ch3prod_prod3ch.
          rewrite !(if_bind (fun '(x,y,z) => _)).

          rewrite if_if.

          rewrite !otf_fto !fto_otf.

          rewrite !subKr.
          rewrite mulrC.
          rewrite !subrK.
          rewrite !fto_otf.

          rewrite if_const.
          reflexivity.
        }
      }
      intros d2r2r1.
      apply rsymmetry.

      simpl ch3prod.

      destruct (ch3prod _) as [[d2 r2] r1] at 2 3.

      rewrite (if_bind (fun '(w,d0,r0) => _)).
      rewrite (if_bind ch3prod).
      rewrite !ch3prod_prod3ch.
      rewrite (if_bind (fun '(w,d0,r0) => _)).

      rewrite !otf_fto.
      rewrite !trunc_pow.
      rewrite !expgD.
      rewrite !trunc_pow.
      rewrite !expgM.

      assert (forall {A} (ℓ : Location) b a c (f g : raw_code A),
                 ⊢ ⦃ λ '(s₀, s₁), s₀ = s₁ ⦄ #put ℓ := (if b then a else c) ;;
                             if b
                             then f
                             else g
                   ≈ if b
                   then #put ℓ := a ;; f
                   else #put ℓ := c ;; g
                    ⦃ Logic.eq ⦄) by now intros ? ? [] ? ? ? ? ; apply rreflexivity_rule.

      assert (forall {A B} b (y z : raw_code A) (f k : A -> raw_code B),
                 (if b
              then x ← y ;;
                   f x
              else x ← z ;;
                   k x) = (x ← (if b then y else z) ;;
                           (if b then f else k) x)) by now intros ; destruct b.

      eapply r_transL.
      1: apply H1.
      apply better_r_put_lhs.


      rewrite H2.

      rewrite !(if_bind bind).

      rewrite (if_then_if).
      rewrite (if_else_if).

      assert (forall {A B} b (x y : raw_code A) (f g : A -> raw_code B),
                 (if b then bind x else bind y) (if b
                  then f
                  else g) = (if b then bind x f else bind y g)) by now intros ; destruct b.
      rewrite H3.
      rewrite !bind_rewrite.

      assert (forall {B} b ℓ (f g : _ -> raw_code B),
                 (if b then x ← get ℓ ;; f x else x ← get ℓ ;; g x) = (x ← get ℓ ;; if b then f x else g x)) by now intros ; destruct b.
      rewrite H4.

      apply getr_set_lhs (* rewrite otf_fto *).

      rewrite (if_bind (fun '(w,d0,r0) => _)).
      rewrite !(if_then_if).
      rewrite !(if_else_if).


      rewrite !(if_bind bind).
      unfold bind at 1 2.

      assert (forall {A B} b (x y : A) (f g : A -> raw_code B),
                 (if b then (if b
                            then f
                            else g) x else (if b
                            then f
                            else g) y) = (if b then f x else g y)) by now intros ; destruct b.
      rewrite H5.
      rewrite !bind_rewrite.

      rewrite !(trunc_pow).
      rewrite !(expgD).
      rewrite !(trunc_pow).

      rewrite <- (if_bind (fun x => ret x)).
      apply r_ret.

      intros ? ? H_post.
      split ; [clear s₀ s₁ H_post | ].
      2:{
        destruct H_post as [? [H_post ?]].
        subst.
        unfold heap_ignore in H_post.
        unfold heap_ignore.
        intros ℓ H_loc.
        specialize (H_post ℓ H_loc).
        rewrite <- H_post.

        unfold Sigma_locs in H_loc.
        rewrite <- fset1E in H_loc.
        rewrite in_fset1 in H_loc.

        now rewrite get_set_heap_neq.
      }

      set (p := (_,_,_,_)).
      pattern vi in p.
      subst p.

      set (p := (_,_,_,_)) at 2.
      pattern vi in p.
      subst p.

      assert (forall {A} (f g : bool -> A) b, (if b then f b else g b) = if b then f true else g false) by now intros ; destruct b.
      rewrite H6.

      match goal with
      | [ |- context [ _ = ?rhs ] ] => set (p := rhs) ; pattern vi in p ; subst p
      end.

      assert (forall {A} (f : bool -> A) b, (if b then f true else f false) = f b) by now intros ; destruct b.
      set (f := fun _ => _).
      rewrite <- (H7 _ f vi).
      subst f.
      hnf.

      rewrite !expg0.
      rewrite !mulg1.

      assert (forall {A} b (a e : A) (c d : A), (if b then a = e else c = d) <-> ((if b then a else c) = (if b then e else d))) by now intros ; destruct b.
      apply H8.

      rewrite !otf_fto.

      assert (forall {A : finType} (x y : A), (fto x = fto y) <-> (x = y)).
      {
        intros.
        (* apply boolp.propeqP. *)
        split.
        - intros.
          rewrite <- (otf_fto y).
          rewrite <- H9.
          rewrite otf_fto.
          reflexivity.
        - easy.
      }

      repeat (rewrite (proj2 (boolp.propeqP _ _) (pair_equal_spec _ _ _ _))).
      rewrite !(proj2 (boolp.propeqP _ _) (H9 (Message) _ _)).
      rewrite !(proj2 (boolp.propeqP _ _) (H9 (MyParam.Response) _ _)).
      repeat (rewrite (proj2 (boolp.propeqP _ _) (pair_equal_spec _ _ _ _))).

      rewrite <- (mulgA (h^+m)).
      rewrite mulgV.
      rewrite mulg1.
      rewrite !subKr.
      rewrite !addrK.

      now destruct vi.
    }
  Qed.

  (* Lemma proving that the output of the extractor defined for Schnorr's *)
  (* protocol is perfectly indistinguishable from real protocol execution. *)
  Lemma extractor_success:
    ∀ LA A,
      ValidPackage LA [interface
                         #val #[ SOUNDNESS ] : chSoundness → 'bool
        ] A_export A →
      ɛ_soundness A = 0.
  Proof.
    intros LA A VA.
    apply: eq_rel_perf_ind_eq.
    2,3: apply fdisjoints0.
    simplify_eq_rel temp.
    destruct temp as [xhy [a [[e z] [e' z']]]].

    unfold Extractor.
    unfold Verify.
    destruct
      (otf xhy) as [[x h] y],
      (otf a) as [[[la1 lb1] la2] lb2],
      (otf z) as [[[lr1 ld1] lr2] ld2],
      (otf z') as [[[rr1 rd1] rr2] rd2].
    rewrite !otf_fto.

    destruct [&& _, _, _ & _] eqn:ando ; [ | now apply r_ret ; intros ; clear -H].
    apply (ssrbool.elimT and4P) in ando.
    destruct ando.
    repeat (apply (ssrbool.elimT andP) in H0 ; destruct H0).
    repeat (apply (ssrbool.elimT andP) in H1 ; destruct H1).
    apply reflection_nonsense in H0, H6, H5, H4, H3, H1, H9, H8, H7, H2.

    unfold R.

    apply f_equal with (f := fto) in H0, H1.
    rewrite !fto_otf in H0, H1.

    subst la1 lb1 la2 lb2.

    apply (proj1 (prod_swap_iff _ _ _ _)) in H9, H7, H8, H2.
    rewrite <- mulgA in H9, H7, H8, H2.

    rewrite !mulg_invg_sub in H9, H7, H8, H2.
    symmetry in H9, H7, H8, H2.
    apply (proj2 (prod_swap_iff _ _ _ _)) in H9, H7, H8, H2.
    rewrite !mulg_invg_left_sub in H9, H7, H8, H2.

    assert (ld1 - rd1 + (ld2 - rd2) <> 0).
    {
      subst e e'.
      clear -H.
      intros ?.
      assert (fto (ld1 + ld2) = fto (rd1 + rd2)).
      2:{
        rewrite H1 in H.
        rewrite eqxx in H.
        discriminate.
      }
      f_equal.
      apply /eqP.
      setoid_rewrite <- (subr_eq (ld1 + ld2) rd1 rd2).
      rewrite <- addrA.
      rewrite addrC.
      rewrite <- (add0r rd1).
      setoid_rewrite <- subr_eq.
      rewrite <- addrA.
      rewrite addrC.
      apply /eqP.
      apply H0.
    }

    assert ((ld1 - rd1) <> 0 \/ (ld2 - rd2) <> 0).
    {
      destruct (ld1 == rd1) eqn:is_eq;
        [ apply (ssrbool.elimT eqP) in is_eq
        | apply (ssrbool.elimF eqP) in is_eq ].
      - rewrite is_eq in H3.
        rewrite addrN in H3.
        rewrite add0r in H3.
        now right.
      - left.
        red ; intros.
        apply is_eq.
        now apply /eqP ; setoid_rewrite <- subr_eq0 ; apply /eqP.
    }

    apply r_ret ; split ; [ clear H5 ; symmetry | easy ].

    assert (if_bind : forall b (a : gT) (c d : 'Z_q), (a ^+ (if b then c else d)) = (if b then a ^+ c else a ^+ d)) by now clear ; intros [].

    replace (g ^+ _) with (x ^+ (if ld1 - rd1 != 0 then (ld1 - rd1) / (ld1 - rd1) else (ld2 - rd2) / (ld2 - rd2))) by
      now destruct (ld1 - rd1 != 0) ; rewrite !trunc_pow !expgM ; [ rewrite H9 | rewrite H7 ].

    replace (h ^+ _) with ((y * g ^- (~~ (ld1 - rd1 != 0))) ^+ (if ld1 - rd1 != 0 then (ld1 - rd1) / (ld1 - rd1) else (ld2 - rd2) / (ld2 - rd2))).
    2:{
      destruct (ld1 - rd1 != 0) ; rewrite !trunc_pow !expgM ; [ rewrite H8 | rewrite H2 ].
      - rewrite expg0.
        rewrite invg1.
        rewrite mulg1.
        reflexivity.
      - rewrite expg1.
        reflexivity.
    }

    destruct (ld1 == rd1) eqn:is_zero;
      [ apply (ssrbool.elimT eqP) in is_zero
      | apply (ssrbool.elimF eqP) in is_zero ].
    {
      rewrite is_zero in H4 |- *.
      rewrite addrN in H4 |- *.
      rewrite eqxx.
      simpl (~~ true) ; hnf.

      destruct H4 ; [ contradiction | ].
      rewrite !div_cancel ; [ | assumption ..].

      rewrite <- !(mulgA _ g^-1).
      rewrite !mulVg.
      rewrite mulg1.

      now rewrite !eqxx.
    }
    {
      assert (ld1 - rd1 <> 0).
      {
        red ; intros.
        apply is_zero.
        now apply /eqP ; setoid_rewrite <- subr_eq0 ; apply /eqP.
      }
      rewrite (ssrbool.introF eqP H5).
      simpl (~~false) ; hnf.

      rewrite !div_cancel ; [ | assumption ..].

      rewrite expg0.
      rewrite invg1.
      rewrite !mulg1.

      now rewrite !eqxx.
    }
  Qed.

End OVN_or_proof.
