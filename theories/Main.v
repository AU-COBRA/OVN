From OVN Require Import BoardroomVoting BoardroomMath.
From OVN Require Import OVN.



Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp Require Import all_ssreflect all_algebra reals distr realsum
  fingroup.fingroup solvable.cyclic prime ssrnat ssreflect ssrfun ssrbool ssrnum
  eqtype choice seq ssralg.

From Crypt Require Import Axioms ChoiceAsOrd SubDistr Couplings
  UniformDistrLemmas FreeProbProg Theta_dens RulesStateProb UniformStateProb
  pkg_composition Package Prelude SigmaProtocol Schnorr DDH.
Set Warnings "notation-overridden,ambiguous-paths".

Import GRing.Theory.

Module FieldEquivalence.
  (* 
    To show that the implementations of OVN in ConCert and SSProve are equivalent in some
    sense we need to show that their implementations of finite fields are equivalent.
  *)

  Section FieldEquivalence.
 (*
    First, we show that if R is a field in the standard library then it is a field in mathcomp.
    This is enough since BoardroomAxioms_field_theory field states that a field as defined 
    by the BoardroomAxioms is a field in the Coq standard library.
 *)
 (* Define a supposed field in mathcomp. *)
  Require Import Setoid.
  Variables (R : Type) (ReqMixin : Equality.mixin_of R) (RchoiceMixin : Choice.mixin_of R).
  
  Canonical R_eqType := EqType R ReqMixin.
  Canonical R_choiceType := ChoiceType R RchoiceMixin.
 
  (* We need to assume R has choiceType. This is a reasonable assumption as we are working
     with finite fields and one can prove Choice for countable types so in particular for 
     finite types. *)
  Variable (rO rI : R) (radd rmul rsub: R -> R -> R) (ropp : R -> R).
  Variable (rdiv : R -> R -> R) (rinv : R -> R).

  From Coq Require Import Field.
  (* First, we assume R is a field in the standard library. *)
  Axiom R_field_theory :
    field_theory
      rO rI
      radd rmul
      rsub ropp
      rdiv rinv
      eq.
  
  Ltac R_is_field := pose R_field_theory as f; inversion f; clear f; inversion F_R.

  Definition runit (r : R) := r != rO.

  Axiom rinv0 : rinv rO = rO.

  (* We then show that R is an abelian group in mathcomp. *)
  Section RisZmod. 
    Lemma raddA : associative radd.
    Proof.
      R_is_field. unfold associative. apply Radd_assoc.
    Qed.

    Lemma raddC : commutative radd.
    Proof.
      R_is_field. unfold commutative. apply Radd_comm.
    Qed.
  
    Lemma rO_id: left_id rO radd.
    Proof.
      R_is_field. unfold left_id. apply Radd_0_l.
    Qed.

    Lemma ropp_inverse : left_inverse rO ropp radd.
    Proof.
      R_is_field. unfold left_inverse. intros. rewrite Radd_comm. apply Ropp_def.
    Qed.

    Definition zmodmixin := ZmodMixin raddA raddC rO_id ropp_inverse.
  End RisZmod.
  
  Canonical R_ZmodType := ZmodType R zmodmixin.
  Check (R_ZmodType : zmodType).

  (* And a (commutative) ring. *)
  Section RisRing.
    Lemma rmulC : commutative rmul.
    Proof.
      R_is_field. unfold commutative. apply Rmul_comm.
    Qed.

    Lemma rmulA : associative rmul.
    Proof.
      R_is_field. unfold associative. apply Rmul_assoc.
    Qed.
    
    Lemma rI_left_id : left_id rI rmul.
    Proof.
      R_is_field. unfold left_id. apply Rmul_1_l.
    Qed.

    Lemma rI_right_id : right_id rI rmul.
    Proof.
      R_is_field. unfold right_id. intros. rewrite Rmul_comm. apply Rmul_1_l.
    Qed.
    
    Lemma left_dist_rmul_radd : left_distributive rmul radd.
    Proof.
      R_is_field. unfold left_distributive. apply Rdistr_l.
    Qed.
    
    Lemma right_dist_rmul_radd : right_distributive rmul radd.
    Proof.
      R_is_field. unfold right_distributive. intros.
      rewrite Rmul_comm. symmetry. rewrite Rmul_comm Radd_comm Rmul_comm Radd_comm.
      symmetry. apply Rdistr_l.
    Qed.

    Lemma rmul0_left : left_zero rO rmul.
    Proof.
      R_is_field. unfold left_zero. intros.
      now rewrite <- (Radd_0_l (rmul rO x)), <- (Ropp_def (rmul rO x)), Radd_comm, 
        Radd_assoc, Ropp_def, <- Rdistr_l, Radd_0_l, Ropp_def.
    Qed.

    Lemma rmul0_right : right_zero rO rmul.
    Proof.
      R_is_field. unfold right_zero. intros. rewrite Rmul_comm. apply rmul0_left.
    Qed.

    Lemma rmul_ropp : forall (x y : R), rmul (ropp x) y = ropp (rmul x y).
    Proof.
      R_is_field. intros.
      rewrite <- (Radd_0_l (ropp (rmul x y))), <- rmul0_left with (x:=y), <- (Ropp_def x), 
        Radd_comm, Rdistr_l, Radd_assoc.
      assert (H : radd (ropp (rmul x y)) (rmul x y) = radd (rmul x y) (ropp (rmul x y))) by apply Radd_comm.
      rewrite H. 
      rewrite Ropp_def. 
      now rewrite Radd_0_l.
    Qed.
    
    Lemma rmul_ropp_symm : forall (x y : R), rmul (ropp x) y = rmul x (ropp y).
    Proof.
      R_is_field. intros.
      rewrite rmul_ropp. rewrite Rmul_comm. now rewrite <- rmul_ropp.
    Qed.
    
    Lemma rInotrO: rI != rO.
    Proof.
      R_is_field. apply/eqP. apply F_1_neq_0. 
    Qed.
    
    Definition ringmixin := RingMixin rmulA rI_left_id rI_right_id 
      left_dist_rmul_radd right_dist_rmul_radd rInotrO.  
  End RisRing.
  
  Canonical R_RingType := Eval hnf in RingType R ringmixin.
  Check (R_RingType : ringType).

  Canonical R_ComRingType := Eval hnf in ComRingType R rmulC.
  Check (R_ComRingType : comRingType).

  (* R is also a (commutative) unit ring. *)
  Section RisUnitRing.
    Lemma unit_ring (x : R) : x !=  rO -> rmul (rinv x) x = rI.
    Proof.
      R_is_field. intros Hneg. move/eqP in Hneg. specialize (Finv_l x). now apply Finv_l.
    Qed.

    Definition fieldunitmixin := FieldUnitMixin unit_ring rinv0.
  End RisUnitRing.
(*
  Definition test := UnitRingType R fieldunitmixin.
  Eval hnf in test.
  Eval compute in (2+2).
  Eval cbv beta delta in (2+2).
*)  

  Canonical R_UnitRingType := Eval hnf in UnitRingType R fieldunitmixin.
  Canonical R_ComUnitRingType := Eval hnf in [comUnitRingType of R].

  Check (R_UnitRingType : unitRingType).
  Check (R_ComUnitRingType : comUnitRingType).
  
  (* And an integral domain. *)
  Section RisIdomain.
    Lemma R_field_axiom : GRing.Field.mixin_of R_UnitRingType.
    Proof.
      cbv; eauto.
    Qed.

    Definition fieldidomainmixin := (FieldIdomainMixin R_field_axiom).
  End RisIdomain.

  Canonical R_IdomainType := Eval hnf in IdomainType R (FieldIdomainMixin R_field_axiom).
  Check (R_IdomainType : idomainType).
  
  (* Finally, R is a field! *)
  Canonical R_FieldType := FieldType R R_field_axiom.
  Check (R_FieldType : fieldType).

  Definition field_stdlib_to_mathcomp : fieldType := R_FieldType.
End FieldEquivalence.
End FieldEquivalence.

Module BoardroomIsFinGroupType.
  (* We want to show that Z/nZ is isomorphic to Zn since Zn has the type finGroupType and is
     the group we are working with in ovn while Z/nZ is a quotient of the same type as used
     in boardroom voting. Since the quotient in boardroom has n elements it is isomorphic to 
     Z/nZ and if we can show the afoare mentioned isomorphism we can show that the group in 
     boardroomvoting is isomorphic to the group in ovn. *)
  (* In the following we assume that n>0 since otherwise Zn the empty set. *)
  Variable (n' : nat).
  Local Notation n := n'.+1.
  Definition (Zn : finGroupType) := [finGroupType of 'Z_n].
  (* The group operation should be the following: Zp0 for the identity element for addition,
     Z_opp for the inverse function of addition, and Z_add for addition. 'Z_n is also a ring
     (when n>1 since otherwise it is the trivial ring which the formalisation of ssralg/finalg
     does not like) with identity Zp1 for multiplication (this is also a generator of the additive
     group), Zp_mul for multiplication, and Zp_inv for the inverse function of multiplication. *)
End BoardroomIsFinGroupType.

Module FunctionalEq (BP : BoardroomParams) (OP : OVNParam).

  Definition A := BP.A. (* Base group *)
  Module BV := BoardroomVoting BP.
  Import BV.

  Module GroupP : GroupParam.

    Parameter n : nat.
    Parameter n_pos : Positive n.

    Parameter gT : finGroupType. (* THIS IS A (play pretend) *)
    Definition ζ : {set gT} := [set : gT].
    Parameter g :  gT.
    Parameter g_gen : ζ = cycle_group g.
    Parameter prime_order : prime (order g).
  End GroupP.

  Module OVN := OVN GroupP OP.
  Import OVN. 

  Theorem equivalent_pk (sk : A) : 
    compute_public_key sk 

  Proof.
    
  Qed.
  
End FunctionalEq.