From OVN Require Import BoardroomVoting BoardroomMath.
From OVN Require Import OVN.

Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp Require Import all_ssreflect all_algebra reals distr realsum
  fingroup.fingroup solvable.cyclic prime ssrnat ssreflect ssrfun ssrbool ssrnum
  eqtype choice seq ssralg.
Set Warnings "notation-overridden,ambiguous-paths".

Import GRing.Theory.

Module FieldEquivalence.
  (* 
    To show that the implementations of OVN in ConCert and SSProve are equivalent in some
    sense we need to show that their implementations of finite fields are equivalent.
  *)

  
 (*
    First, we show that if R is a field in the standard library then it is a field in mathcomp.
    This is enough since BoardroomAxioms_field_theory field states that a field as defined 
    by the BoardroomAxioms is a field in the Coq standard library.
 *)
  (* Define a supposed field in mathcomp. *)
  Require Import Setoid.
  Variable R : choiceType.
  (* We need to assume R has choiceType. This is a reasonable assumption as we are working
     with finite fields and one can prove Choice for countable types so in particular for 
     finite types. *)
  Variable (rO rI : R) (radd rmul rsub: R -> R -> R) (ropp : R -> R).
  Variable (rdiv : R -> R -> R) (rinv : R -> R).
  (*Variable req : R -> R -> Prop. (* rel R same as R -> R -> bool *)*)
  


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

  (*Definition runit (r : R) := r != rO.*)

  Axiom rinv0 : rinv rO = rO.

  Axiom eq_dec : forall (x y : R), (x == y) \/ (x != y).

  Lemma neq_refl : forall a b : R, a<>b <-> a!=b. 
  Proof.
Admitted.

  (* We then show that R is an abelian group in mathcomp. *)
  Module RisZmod. 
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
  
  Canonical R_ZmodType := ZmodType R RisZmod.zmodmixin.
  Check (R_ZmodType : zmodType).

  (* And a (commutative) ring. *)
  Module RisRing.
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
      R_is_field. rewrite <- neq_refl. apply F_1_neq_0.
    Qed.
    
    Definition ringmixin := RingMixin rmulA rI_left_id rI_right_id 
      left_dist_rmul_radd right_dist_rmul_radd rInotrO.  
    Check ringmixin.
    (*
    Definition comringmixin := ComRingMixin rmulA rmulC rI_left_id 
      left_dist_rmul_radd rInotrO.*)
  End RisRing.

  Canonical R_RingType := RingType R_ZmodType RisRing.ringmixin.
  Check (R_RingType : ringType).
  Canonical R_ComRingType := ComRingType R_RingType RisRing.rmulC.
  Check (R_ComRingType : comRingType).

  (* R is also a unit (commutative) ring. *)
  Definition runit (r : R_RingType) := r != rO.
  Module RisUnitRing.
    Lemma left_unit : {in runit, left_inverse rI rinv rmul}.
    Proof.
      R_is_field. intros x Hunit. rewrite Finv_l. auto.
      unfold runit in Hunit. rewrite neq_refl. apply Hunit.
    Qed.
    
    Lemma right_unit : {in runit, right_inverse rI rinv rmul}.
    Proof.
      R_is_field. intros x Hunit. rewrite Rmul_comm. now apply left_unit.
    Qed.

    Lemma multinv_then_unit : forall x y : R_RingType, rmul y x = rI /\ rmul x y = rI -> runit x.
    Proof.
      R_is_field. intros x y [Hyx Hxy]. 
      unfold runit. rewrite <- neq_refl. intros contra. intuition. 
    Qed.

    Lemma com_multinv_then_unit : forall x y : R_ComRingType, rmul y x = rI -> runit x.
    Proof.
      R_is_field. intros x y Hyx. 
      unfold runit. rewrite <- neq_refl. intros contra. intuition. 
    Qed.

    Lemma inv_unit : {in [predC runit], rinv =1 id}. 
    Proof.
      intros x H. unfold predC in H. rewrite inE in H. unfold "\notin" in H. 
      destruct (x \in runit) eqn:E.
      - discriminate. 
      - clear H.
        unfold runit in E. unfold "\in" in E. simpl in E. 
        destruct (eq_dec x rO); rewrite /is_true in H.
        + clear E.
          apply (ssrbool.elimT eqtype.eqP) in H.
          rewrite H. apply rinv0.
        + rewrite H in E. discriminate.
    Qed.
    
    (*Definition unitringmixin := UnitRingMixin left_unit right_unit multinv_then_unit inv_unit.*)
    Definition comunitringmixin := ComUnitRingMixin left_unit com_multinv_then_unit inv_unit.
  End RisUnitRing.

  (*Canonical R_UnitRingType := UnitRingType R_RingType RisUnitRing.unitringmixin.*)
  Canonical R_ComUnitRingType := UnitRingType R_ComRingType RisUnitRing.comunitringmixin.
  
  (* And an integral domain. *)
  Module RisIdomain.
    Lemma integraldomain_axiom : GRing.IntegralDomain.axiom R_RingType.
    Proof.
      unfold GRing.IntegralDomain.axiom.
      R_is_field. 
      
      intros x y H. destruct (eq_dec x rO).
      - unfold "||". now rewrite H0.
      - specialize (Finv_l x). rewrite <- neq_refl in H0. specialize (Finv_l H0).
        assert (multinv : forall a b c, b = c -> rmul a b = rmul a c). 
          { intros. rewrite H1. reflexivity. }
        specialize (multinv (rinv x) (rmul x y) rO).
        specialize (multinv H).
        rewrite RisRing.rmul0_right in multinv.
        rewrite Rmul_assoc Finv_l Rmul_1_l in multinv.
        unfold "||". destruct (x == rO); auto.
        now rewrite multinv. 
    Qed.
    
    Lemma idomain_axiom : forall x y, rmul x y = rO -> (x == rO) || (y == rO).
    Proof.
      R_is_field. intros x y H. destruct (eq_dec x rO).
      - unfold "||". now rewrite H0.
      - specialize (Finv_l x). rewrite <- neq_refl in H0. specialize (Finv_l H0).
        assert (multinv : forall a b c, b = c -> rmul a b = rmul a c). 
          { intros. rewrite H1. reflexivity. }
        specialize (multinv (rinv x) (rmul x y) rO).
        specialize (multinv H).
        rewrite RisRing.rmul0_right in multinv.
        rewrite Rmul_assoc Finv_l Rmul_1_l in multinv.
        unfold "||". destruct (x == rO); auto.
        now rewrite multinv. 
    Qed.  
  End RisIdomain.
  Canonical R_IdomainType := IdomainType R_ComUnitRingType RisIdomain.idomain_axiom.
  
  (* Finally, R is a field! *)
  Module RisField.
    Lemma unit_ring : forall (x : R), ~(eq x rO) -> rmul (rinv x) x = rI.
    Proof.
      R_is_field. apply Finv_l.
    Qed.
    
    Definition fieldunitmixin := FieldUnitMixin unit_ring rinv0.
    Definition fieldidomainmixin := FieldIdomainMixin fieldunitmixin.
    Definition R_fieldish := GRing.Field.IdomainType unit_ring rinv0.
    Definition fieldmixin := FieldMixin unit_ring rinv0.
  End RisField.
  Canonical R_FieldType := FieldType R_fieldish fieldmixin.

  Definition field_stdlib_to_mathcomp :
    fieldType.
  Proof.
    exists R_FieldType.
  Qed.

End FieldEquivalence.