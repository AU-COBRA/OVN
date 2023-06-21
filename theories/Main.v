From OVN Require Import BoardroomVoting BoardroomMath.
From OVN Require Import OVN.

Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp Require Import all_ssreflect all_algebra reals distr realsum
  fingroup.fingroup solvable.cyclic prime ssrnat ssreflect ssrfun ssrbool ssrnum
  eqtype choice seq ssralg.
Set Warnings "notation-overridden,ambiguous-paths".
From HB Require Import structures.
Import GRing.Theory.

Section FieldEquivalence.
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
  Variable R : Type.
  Variable (rO rI : R) (radd rmul rsub: R->R->R) (ropp : R -> R).
  Variable (rdiv : R -> R -> R) (rinv : R -> R).
  Variable req : R -> R -> bool. (* rel R same as R -> R -> bool *)

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

Locate isZmodule.Build.

    Definition zmod_Mixin := ZmodMixin raddA raddC rO_id ropp_inverse.
  End RisZmod.

  (*HB.instance Definition _ := RisZmod.Mixin.*)

  (* And a commutative ring. *)
  Section RisComRing.
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

    Lemma rInotrO: ~ (eq rI rO).
    Proof.
      R_is_field. apply F_1_neq_0.
    Qed.
  
    Definition ring_Mixin := GRing.Zmodule_isRing.Build R rI rmul rmulA rI_left_id rI_right_id 
      left_dist_rmul_radd right_dist_rmul_radd rInotrO. 
    
    Definition ring_Mixin' := GRing.Zmodule_isComRing.Build R rmulA rmulC rI_left_id 
      left_dist_rmul_radd rInotrO.
    
  End RisComRing.
  (* Zmodule_isComRing 2584*)

  (*HB.instance Definition _ := RisComRing.Mixin.*)
  
  (* We must then show that R is an integral domain. Not necessary when using comring? Then need inv0 = 0... which is not true in Q... *)
  Section RisIdomain.
      Lemma idomain_axiom (x y : R) : rmul x y = rO -> (req x rO) || (req y rO).
      Proof.
        R_is_field. intros. 
      Qed.
      
  End RisIdomain.
*)
  
  (* Since R is a commutative ring and an integral domain it is a field in mathcomp. *)
  Section RisField.
    Lemma unit_ring : forall (x : R), ~(eq x rO) -> rmul (rinv x) x = rI.
    Proof.
      R_is_field. apply Finv_l.
    Qed.

    Lemma rinv0 : rinv rO = rO.
    Proof.
      R_is_field.
    Qed.
    
    
  End RisField.
  (* ComRing_isField 4100 *)

  Definition field_stdlib_to_mathcomp :
    fieldType.
  Proof.
    pose R_field_theory as f.
    inversion f. clear f.
    inversion F_R. 
    exists R.
    econstructor. econstructor.
  Qed.

End FieldEquivalence.