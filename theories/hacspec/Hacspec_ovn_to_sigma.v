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


Module Misc.

  Lemma hasChoice_surjective : forall {A B : Type},
    forall {f : A -> B} {f_inv : B -> A} `(η : cancel f_inv f),
      hasChoice.axioms_ A ->
      hasChoice.axioms_ B.
  Proof.
    intros A B f f_inv η [].
    refine ({| hasChoice.find_subdef := (fun P n => match find_subdef (fun x => P (f x)) n with
                                                 | Some x => Some (f x)
                                                 | None => None
                                                 end) |}).
    - intros.
      destruct (find_subdef (fun x => P (f x)) n) eqn:Heq.
      + inversion H.
        subst.
        apply (choice_correct_subdef (fun x => P (f x)) n a Heq).
      + discriminate H.
    - intros.
      destruct (choice_complete_subdef (fun x => P (f x)) (match H with ex_intro _ x H_P => ex_intro _ (f_inv x) (eq_ind_r P H_P (η x)) end )).
      exists x. now destruct (find_subdef _ _).
    - intros P Q H_eq n.
      now rewrite (choice_extensional_subdef (fun x => P (f x)) (fun x => Q (f x)) (fun x => H_eq (f x)) n).
  Qed.

  Lemma Choice_isCountable_surjective : forall {A B},
    forall {f : A -> B} {f_inv : B -> A} `(η : cancel f_inv f),
      Choice_isCountable.axioms_ A ->
      Choice_isCountable.axioms_ B.
  Proof.
    intros A B f f_inv η [].
    refine {|
        Choice_isCountable.pickle := fun x => pickle (f_inv x);
        Choice_isCountable.unpickle := fun x => Option.map f (unpickle x);
        Choice_isCountable.pickleK := _
      |}.
    intros x.
    rewrite (pickleK (f_inv x)).
    simpl.
    now rewrite η.
  Qed.

  Lemma equality_surjective : forall {A B},
    forall {f : A -> B} {f_inv : B -> A} `(η : cancel f_inv f),
      hasDecEq.axioms_ A ->
      hasDecEq.axioms_ B.
  Proof.
    intros A B f f_inv η H_eq.
    assert (@injective (Equality.sort (@Equality.Pack A (@Equality.Class A H_eq))) _ f_inv) by easy.
    apply (eqtype_inj_type__canonical__eqtype_Equality H).
  Qed.

  Lemma bijection_is_adjoint : forall {A B : eqType},
    forall (f : A -> B) (f_inv : B -> A),
      (forall (x : B), f (f_inv x) == x) /\ (forall x, f_inv (f x) == x) <-> forall x y, (f y == x) = (y == f_inv x).
  Proof.
    intros.
    split.
    - intros [] x y.
      specialize (H x).
      specialize (H0 y).
      apply (ssrbool.elimT eqP) in H.
      apply (ssrbool.elimT eqP) in H0.
      apply Bool.eq_iff_eq_true.
      now split ; intros ; apply (ssrbool.elimT eqP) in H1 ; apply (ssrbool.introT eqP).
    - intros.
      split ; [ intros x ; set (y := f_inv x) |
                intros y ; set (x := f y) ; rewrite eq_sym ; symmetry in H ] ;
        specialize (H x y) ;
        now rewrite H.
  Qed.

  Lemma isFinite_bijective : forall {A B},
    forall {f : A -> B} {f_inv : B -> A} `(η : cancel f_inv f) `(β : cancel f f_inv),
    forall (H_eq : Equality.mixin_of A),
      isFinite.axioms_ A H_eq ->
      isFinite.axioms_ B (equality_surjective η H_eq).
  Proof.
    intros A B f f_inv η β H_eq [].

    pose (eqA := @Equality.Pack A (@Equality.Class A H_eq)).
    pose (eqB := @Equality.Pack B (@Equality.Class B (@equality_surjective A B f f_inv η H_eq))).

    refine {|
        isFinite.enum_subdef := [ seq f i | i <- enum_subdef ];
        isFinite.enumP_subdef := _;
      |}.

    assert (H : injective (aT := Equality.sort eqA) (rT := Equality.sort eqB) f) by easy ; epose proof (H_inj := eqtype.inj_eq H) ; simpl in H_inj ; clear H.

    assert (H : injective (aT := Equality.sort eqB) (rT := Equality.sort eqA) f_inv) by easy ; epose proof (H_inv_inj := eqtype.inj_eq H) ; simpl in H_inv_inj ; clear H.

    intros x ; simpl in x.
    rewrite count_map.
    rewrite <- (enumP_subdef (f_inv x)).
    clear -H_inj (* H_inv_inj η *) β.
    induction enum_subdef as [ | y ] ; [ reflexivity | ] ; simpl in *.
    rewrite (IHenum_subdef).
    f_equal.
    f_equal. (* remove nat_of_bool *)
    apply (proj1 (bijection_is_adjoint (A := eqA) (B := eqB) f f_inv)).
    now split ; intros ; [ rewrite η | rewrite β ].
  Qed.

  Definition finite_bijective : forall {A B},
    forall (f : A -> B) (f_inv : B -> A) `(η : cancel f_inv f) `(β : cancel f f_inv),
      Finite.axioms_ A ->
      Finite.axioms_ B.
  Proof.
    intros A B f f_inv η β H.
    refine {|
        Finite.choice_hasChoice_mixin := hasChoice_surjective η H ;
        Finite.choice_Choice_isCountable_mixin := Choice_isCountable_surjective η H;
        Finite.fintype_isFinite_mixin := isFinite_bijective η β H H
      |}.
  Qed.

  Lemma is_pure_cancel_ret_both : forall {A : choice_type}, cancel (@ret_both A) (@is_pure A).
  Proof. easy. Qed.

  Definition finite_to_word {n} (x : 'I_(Z.to_nat (modulus n)).-1.+1) : n.-word :=
    mkword _ (Z.of_nat (nat_of_ord x)).

  Definition word_to_finite {n} (x : n.-word) : 'I_((Z.to_nat (modulus n)).-1.+1) := inord (Z.to_nat (toword x)).

  Lemma finite_word_cancel : forall {n}, cancel word_to_finite (finite_to_word (n := n)).
  Proof.
    intros.
    unfold word_to_finite, finite_to_word.
    intros x ; clear.
    rewrite inordK.
    - rewrite Z2Nat.id.
      + now rewrite ureprK.
      + now destruct x as [[] ?].
    - destruct x.
      simpl.
      apply (ssrbool.elimT andP) in i as [].
      apply Z.leb_le in H.
      apply Z.ltb_lt in H0.
      apply (ssrbool.introT (jasmin_util.ZNltP _ _)).
      rewrite Nat.succ_pred.
      + now rewrite !Z2Nat.id.
      + unfold modulus.
        unfold two_power_nat.
        easy.
  Qed.

  Lemma word_finite_cancel : forall {n}, cancel (finite_to_word (n := n)) word_to_finite.
  Proof.
    intros.
    unfold finite_to_word, word_to_finite.
    intros x.

    destruct n.
    {
      simpl in x |- *.
      rewrite Z.mod_1_r.
      unfold Z.to_nat.
      destruct x as [[]].
      + unfold inord, insubd, odflt, oapp, insub.
        destruct idP ; now apply ord_ext.
      + discriminate i.
    }

    rewrite mkword_val_small.
    2:{
      destruct x ; simpl.
      rewrite <- modulusE.
      rewrite Nat.succ_pred in i. 2: now unfold modulus, two_power_nat .
      apply (ssrbool.introT andP) ; split ; [ apply Z.leb_le | apply Z.ltb_lt ].
      - eapply (ssrbool.elimT (isword_ofnatZP _ _)).
        apply (ltn_expl m).
        easy.
      - eapply Z.lt_le_trans ; [ apply (ssrbool.elimT (jasmin_util.ZNltP _ _) i) | ].
        clear.
        rewrite !Z2Nat.id. 2: easy.
        unfold modulus.
        now rewrite two_power_nat_equiv.
    }
    rewrite Nat2Z.id.
    now rewrite inord_val.
  Qed.

  Definition word32_Finite (n : nat) : Finite (word n) :=
    finite_bijective
      finite_to_word
      word_to_finite finite_word_cancel word_finite_cancel
      (Finite.fintype_isFinite_mixin (Finite.class (fintype_ordinal__canonical__fintype_Finite (Z.to_nat (modulus n)).-1.+1))).

End Misc.

Module Type GroupOperationProperties (OVN_impl : Hacspec_ovn.HacspecOVNParams).
  Import OVN_impl.

  (* Notation v_G := OVN_impl.v_G. *)
  (* Instance v_G_t_Group : t_Group v_G := OVN_impl.v_G_t_Group. *)

  (* Notation v_Z := v_G_t_Group.(f_Z). *)
  (* Instance v_Z_t_Field : t_Field v_Z := _. *)

  Axiom add_sub_cancel : forall a b, f_add a (f_sub b a) ≈both b.
  Axiom add_sub_cancel2 : forall a b, f_add (f_sub b a) a ≈both b.
  (* Definition hacspec_group_type : Type := (Choice.sort (chElement v_G)). *)
  Axiom prod_pow_add_mul : forall x y z, f_prod (f_g_pow x) (f_pow (f_g_pow z) y) ≈both f_g_pow (f_add x (f_mul z y)).
  Axiom prod_pow_pow : forall h x a b, f_prod (f_pow h x) (f_pow (f_pow h a) b) ≈both f_pow h (f_add x (f_mul a b)).
  Axiom div_prod_cancel : forall x y, f_div (f_prod x y) y ≈both x.

  Axiom mul_comm : forall x y, f_mul x y ≈both f_mul y x.

  (* HB.instance Definition sort_group : hasChoice (Choice.sort (chElement v_G)) := _. (* Choice.clone (Choice.sort (chElement v_G)) _.  *) *)

  Axiom both_v_G_choice : hasChoice.axioms_ (both v_G).
  Axiom both_v_G_countable : Choice_isCountable (both v_G).
  Axiom both_v_G_hasDecEq : hasDecEq (both v_G).
  Axiom both_v_G_isFinite : isFinite.axioms_ (both v_G) both_v_G_hasDecEq.
  Definition both_v_G_Finite : Finite (both v_G) :=
    {|
      Finite.choice_hasChoice_mixin := both_v_G_choice;
      Finite.choice_Choice_isCountable_mixin := both_v_G_countable;
      Finite.eqtype_hasDecEq_mixin := both_v_G_hasDecEq;
      Finite.fintype_isFinite_mixin := both_v_G_isFinite
    |}.

  Axiom v_G_countable : Choice_isCountable (Choice.sort (chElement v_G)).
  Axiom v_G_isFinite : isFinite (Choice.sort (chElement v_G)).
  Definition v_G_Finite : Finite (Choice.sort (chElement v_G)) :=
    {|
      Finite.choice_hasChoice_mixin := Choice.choice_hasChoice_mixin (Choice.class v_G);
      Finite.choice_Choice_isCountable_mixin := v_G_countable;
      Finite.eqtype_hasDecEq_mixin := Choice.eqtype_hasDecEq_mixin (Choice.class v_G);
      Finite.fintype_isFinite_mixin := v_G_isFinite
    |}.

  Axiom both_v_Z_choice : hasChoice.axioms_ (both v_Z).
  Axiom both_v_Z_countable : Choice_isCountable (both v_Z).
  Axiom both_v_Z_hasDecEq : hasDecEq (both v_Z).
  Axiom both_v_Z_isFinite : isFinite.axioms_ (both v_Z) both_v_Z_hasDecEq.
  Definition both_v_Z_Finite : Finite (both v_Z) :=
    {|
      Finite.choice_hasChoice_mixin := both_v_Z_choice;
      Finite.choice_Choice_isCountable_mixin := both_v_Z_countable;
      Finite.eqtype_hasDecEq_mixin := both_v_Z_hasDecEq;
      Finite.fintype_isFinite_mixin := both_v_Z_isFinite
    |}.

  Axiom v_Z_countable : Choice_isCountable (Choice.sort (chElement v_Z)).
  Axiom v_Z_isFinite : isFinite (Choice.sort (chElement v_Z)).
  Definition v_Z_Finite : Finite (Choice.sort (chElement v_Z)) :=
    {|
      Finite.choice_hasChoice_mixin := Choice.choice_hasChoice_mixin (Choice.class v_Z);
      Finite.choice_Choice_isCountable_mixin := v_Z_countable;
      Finite.eqtype_hasDecEq_mixin := Choice.eqtype_hasDecEq_mixin (Choice.class v_Z);
      Finite.fintype_isFinite_mixin := v_Z_isFinite
    |}.


  Definition both_f_field_finType : finType := Finite.Pack both_v_Z_Finite.
  Definition both_f_group_finType : finType := Finite.Pack both_v_G_Finite.

  Definition f_field_finType : finType := Finite.Pack v_Z_Finite.
  Definition f_group_finType : finType := Finite.Pack v_G_Finite.

End GroupOperationProperties.


Module HacspecGroup (OVN_impl : Hacspec_ovn.HacspecOVNParams) (GOP : GroupOperationProperties OVN_impl).
  Import OVN_impl.
  Import GOP.

  (* both v_Z is a field *)
  (* ChoiceEquality_both__canonical__GRing_Field *)
  Axiom v_Z_Field : GRing.Field (v_Z).

  Definition lower1 {A B : choice_type} (f : both A -> both B) : A -> B :=
    fun x => is_pure (f (ret_both x)).

  Definition lower2 {A B C : choice_type} (f : both A -> both B -> both C) : A -> B -> C :=
    fun x y => is_pure (f (ret_both x) (ret_both y)).

  Axiom f_prodA : associative (lower2 f_prod).
  Axiom f_prod1 : associative (lower2 f_prod).
  Axiom f_prod_left_id : left_id (is_pure f_group_one) (lower2 f_prod).
  Axiom f_invK : involutive (lower1 f_inv).
  Axiom f_invM : {morph (lower1 f_inv)  : x y / (lower2 f_prod) x y >-> (lower2 f_prod)  y x}.
  Definition mul_group : isMulBaseGroup (v_G) :=
    {|
      isMulBaseGroup.mulg_subdef := lower2 f_prod;
      isMulBaseGroup.oneg_subdef := is_pure f_group_one;
      isMulBaseGroup.invg_subdef := lower1 f_inv;
      isMulBaseGroup.mulgA_subproof := f_prodA;
      isMulBaseGroup.mul1g_subproof := f_prod_left_id;
      isMulBaseGroup.invgK_subproof := f_invK;
      isMulBaseGroup.invMg_subproof := f_invM
    |}.

  Axiom prod_inv_cancel : forall x, f_prod (f_inv x) x ≈both f_group_one.

  #[export] Definition v_G_BaseFinGroup : baseFinGroupType :=
    BaseFinGroup.Pack
      {|
        BaseFinGroup.fingroup_isMulBaseGroup_mixin := mul_group;
        BaseFinGroup.choice_hasChoice_mixin := v_G_Finite;
        BaseFinGroup.choice_Choice_isCountable_mixin := v_G_Finite;
        BaseFinGroup.eqtype_hasDecEq_mixin := v_G_Finite;
        BaseFinGroup.fintype_isFinite_mixin := v_G_Finite
      |}.
  #[export] Lemma inv_mul_inverse : left_inverse (T := v_G_BaseFinGroup) (R := v_G) (oneg v_G_BaseFinGroup) invg mulg.
  Proof.
    unfold invg, mulg ; change 1%g with (is_pure f_group_one) ; simpl.
    intros x.
    unfold lower1, lower2.
    rewrite hacspec_function_guarantees ; rewrite <- hacspec_function_guarantees2.
    rewrite <- (both_equivalence_is_pure_eq).
    apply prod_inv_cancel.
  Qed.

  Definition v_G_is_group : finGroupType :=
    FinGroup.Pack
      {| FinGroup.fingroup_BaseFinGroup_isGroup_mixin :=
          {| BaseFinGroup_isGroup.mulVg_subproof := inv_mul_inverse |} |}.

  (* prime_cyclic *)

  Axiom v_G_prime_order : prime #[is_pure f_g : v_G_is_group].
  Axiom v_G_g_gen : [set : v_G_is_group] = <[is_pure f_g : v_G_is_group]>.
End HacspecGroup.

Module HacspecGroupParam (OVN_impl : Hacspec_ovn.HacspecOVNParams) (GOP : GroupOperationProperties OVN_impl) <: GroupParam.
  Import OVN_impl.
  Import GOP.

  Module Hacspec_group := HacspecGroup OVN_impl GOP.
  Import Hacspec_group.
  
  Definition gT : finGroupType := v_G_is_group.
  Definition ζ : {set gT} := [set : gT].
  Definition g :  gT := is_pure f_g.

  (* Open Scope group_scope. *)

  Definition prime_order : prime #[g] := v_G_prime_order.
  Definition g_gen : ζ = <[g]> := v_G_g_gen.
End HacspecGroupParam.

Module Z89_impl : HacspecOVNParams.
  #[local] Open Scope hacspec_scope.

  Definition v_Z : choice_type := 'nat.
  Definition v_G : choice_type := 'nat.
  Definition v_A : choice_type := 'nat.
  Definition n : both uint_size := ret_both 55.

  Axiom v_Z_t_Field : t_Field v_Z.
  Axiom v_G_t_Group : t_Group v_G.

  Axiom v_G_t_Eq : t_Eq v_G.
  Axiom v_A_t_HasActions : t_HasActions v_A.

End Z89_impl.

(* Module Z89_group_operations : GroupOperationProperties Z89_impl. *)
(*   #[local] Open Scope hacspec_scope. *)
(*   Import Z89_impl. *)
  
(*   Axiom v_G_t_Group : t_Group v_G. *)
(*   Axiom add_sub_cancel : ∀ a b : both v_Z, f_add a (f_sub b a) ≈both b. *)

(* End Z89_group_operations. *)

(* Module Hacspec_Z89 := HacspecGroupParam Z89_impl . *)

(* Module Schnorr_Z3 := Schnorr. *)

(* Module Schnorr_v_G (OVN_impl : Hacspec_ovn.HacspecOVN) (GOP : GroupOperationProperties OVN_impl) := Schnorr. *)

(* Module HacspecSchnorr (GP : GOP : GroupOperationProperties). *)

(* Import GP. *)

(* (* order of g *) *)
(* Definition q : nat := #[g]. *)


(* Module MyParam <: SigmaProtocolParams. *)
(*   Include HacspecGroup. *)
(*   Include Misc. *)

(*   Definition Witness : finType := Finite.Pack (word32_Finite 32). *)
(*   Locate HacspecGP.v_G_is_group. *)
(*   Check HacspecGP.gT. *)
(*   Definition Statement : finType := v_G_is_group. *)
(*   Definition Message : finType := *)
(*     (Datatypes_prod__canonical__fintype_Finite *)
(*        (Datatypes_prod__canonical__fintype_Finite v_G_is_group v_G_is_group) *)
(*        v_G_is_group). *)
(*   Definition Challenge : finType := f_field_finType. *)
(*   Definition Response : finType :=  f_field_finType. *)
(*   Definition Transcript : finType := *)
(*     prod (prod Message Challenge) Response. *)

(*   Definition w0 : Witness := mkword _ 0 . *)
(*   Definition e0 : Challenge := is_pure f_field_zero. *)
(*   Definition z0 : Response := is_pure f_field_zero. *)

(*   Definition R : Statement -> Witness -> bool := *)
(*     (fun (h : Statement) (w : Witness) => h == ((is_pure f_g : v_G_is_group) ^+ w : v_G_is_group)). *)

(*   #[export] Instance positive_gT : Positive #|f_group_finType|. *)
(*   Proof. *)
(*     apply /card_gt0P. exists (is_pure f_g). auto. *)
(*   Qed. *)

(*   #[export] Instance positive_fT : Positive #|f_field_finType|. *)
(*   Proof. *)
(*     apply /card_gt0P. exists (is_pure f_field_zero). auto. *)
(*   Qed. *)

(*   #[export] Instance Witness_pos : Positive #|Witness|. *)
(*   Proof. *)
(*     apply /card_gt0P. exists (mkword _ 0). auto. *)
(*   Defined. *)

(*   Definition Statement_pos : Positive #|Statement| := _. *)
(*   #[export] Definition Message_pos : Positive #|Message|. *)
(*   Proof. *)
(*     rewrite !card_prod. repeat apply Positive_prod ; apply positive_gT. *)
(*   Defined. *)
(*   Definition Challenge_pos : Positive #|Challenge| := _. *)
(*   Definition Response_pos : Positive #|Response| := _. *)
(*   Definition Bool_pos : Positive #|'bool|. *)
(*   Proof. *)
(*     rewrite card_bool. done. *)
(*   Defined. *)

(* End MyParam. *)



(* Module MyParam <: SigmaProtocolParams. *)

(*   Definition Witness : finType := Finite.clone _ 'Z_q. *)
(*   Definition Statement : finType := gT. *)
(*   Definition Message : finType := gT. *)
(*   Definition Challenge : finType := Finite.clone _ 'Z_q. *)
(*   Definition Response : finType :=  Finite.clone _ 'Z_q. *)
(*   Definition Transcript : finType := *)
(*     prod (prod Message Challenge) Response. *)

(*   Definition w0 : Witness := 0. *)
(*   Definition e0 : Challenge := 0. *)
(*   Definition z0 : Response := 0. *)

(*   Definition R : Statement -> Witness -> bool := *)
(*     (λ (h : Statement) (w : Witness), h == (g ^+ w)). *)

(*   #[export] Instance positive_gT : Positive #|gT|. *)
(*   Proof. *)
(*     apply /card_gt0P. exists g. auto. *)
(*   Qed. *)

(*   #[export] Instance Witness_pos : Positive #|Witness|. *)
(*   Proof. *)
(*     apply /card_gt0P. exists w0. auto. *)
(*   Qed. *)

(*   Definition Statement_pos : Positive #|Statement| := _. *)
(*   Definition Message_pos : Positive #|Message| := _. *)
(*   Definition Challenge_pos : Positive #|Challenge| := _. *)
(*   Definition Response_pos : Positive #|Response| := _. *)
(*   Definition Bool_pos : Positive #|'bool|. *)
(*   Proof. *)
(*     rewrite card_bool. done. *)
(*   Defined. *)

(* End MyParam. *)






(* Module MyAlg <: SigmaProtocolAlgorithms MyParam. *)

(*   Import MyParam. *)

(*   #[local] Existing Instance Bool_pos. *)

(*   Definition choiceWitness : choice_type := 'fin #|Witness|. *)
(*   Definition choiceStatement : choice_type := 'fin #|Statement|. *)
(*   Definition choiceMessage : choice_type := 'fin #|Message|. *)
(*   Definition choiceChallenge : choice_type := 'fin #|Challenge|. *)
(*   Definition choiceResponse : choice_type := 'fin #|Response|. *)
(*   Definition choiceTranscript : choice_type := *)
(*     chProd *)
(*       (chProd (chProd choiceStatement choiceMessage) choiceChallenge) *)
(*       choiceResponse. *)
(*   Definition choiceBool := 'fin #|'bool|. *)

(*   Definition i_witness := #|Witness|. *)

(*   Definition HIDING : nat := 0. *)
(*   Definition SOUNDNESS : nat := 1. *)

(*   Definition commit_loc : Location := (choiceWitness; 2%N). *)

(*   Definition Sigma_locs : {fset Location} := fset [:: commit_loc]. *)
(*   Definition Simulator_locs : {fset Location} := fset0. *)

(*   Definition Commit (h : choiceStatement) (w : choiceWitness): *)
(*     code Sigma_locs [interface] choiceMessage := *)
(*     {code *)
(*       r ← sample uniform i_witness ;; *)
(*       #put commit_loc := r ;; *)
(*       ret (fto (g ^+ (otf r))) *)
(*     }. *)

(*   Definition Response (h : choiceStatement) (w : choiceWitness) (a : choiceMessage) (e : choiceChallenge) : *)
(*     code Sigma_locs [interface] choiceResponse := *)
(*     {code *)
(*       r ← get commit_loc ;; *)
(*       ret (fto (otf r + otf e * otf w)) *)
(*     }. *)

(*   Definition Simulate (h : choiceStatement) (e : choiceChallenge) : *)
(*     code Simulator_locs [interface] choiceTranscript := *)
(*     {code *)
(*       z ← sample uniform i_witness ;; *)
(*       ret (h, fto (g ^+ (otf z) * (otf h ^- (otf e))), e, z) *)
(*     }. *)

(*   Definition Verify (h : choiceStatement) (a : choiceMessage) *)
(*     (e : choiceChallenge) (z : choiceResponse) : choiceBool := *)
(*     fto (g ^+ (otf z) == (otf a) * (otf h) ^+ (otf e)). *)

(*   Definition Extractor (h : choiceStatement) (a : choiceMessage) *)
(*     (e : choiceChallenge) (e' : choiceChallenge) *)
(*     (z : choiceResponse)  (z' : choiceResponse) : 'option choiceWitness := *)
(*     Some (fto ((otf z - otf z') / (otf e - otf e'))). *)

(*   Definition KeyGen (w : choiceWitness) := fto (g ^+ w). *)

(* End MyAlg. *)


(* #[local] Open Scope package_scope. *)

(* Module Sigma := SigmaProtocol MyParam MyAlg. *)

(* Import MyParam MyAlg Sigma. *)
