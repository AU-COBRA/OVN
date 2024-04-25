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

Module Type GroupOperationProperties.
  Axiom add_sub_cancel : forall a b, f_add a (f_sub b a) ≈both b.
  Axiom add_sub_cancel2 : forall a b, f_add (f_sub b a) a ≈both b.
  (* Definition hacspec_group_type : Type := (Choice.sort (chElement f_group_type)). *)
  Axiom prod_pow_add_mul : forall x y z, f_prod (f_g_pow x) (f_pow (f_g_pow z) y) ≈both f_g_pow (f_add x (f_mul z y)).
  Axiom prod_pow_pow : forall h x a b, f_prod (f_pow h x) (f_pow (f_pow h a) b) ≈both f_pow h (f_add x (f_mul a b)).
  Axiom div_prod_cancel : forall x y, f_div (f_prod x y) y ≈both x.

  Axiom mul_comm : forall x y, f_mul x y ≈both f_mul y x.

  (* HB.instance Definition sort_group : hasChoice (Choice.sort (chElement f_group_type)) := _. (* Choice.clone (Choice.sort (chElement f_group_type)) _.  *) *)

  Axiom both_f_group_type_choice : hasChoice.axioms_ (both f_group_type).
  Axiom both_f_group_type_countable : Choice_isCountable (both f_group_type).
  Axiom both_f_group_type_hasDecEq : hasDecEq (both f_group_type).
  Axiom both_f_group_type_isFinite : isFinite.axioms_ (both f_group_type) both_f_group_type_hasDecEq.
  Definition both_f_group_type_Finite : Finite (both f_group_type) :=
    {|
      Finite.choice_hasChoice_mixin := both_f_group_type_choice;
      Finite.choice_Choice_isCountable_mixin := both_f_group_type_countable;
      Finite.eqtype_hasDecEq_mixin := both_f_group_type_hasDecEq;
      Finite.fintype_isFinite_mixin := both_f_group_type_isFinite
    |}.

  Axiom f_group_type_countable : Choice_isCountable (Choice.sort (chElement f_group_type)).
  Axiom f_group_type_isFinite : isFinite (Choice.sort (chElement f_group_type)).
  Definition f_group_type_Finite : Finite (Choice.sort (chElement f_group_type)) :=
    {|
      Finite.choice_hasChoice_mixin := Choice.choice_hasChoice_mixin (Choice.class f_group_type);
      Finite.choice_Choice_isCountable_mixin := f_group_type_countable;
      Finite.eqtype_hasDecEq_mixin := Choice.eqtype_hasDecEq_mixin (Choice.class f_group_type);
      Finite.fintype_isFinite_mixin := f_group_type_isFinite
    |}.

  Axiom both_f_field_type_choice : hasChoice.axioms_ (both f_field_type).
  Axiom both_f_field_type_countable : Choice_isCountable (both f_field_type).
  Axiom both_f_field_type_hasDecEq : hasDecEq (both f_field_type).
  Axiom both_f_field_type_isFinite : isFinite.axioms_ (both f_field_type) both_f_field_type_hasDecEq.
  Definition both_f_field_type_Finite : Finite (both f_field_type) :=
    {|
      Finite.choice_hasChoice_mixin := both_f_field_type_choice;
      Finite.choice_Choice_isCountable_mixin := both_f_field_type_countable;
      Finite.eqtype_hasDecEq_mixin := both_f_field_type_hasDecEq;
      Finite.fintype_isFinite_mixin := both_f_field_type_isFinite
    |}.

  Axiom f_field_type_countable : Choice_isCountable (Choice.sort (chElement f_field_type)).
  Axiom f_field_type_isFinite : isFinite (Choice.sort (chElement f_field_type)).
  Definition f_field_type_Finite : Finite (Choice.sort (chElement f_field_type)) :=
    {|
      Finite.choice_hasChoice_mixin := Choice.choice_hasChoice_mixin (Choice.class f_field_type);
      Finite.choice_Choice_isCountable_mixin := f_field_type_countable;
      Finite.eqtype_hasDecEq_mixin := Choice.eqtype_hasDecEq_mixin (Choice.class f_field_type);
      Finite.fintype_isFinite_mixin := f_field_type_isFinite
    |}.

  
  Definition both_f_field_finType : finType := Finite.Pack both_f_field_type_Finite.
  Definition both_f_group_finType : finType := Finite.Pack both_f_group_type_Finite.

  Definition f_field_finType : finType := Finite.Pack f_field_type_Finite.
  Definition f_group_finType : finType := Finite.Pack f_group_type_Finite.

End GroupOperationProperties.

Module OVN_proofs (group_properties : GroupOperationProperties).
  Include group_properties.

  (* Commitments compute correctly *)
  Lemma commitment_correct : forall x, (check_commitment x (commit_to x)) ≈both ret_both (true : 'bool).
  Proof.
    intros.
    apply both_equivalence_is_pure_eq.
    apply eqb_refl.
  Qed.

  Infix "f+" := (f_add) (at level 77).
  Infix "f-" := (f_sub) (at level 77).
  Infix "f*" := f_mul (at level 77).
  Notation "'<$-'" := (f_random_field_elem) (at level 77).

  Infix "g*" := f_prod (at level 77).
  Notation "'g_g^'" := (f_g_pow) (at level 77).
  Infix "g^" := (f_pow) (at level 77).
  Infix "g/" := (f_div) (at level 77).

  Notation "'vec_from_list' l" :=
    (impl__into_vec
      (unsize
         (box_new
            (array_from_list l) ) )) (at level 77).

  Lemma if_eta : forall {A B} (a : bool) (b c : A) (f : A -> B),
      f (if a then b else c) = if a then f b else f c.
  Proof. now destruct a. Qed.

  Lemma if_pure_eta : forall {A} (a : bool) (b c : both A),
      is_pure (if a then b else c) = is_pure (if a then ret_both (is_pure b) else ret_both (is_pure c)).
  Proof. now destruct a. Qed.

  Lemma bind_both_assoc :
    forall {A B C} (v : both A) (f : A -> both B) (g : B -> both C),
      bind_both (bind_both v f) g ≈both
        bind_both v (fun x => bind_both (f x) g).
  Proof. by now intros ; apply both_equivalence_is_pure_eq. Qed.

  Lemma prod_both_pure_eta_11 : forall {A B C D E F G H I J K} (a : both A) (b : both B) (c : both C) (d : both D) (e : both E) (f : both F) (g : both G) (h : both H) (i : both I) (j : both J) (k : both K), 
                 ((is_pure (both_prog a) : A,
                   is_pure (both_prog b) : B,
                   is_pure (both_prog c) : C,
                   is_pure (both_prog d) : D,
                   is_pure (both_prog e) : E,
                   is_pure (both_prog f) : F,
                   is_pure (both_prog g) : G,
                   is_pure (both_prog h) : H,
                   is_pure (both_prog i) : I,
                   is_pure (both_prog j) : J,
                   is_pure (both_prog k) : K)) =
                   is_pure (both_prog (prod_b( a , b, c, d, e, f, g, h, i, j, k ))).
  Proof. reflexivity. Qed.

  (* Infix "f+" := (f_add) (at level 77). *)
  (* Infix "f-" := (f_sub) (at level 77). *)
  (* Infix "f*" := f_mul (at level 77). *)
  (* Notation "'<$-'" := (f_random_field_elem) (at level 77). *)

  (* Infix "g*" := f_prod (at level 77). *)
  (* Notation "'g_g^'" := (f_g_pow) (at level 77). *)
  (* Infix "g^" := (f_pow) (at level 77). *)
  (* Infix "g/" := (f_div) (at level 77). *)

  Ltac get_both_sides H_lhs H_rhs :=
    match goal with
    | [ |- context [?lhs ≈both ?rhs ] ] =>
        set (H_lhs := lhs) at 1 ;
        set (H_rhs := rhs) at 1
    | [ |- context [?lhs = ?rhs ] ] =>
        set (H_lhs := lhs) at 1 ;
        set (H_rhs := rhs) at 1
   end.

  Ltac apply_to_pure_sides H H_lhs H_rhs :=
    match goal with
    | [ |- context [ _ ≈both _ ] ] =>
        rewrite both_equivalence_is_pure_eq ;
        get_both_sides H_lhs H_rhs ;
        H ;
        rewrite <- both_equivalence_is_pure_eq
    | [ |- context [ _ = _ ] ] =>
        get_both_sides H_lhs H_rhs ;
        H
   end.

  Ltac push_down :=
    match goal with
    | H := is_pure (both_prog (?f (ret_both (is_pure (both_prog ?a))) (ret_both (is_pure (both_prog ?b))))) : _ |- _  =>
      subst H ;
      set (is_pure a) ;
      push_down ;
      set (is_pure b) ;
      push_down
    | H := is_pure (both_prog (?f ?a ?b)) |- _  =>
      subst H ;
      rewrite (hacspec_function_guarantees2 f a b) ;
      set (is_pure a) ;
      push_down ;
      set (is_pure b) ;
      push_down
    | H := is_pure (both_prog (?f (ret_both (is_pure (both_prog ?a))))) : _ |- _  =>
      subst H ;
      set (is_pure a) ;
      push_down
    | H := is_pure (both_prog (?f ?a)) : _ |- _  =>
      subst H ;
      rewrite (hacspec_function_guarantees f a) ;
      set (is_pure a) ;
      push_down
   | H : _ |- _ => subst H
    end ; simpl.

   Ltac pull_up_assert :=
     match goal with
    | |- is_pure (both_prog (?f
        (ret_both (is_pure (both_prog ?a)))
        (ret_both (is_pure (both_prog ?b))))) = _ =>
        let H_a := fresh in
        let H_b := fresh in
        eassert (H_a : (is_pure a) = _) ;
        [ |
          eassert (H_b : (is_pure b) = _) ;
          [ | rewrite H_a ; rewrite H_b ; rewrite <- (hacspec_function_guarantees2 f) ; reflexivity ]
          ]
   | |- is_pure (both_prog (?f (ret_both (is_pure (both_prog ?a))))) = _ =>
       let H_a := fresh in
       eassert (H_a : (is_pure a) = _) ;
       [ | rewrite H_a ; rewrite <- (hacspec_function_guarantees f) ; reflexivity ]
    end.

   Ltac pull_up H :=
     let H_rewrite := fresh in
     eassert (H_rewrite : H = _) by repeat (pull_up_assert ; reflexivity) ; rewrite H_rewrite ; clear H_rewrite.

   Ltac pull_up_side H :=
     let H_rewrite := fresh in
     eassert (H_rewrite : H = _) ; subst H ; [ repeat pull_up_assert ; reflexivity | ] ; rewrite H_rewrite ; clear H_rewrite.

  Ltac remove_solve_lift :=
    repeat progress (rewrite (hacspec_function_guarantees2 _ (solve_lift _)) ; simpl) ;
    repeat progress (rewrite (hacspec_function_guarantees2 _ _ (solve_lift _)) ; simpl) ;
    repeat progress (rewrite (hacspec_function_guarantees _ (solve_lift _)) ; simpl).

  Ltac normalize_lhs :=
    let H_lhs := fresh in
    let H_rhs := fresh in
    get_both_sides H_lhs H_rhs ; subst H_rhs ;
    push_down ; simpl ;
    remove_solve_lift ; simpl ;
    get_both_sides H_lhs H_rhs ; subst H_rhs ;
    pull_up_side H_lhs.

  Ltac normalize_rhs :=
    let H_lhs := fresh in
    let H_rhs := fresh in
    get_both_sides H_lhs H_rhs ; subst H_lhs ;
    push_down ; simpl ;
    remove_solve_lift ; simpl ;
    get_both_sides H_lhs H_rhs ; subst H_lhs ;
    pull_up_side H_rhs.
 
  Ltac normalize_equation :=
    normalize_lhs ; normalize_rhs.
  (* Ltac compute_normal_form := *)
  (*   push_computation_down; simpl ; *)
  (*   rewrite both_equivalence_is_pure_eq ; *)
  (*   push_computation_up ; *)
  (*   rewrite <- both_equivalence_is_pure_eq. *)

  Ltac cancel_operations :=
    try apply both_eq_fun_ext ; 
      try apply both_eq_fun_ext2 ;
      try (eapply both_eq_trans ; [ | apply both_eq_symmetry ; apply prod_pow_add_mul ]) ; 
      try (eapply both_eq_trans ; [ | apply both_eq_symmetry ; apply add_sub_cancel ]) ;
      try (eapply both_eq_trans ; [ | apply both_eq_symmetry ; apply add_sub_cancel2 ]) ;
      try (eapply both_eq_trans ; [ | apply both_eq_symmetry ; apply prod_pow_pow ]) ;
      try (eapply both_eq_trans ; [ | apply both_eq_symmetry ; apply div_prod_cancel ]).
  
  Lemma zkp_one_out_of_two_correct :
    forall x y z h j b, zkp_one_out_of_two_validate h (zkp_one_out_of_two x y z h j b) ≈both ret_both (true : 'bool).
  Proof.
    intros.
    
    rewrite (both_equivalence_is_pure_eq).
    rewrite hacspec_function_guarantees.

      rewrite zkp_one_out_of_two_equation_1 .
      repeat unfold let_both at 1.
      unfold lift_both ; simpl ret_both.

      do 4 rewrite if_eta ; simpl ret_both.

      do 2 unfold Build_t_OrZKPCommit at 1.
      simpl ret_both.
      do 2 rewrite prod_both_pure_eta_11.

      do 4 rewrite <- if_eta.
      rewrite if_pure_eta.
      repeat unfold prod_both at 1 ; simpl ret_both.

    rewrite <- hacspec_function_guarantees.
    rewrite <- both_equivalence_is_pure_eq.
    
    set (if _ then _ else _).
    rewrite zkp_one_out_of_two_validate_equation_1.

    eapply both_eq_trans ; [ apply both_eq_let_both | ].
    eapply both_eq_trans ; [ apply both_eq_solve_lift | ].

    eapply both_eq_trans ;
      [ apply both_eq_andb_true ; eapply both_eq_trans ;
        [ apply both_eq_andb_true ; eapply both_eq_trans ; [
            apply both_eq_andb_true ; eapply both_eq_trans ; [ apply both_eq_andb_true | .. ] | .. ] | .. ]|  ].
   
    all: try rewrite <- both_eq_eqb_true ; try now apply both_eq_reflexivity.
    all: destruct (is_pure b).

    all: subst y0 ;
      repeat try unfold f_or_zkp_a1 at 1 ;
      repeat try unfold f_or_zkp_a2 at 1 ;
      repeat try unfold f_or_zkp_b1 at 1 ;
      repeat try unfold f_or_zkp_b2 at 1 ;
      repeat try unfold f_or_zkp_d1 at 1 ;
      repeat try unfold f_or_zkp_d2 at 1 ;
      repeat try unfold f_or_zkp_r1 at 1 ;
      repeat try unfold f_or_zkp_r2 at 1 ;
      repeat try unfold f_or_zkp_x at 1 ;
      repeat try unfold f_or_zkp_y at 1.
    all: simpl.
    all: try rewrite !bind_ret_both ; simpl.
    all: simpl.

    (* Remove is_pure in the start of expressions *)
    all: try (eapply both_eq_trans ; [ apply both_eq_symmetry ; apply ret_both_is_pure_cancel | ]).
    all: try (eapply both_eq_trans ; [ | apply ret_both_is_pure_cancel]).

    all: try now (rewrite both_equivalence_is_pure_eq;
        normalize_equation;
        rewrite <- both_equivalence_is_pure_eq;
        repeat cancel_operations; apply both_eq_reflexivity).
   
    -  eapply both_eq_trans ; [ | apply both_eq_symmetry ; apply (proj2 both_equivalence_is_pure_eq (hacspec_function_guarantees2 f_add _ _)) ].

     
      set (add_cancel := add_sub_cancel). simpl ; eapply both_eq_trans ; [ | apply (proj2 both_equivalence_is_pure_eq (hacspec_function_guarantees2 f_add _ _)) ] ; eapply both_eq_trans ; [ | apply both_eq_symmetry ; apply add_cancel ] ; do 4 apply both_eq_fun_ext ; now apply both_equivalence_is_pure_eq.

  all: try now (rewrite both_equivalence_is_pure_eq;
        normalize_equation;
        rewrite <- both_equivalence_is_pure_eq;
        repeat cancel_operations; apply both_eq_reflexivity).

  - rewrite both_equivalence_is_pure_eq.

    normalize_lhs.
    normalize_rhs.

    normalize_equation.
    rewrite <- both_equivalence_is_pure_eq.

    repeat cancel_operations.
    now apply both_equivalence_is_pure_eq.
  - rewrite both_equivalence_is_pure_eq.
    do 2 normalize_equation.
    rewrite <- both_equivalence_is_pure_eq.

    eapply both_eq_trans.
    2:{
      apply both_eq_symmetry.
      let H_in := fresh in
      set (H_in := f_prod _ _) ; pattern (f_div (((f_pow h j) g* (f_g))) f_g) in H_in ; subst H_in.
      apply both_eq_fun_ext.
      apply div_prod_cancel.
    }

    repeat cancel_operations ; apply both_eq_reflexivity.
  Admitted. (* (* Slow *) Qed. *)

  Lemma prod_both_pure_eta_3 : forall {A B C} (a : both A) (b : both B) (c : both C), 
                 ((is_pure (both_prog a) : A,
                   is_pure (both_prog b) : B,
                   is_pure (both_prog c) : C)) =
                   is_pure (both_prog (prod_b( a , b, c ))).
  Proof. reflexivity. Qed.

  Lemma schnorr_zkp_correct :
    forall r x, schnorr_zkp_validate (g_g^ x) (schnorr_zkp r (g_g^ x) x) ≈both ret_both (true : 'bool).
  Proof.
    intros.
    
    (* Unfold definition *)
    rewrite (both_equivalence_is_pure_eq).
    rewrite hacspec_function_guarantees.

      rewrite schnorr_zkp_equation_1 .
      repeat unfold let_both at 1.
      unfold lift_both ; simpl ret_both.

      unfold Build_t_SchnorrZKPCommit at 1.
      simpl ret_both.
      repeat unfold prod_both at 1 ; simpl ret_both.

      unfold run at 1.
      simpl ret_both.

      unfold f_from_residual at 1.
      simpl ret_both.
      unfold lift1_both at 1.
      simpl ret_both.

      rewrite prod_both_pure_eta_3.
      rewrite (hacspec_function_guarantees2 prod_both).

    rewrite <- hacspec_function_guarantees.
    rewrite <- both_equivalence_is_pure_eq.
    
    repeat unfold prod_both at 1 ; rewrite !bind_ret_both ; simpl.
     set (_, _, _).
        
    (* unfold definition *)
    rewrite schnorr_zkp_validate_equation_1 .
 
    eapply both_eq_trans ; [ apply both_eq_solve_lift | ].

    eapply both_eq_trans ;
      [ apply both_eq_andb_true |  ].

    all: try rewrite <- both_eq_eqb_true ; try now apply both_eq_reflexivity.

    all: subst p;
      try repeat unfold f_schnorr_zkp_c at 1 ;
      try repeat unfold f_schnorr_zkp_u at 1 ;
      try repeat unfold f_schnorr_zkp_z at 1 ;
      simpl ; try rewrite !bind_ret_both ; simpl.
    all: rewrite both_equivalence_is_pure_eq ;
      normalize_equation ;
      rewrite <- both_equivalence_is_pure_eq.
    
  {
    repeat cancel_operations.
    now apply both_equivalence_is_pure_eq.
  }
  {
    try (eapply both_eq_trans ; [ | apply both_eq_symmetry ; apply prod_pow_add_mul ]) ; 
      try (eapply both_eq_trans ; [ | apply both_eq_symmetry ; apply add_sub_cancel ]) ;
      try (eapply both_eq_trans ; [ | apply both_eq_symmetry ; apply add_sub_cancel2 ]) ;
      try (eapply both_eq_trans ; [ | apply both_eq_symmetry ; apply prod_pow_pow ]) ;
      try (eapply both_eq_trans ; [ | apply both_eq_symmetry ; apply div_prod_cancel ]).

    apply both_eq_fun_ext.
    apply both_eq_fun_ext.

    apply mul_comm.
  }
  Qed.

  Require Import mathcomp.algebra.ssralg.

  Module HacspecGroup.
 
    
    (* both f_field_type is a field *)
    (* ChoiceEquality_both__canonical__GRing_Field *)
    Axiom f_field_type_Field : GRing.Field (f_field_type). 

    Definition lower1 {A B : choice_type} (f : both A -> both B) : A -> B :=
      fun x => is_pure (f (ret_both x)).

    Definition lower2 {A B C : choice_type} (f : both A -> both B -> both C) : A -> B -> C :=
      fun x y => is_pure (f (ret_both x) (ret_both y)).
    
    Axiom f_prodA : associative (lower2 f_prod).
    Axiom f_prod1 : associative (lower2 f_prod).
    Axiom f_prod_left_id : left_id (is_pure f_group_one) (lower2 f_prod).
    Axiom f_invK : involutive (lower1 f_inv).
    Axiom f_invM : {morph (lower1 f_inv)  : x y / (lower2 f_prod) x y >-> (lower2 f_prod)  y x}.
    Definition mul_group : isMulBaseGroup (f_group_type) :=
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

    #[export] Definition f_group_type_BaseFinGroup : baseFinGroupType :=
      BaseFinGroup.Pack
        {|
          BaseFinGroup.fingroup_isMulBaseGroup_mixin := mul_group;
          BaseFinGroup.choice_hasChoice_mixin := f_group_type_Finite;
          BaseFinGroup.choice_Choice_isCountable_mixin := f_group_type_Finite;
          BaseFinGroup.eqtype_hasDecEq_mixin := f_group_type_Finite;
        BaseFinGroup.fintype_isFinite_mixin := f_group_type_Finite
      |}.
    #[export] Lemma inv_mul_inverse : left_inverse (T := f_group_type_BaseFinGroup) (R := f_group_type) (oneg f_group_type_BaseFinGroup) invg mulg.
    Proof.
      unfold invg, mulg ; change 1%g with (is_pure f_group_one) ; simpl.
      intros x.
      unfold lower1, lower2.
      rewrite hacspec_function_guarantees ; rewrite <- hacspec_function_guarantees2.
      rewrite <- (both_equivalence_is_pure_eq).
      apply prod_inv_cancel.
    Qed.

    Definition f_group_type_is_group : finGroupType :=
      FinGroup.Pack
        {| FinGroup.fingroup_BaseFinGroup_isGroup_mixin :=
            {| BaseFinGroup_isGroup.mulVg_subproof := inv_mul_inverse |} |}.
  End HacspecGroup.

  From mathcomp Require Import zmodp.
 
  Module HacspecGP : GroupParam.
    Include HacspecGroup.
    
    Definition gT : finGroupType := f_group_type_is_group.
    Definition ζ : {set gT} := [set : gT].
    Definition g :  gT := is_pure f_g.

    Open Scope ring_scope.

    (* Definition field_element_is_iterated_add_of_generator : *)

    Theorem field_elem_is_mul_one :
      forall {F : ringType} (i : nat), exists (x : F), x = (1%:R *+ i).
    Proof.
      by intros ; exists i%:R.
      (* rewrite <- GRing.mulr_natr ; rewrite GRing.mul1r. *)
    Qed.

    Close Scope ring_scope.

    Open Scope group_scope.
    Theorem group_elem_is_exp_generator :
      forall {G : finGroupType} (i : nat), exists (x g : G), x = (expgn g i).
    Proof.
      intros.
      induction i.
      - exists 1, 1. reflexivity.
      - destruct IHi as [x [g ?]].
        exists (x * g), g.
        now rewrite H expgSr.
    Qed.

    (* cycleP *)
    Lemma group_element_is_iterated_mul_of_generator :
      forall (x : both f_group_type), exists (y : both f_field_type), x = f_g_pow y.
    Proof.
    Admitted.

    Lemma expgn_rec_is_f_g_pow :
      forall i, expgn_rec (T:=gT) (is_pure f_g) i = is_pure (f_g_pow (iterop i f_add f_field_one f_field_zero)).
    Proof.
      intros.
      unfold expgn_rec.
      induction i.
      - simpl.
    Admitted.        
    
    Lemma element_is_iterated_mul_of_generator :
      forall (x : gT), exists (i : nat), x = expgn_rec (T:=gT) (is_pure f_g) i.
    Proof.
      intros.
      pose (@cycleP gT x (is_pure f_g)).
      
      epose (group_elem_is_exp_generator 1).
      
    Admitted.      
    
    Lemma g_gen : ζ = <[g]>.
    Proof.
      intros.

      unfold ζ, g.
      apply/setP=> x.
      rewrite inE.

      (* rewrite (ssrbool.introT (cycleP _ _) _) ; [ reflexivity | ]. *)
      destruct (element_is_iterated_mul_of_generator x) as [y H].
      rewrite H ; clear H.
      now rewrite (mem_cycle (is_pure f_g : gT)).
    Qed.

    Lemma prime_order : prime #[g].
    Proof.
      unfold g.
    Admitted.

  End HacspecGP.

  From Crypt Require Import Schnorr SigmaProtocol.

  Module HacspecScnorr := Schnorr HacspecGP.

  Import HacspecScnorr.
  Import MyParam MyAlg Sigma.

  #[local] Open Scope package_scope.
  Import GroupScope GRing.Theory.

  (* Main theorem. *)
  (* Proves that Schnorr is a ∑-protocol with perfect special honest-verifier
  zero-knowledge *)
  Theorem schnorr_SHVZK :
    forall LA A,
      ValidPackage LA [interface
                         #val #[ TRANSCRIPT ] : chInput → chTranscript
        ] A_export A ->
      fdisjoint LA Sigma_locs ->
      ɛ_SHVZK A = (@GRing.zero (reals.Real.Exports.reals_Real__to__GRing_Nmodule Axioms.R)).
  Proof.
    intros LA A Va Hdisj.
    apply: eq_rel_perf_ind.
    all: ssprove_valid.
    3: apply fdisjoints0.
    1:{ instantiate (1 := heap_ignore Sigma_locs).
        ssprove_invariant.
        apply fsubsetUl. }
    simplify_eq_rel hwe.
    (* Programming logic part *)
    destruct hwe as [[h w] e].
    (* We can only simulate if the relation is valid *)
    ssprove_sync_eq. intros rel.
    (* When relation holds we can reconstruct the first message from the response *)
    unfold R in rel. apply reflection_nonsense in rel.
    eapply r_uniform_bij with (1 := bij_f (otf w) (otf e)). intros z_val.
    ssprove_contract_put_get_lhs.
    apply r_put_lhs.
    ssprove_restore_pre.
    1: ssprove_invariant.
    apply r_ret.
    (* Ambient logic proof of post condition *)
    intros s₀ s₁ Hs.
    unfold f.
    rewrite rel.
    split.
    2: apply Hs.
    simpl.
    rewrite otf_fto expg_mod.
    2: rewrite order_ge1 ; apply expg_order.
    rewrite expgD - !expgVn.
    rewrite group_prodC group_prodA group_prodC group_prodA /=.
    rewrite expg_mod.
    2: rewrite order_ge1 ; apply expg_order.
    rewrite -expgM -expgMn.
    2: apply group_prodC.
    rewrite mulgV expg1n mul1g.
    cbn. rewrite Zp_mulC.
    reflexivity.
  Qed.


















  
















  
















  
















  
















  
















  
















  
















  
















  
















  
  From Crypt Require Import pkg_notation.
  Include PackageNotation.
  Open Scope package_scope. 
  (* Definition choiceTranscript := *)
  (*   chProd (chProd (chProd choiceStatement choiceMessage) choiceChallenge) choiceResponse. *)
  
  Definition my_locations : {fset Location} := fset0.

  Import PackageNotation.
  Open Scope package_scope.

  Locate HacspecScnorr.Sigma.witness.
  Program Definition chRelation : choice_type := chProd f_group_type f_field_type.
  Admit Obligations.
  
  Import Misc.

  Definition chTranscript : choice_type := t_SchnorrZKPCommit.
  Check chTranscript.
  Locate "#val  #[ f ]  :  A  →  B".

  Definition my_raw hw :=
    let '(h,w) := hw in
    ((r ← sample uniform (Z.to_nat (modulus 32)).-1.+1 ;;
             is_state (schnorr_zkp (ret_both (finite_to_word r : uint32)) (ret_both h) (ret_both w)))
             : raw_code t_SchnorrZKPCommit).
  
  #[tactic=notac] Program Definition mypkg :
      package my_locations
        [interface]
        (fset [(pair HacspecScnorr.Sigma.RUN
                  (chRelation, chTranscript));
               (pair HacspecScnorr.Sigma.VERIFY
                  (chTranscript,
                    'bool))]
        ) :=
    (mkpackage (fmap.mkfmap [
                    (HacspecScnorr.Sigma.RUN,
                      (chRelation;
                       chTranscript;
                       _ ));
                    (HacspecScnorr.Sigma.VERIFY,
                      (chTranscript;
                       'bool;
                       fun _ => ret (false : 'bool)))
       ]) _).
  Next Obligation.
    refine (fun hw => my_raw hw).
  Defined.
  Next Obligation.
    unfold my_locations.
    rewrite fset0E.

    apply valid_package_cons. 
    {
      apply valid_package1.
      intros.

      ssprove_valid.
    }
    
    {
      intros [].
      apply valid_scheme.
      unfold mypkg_obligation_1.
      unfold my_raw.
      
      ssprove_valid.
      rewrite <- fset0E.
      apply (is_valid_code (both_prog_valid (schnorr_zkp _ _ _))).
    }

    {
      rewrite <- fset1E.
      rewrite imfset1.
      easy.
    }    
  Defined.

  Print mypkg.
  Include HacspecGroup.
  Import PackageNotation.

  Check (pkg_composition.link HacspecScnorr.Sigma.Fiat_Shamir HacspecScnorr.Sigma.Oracle.RO).
  
 (* Lemma proving that the output of the extractor defined for Schnorr's
  protocol is perfectly indistinguishable from real protocol execution.
  *)
  (* Definition chSoundness := (chProd _ (chProd _ (chProd _ _))). *)

  From Crypt Require Import SigmaProtocol.
  
  Goal forall LA A,
      ValidPackage LA (fset []) (fset [(pair HacspecScnorr.Sigma.RUN (chRelation, chTranscript));
                             (pair HacspecScnorr.Sigma.VERIFY (chTranscript, 'bool))]) A ->
           fdisjoint LA my_locations ->
      fdisjoint my_locations HacspecScnorr.Sigma.Oracle.RO_locs ->
      HacspecScnorr.Sigma.ɛ_hiding A = (@GRing.zero (reals.Real.Exports.reals_Real__to__GRing_Nmodule Axioms.R)).
    intros.
    unfold HacspecScnorr.Sigma.ɛ_hiding.

    eapply eq_rel_perf_ind_ignore.
    all: ssprove_valid.
    - admit.
    - admit.
    -  admit.
    - simplify_eq_rel hw.
 
  Qed.
  
Lemma extractor_success:
  forall LA A,
    ValidPackage LA (fset [(pair HacspecScnorr.Sigma.RUN (chRelation, chTranscript));
        (pair HacspecScnorr.Sigma.VERIFY (chTranscript, 'bool))]) A_export A ->
    ɛ_soundness A = 0.

  Lemma some :
    ValidPackage LA [interface
      #val #[ TRANSCRIPT ] : chInput → chTranscript
    ] A_export A →
    fdisjoint LA Sigma_locs →
    ɛ_SHVZK A = 0.

  Lemma test :
    forall LA A,
      ValidPackage LA (fset [(pair HacspecScnorr.Sigma.RUN (chRelation, chTranscript));
        (pair HacspecScnorr.Sigma.VERIFY (chTranscript, 'bool))]) A_export A ->
      fdisjoint LA my_locations ->
      fdisjoint my_locations HacspecScnorr.Sigma.Oracle.RO_locs ->
      AdvantageE
        mypkg
        (pkg_composition.link HacspecScnorr.Sigma.Fiat_Shamir HacspecScnorr.Sigma.Oracle.RO)
        A = (@GRing.zero (reals.Real.Exports.reals_Real__to__GRing_Nmodule Axioms.R)).
  Proof.
    intros LA A Va Hdisj Hdisj_oracle.
    eapply eq_rel_perf_ind_ignore.
    6: apply Hdisj.
    6: apply Hdisj.
    5: apply Va.
    - ssprove_valid.
    - admit.
    - admit.      
    - unfold mypkg.
      unfold mypkg_obligation_1.
      unfold my_raw.
      
      simplify_eq_rel hw.
      ssprove_code_simpl.
      destruct hw as [h w].
      ssprove_sync. intros rel.
      eapply rsame_head_alt.
      1: exact _.
      1:{
        intros l Il.
        apply get_pre_cond_heap_ignore.
        revert l Il.
        apply /fdisjointP.
        assumption.
      }
      1:{ intros. apply put_pre_cond_heap_ignore. }
      intros [a st].
      ssprove_contract_put_get_lhs.
      rewrite emptymE.
      apply r_put_lhs.
      ssprove_sync. intro e.
      apply r_put_lhs.
      ssprove_restore_pre. 1: ssprove_invariant.
      eapply r_reflexivity_alt.
      - exact _.
      - intros l Il.
        ssprove_invariant.
        revert l Il.
        apply /fdisjointP. assumption.
      - intros. ssprove_invariant.

      
  Definition test :
    HacspecScnorr.Sigma.fiat_shamir_correct _ _ _ _ _.
  
  Check SiSigmaProtocol.Fiat_Shamir.
 


  
  Require Import mathcomp.algebra.ssralg.
  Open Scope group_scope.

  Module MyParam <: SigmaProtocolParams.
    Include HacspecGroup.
    Include Misc.
    
    Definition Witness : finType := Finite.Pack (word32_Finite 32).
    Locate HacspecGP.f_group_type_is_group.
    Check HacspecGP.gT.
    Definition Statement : finType := f_group_type_is_group.
    Definition Message : finType := 
      (Datatypes_prod__canonical__fintype_Finite
         (Datatypes_prod__canonical__fintype_Finite f_group_type_is_group f_group_type_is_group)
         f_group_type_is_group).
    Definition Challenge : finType := f_field_finType.
    Definition Response : finType :=  f_field_finType.
    Definition Transcript : finType :=
      prod (prod Message Challenge) Response.

    Definition w0 : Witness := mkword _ 0 .
    Definition e0 : Challenge := is_pure f_field_zero.
    Definition z0 : Response := is_pure f_field_zero.

    Definition R : Statement -> Witness -> bool :=
      (fun (h : Statement) (w : Witness) => h == ((is_pure f_g : f_group_type_is_group) ^+ w : f_group_type_is_group)).

    #[export] Instance positive_gT : Positive #|f_group_finType|.
    Proof.
      apply /card_gt0P. exists (is_pure f_g). auto.
    Qed.

    #[export] Instance positive_fT : Positive #|f_field_finType|.
    Proof.
      apply /card_gt0P. exists (is_pure f_field_zero). auto.
    Qed.

    #[export] Instance Witness_pos : Positive #|Witness|.
    Proof.
      apply /card_gt0P. exists (mkword _ 0). auto.
    Defined.

    Definition Statement_pos : Positive #|Statement| := _.
    #[export] Definition Message_pos : Positive #|Message|.
    Proof.
      rewrite !card_prod. repeat apply Positive_prod ; apply positive_gT.
    Defined.
    Definition Challenge_pos : Positive #|Challenge| := _.
    Definition Response_pos : Positive #|Response| := _.
    Definition Bool_pos : Positive #|'bool|.
    Proof.
      rewrite card_bool. done.
    Defined.

  End MyParam.


  
  From Crypt Require Import SigmaProtocol. 
  Module MyAlg <: Oracle. MyParam.

  
  Module MyAlg <: SigmaProtocolAlgorithms MyParam.

    Import MyParam.

    #[local] Existing Instance Bool_pos.

    Definition choiceWitness : choice_type := f_field_type (* 'fin #|Witness| *).
    Definition choiceStatement : choice_type := f_group_type (* 'fin #|Statement| *).
    Definition choiceMessage : choice_type := chProd (chProd f_group_type f_field_type) f_field_type.
    Definition choiceChallenge : choice_type := 'fin #|Challenge|.
    Definition choiceResponse : choice_type := 'fin #|Response|.
    Definition choiceTranscript : choice_type :=
      chProd
        (chProd (chProd choiceStatement choiceMessage) choiceChallenge)
        choiceResponse.
    Definition choiceBool := 'fin #|'bool|.

    Definition i_witness := (* #|Witness| *) (Z.to_nat (modulus 32)).-1.+1.

    Definition HIDING : nat := 0.
    Definition SOUNDNESS : nat := 1.

    Definition commit_loc : Location := (int32; 2%nat).
    
    Definition Sigma_locs : {fset Location} := fset [:: commit_loc].
    Definition Simulator_locs : {fset Location} := fset0.

    (* schnorr_zkp_validate (g_g^ x) (schnorr_zkp r (g_g^ x) x) *)
    Obligation Tactic := try timeout 1 intros.
    Program Definition Commit (h : choiceStatement) (w : choiceWitness):
      code Sigma_locs [interface] choiceMessage :=
      {code
         r ← sample uniform i_witness ;;
         #put commit_loc := (finite_to_word (n := 32) r : int32) ;;
         is_state (schnorr_zkp (ret_both (finite_to_word (n := 32) r)) (ret_both ( h)) (ret_both w))
      }.
    Next Obligation.
      ssprove_valid.
      epose (is_valid_code (both_prog_valid (schnorr_zkp _ _ _))).
      ssprove_valid.
      apply valid_scheme.
      rewrite <- fset0E.
      apply v0.
    Qed.

    Definition Simulate (h : choiceStatement) (e : choiceChallenge) :
      code Simulator_locs [interface] choiceTranscript :=
      {code
         z ← sample uniform i_witness ;;
       ret (h, fto (g ^+ (otf z) * (otf h ^- (otf e))), e, z)
      }.

    Definition Verify (h : choiceStatement) (a : choiceMessage)
      (e : choiceChallenge) (z : choiceResponse) : choiceBool :=
      fto (g ^+ (otf z) == (otf a) * (otf h) ^+ (otf e)).

    Definition Extractor (h : choiceStatement) (a : choiceMessage)
      (e : choiceChallenge) (e' : choiceChallenge)
      (z : choiceResponse)  (z' : choiceResponse) : 'option choiceWitness :=
      Some (fto ((otf z - otf z') / (otf e - otf e'))).

    Definition KeyGen (w : choiceWitness) := fto (g ^+ w).

  End MyAlg.

  #[local] Open Scope package_scope.

  Module Sigma := SigmaProtocol MyParam MyAlg.


  Check HacspecScnorr.schnorr_com_binding. 


  Check HacspecScnorr.schnorr_com_binding.
  
  (* Main theorem *)
  Theorem schnorr_com_binding :
    forall (LA : {fset Location}) (A : raw_package),
       AdvantageE
          schnorr_zkp
          HacspecScnorr.Sigma.Special_Soundness_f A <= 0.
  Proof.
    intros LA A VA Hdisj.
    eapply Order.le_trans.
    1: apply Advantage_triangle.
    instantiate (1 := Special_Soundness_t).
    rewrite (commitment_binding LA A VA Hdisj).
    setoid_rewrite (extractor_success LA A VA).
    now setoid_rewrite GRing.isNmodule.add0r.
  Qed.

  
  (* Module Type HacspecSigmaProtocolParams. *)

End OVN_proofs.

(* Lemma vote_hiding (i j : pid) m: *)
(*   i != j → *)
(*   ∀ LA A ϵ_DDH, *)
(*     ValidPackage LA [interface #val #[ Exec i ] : 'bool → 'public] A_export A → *)
(*     fdisjoint Sigma1.MyAlg.Sigma_locs DDH.DDH_locs → *)
(*     fdisjoint LA DDH.DDH_locs → *)
(*     fdisjoint LA (P_i_locs i) → *)
(*     fdisjoint LA combined_locations → *)
(*     (∀ D, DDH.ϵ_DDH D <= ϵ_DDH) → *)
(*     AdvantageE (Exec_i_realised true m i j) (Exec_i_realised false m i j) A <= ϵ_DDH + ϵ_DDH. *)
a
