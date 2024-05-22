
(*** Example (Z89) *)

(* From OVN Require Import Hacspec_ovn_Ovn_z_89_. *)

(* Module Z89_impl <: HacspecOVNParams. *)
(*   #[local] Open Scope hacspec_scope. *)

(*   Definition v_G : choice_type := t_g_z_89_. *)
(*   Transparent v_G. *)
(*   Hint Unfold v_G. *)

(*   Definition n : both uint_size := ret_both 55. *)

(*   Instance Serializable_chFin (n : positive) : Serializable.Serializable (chFin n). *)
(*   Proof. *)
(*     destruct n as [[] ?] ; [ discriminate | ]. *)
(*     refine (serialize_by_other (fun x => nat_of_ord x) (fun x => inord x) (inord_val)). *)
(*     apply Serializable.nat_serializable. *)
(*   Defined. *)

(*   Instance v_Z_t_Field : t_Field _ := t_z_89__t_Field. *)
(*   (* Instance t_Eq_from_eqType (A : eqType) : t_Eq A := *) *)
(*   (*   {| Hacspec_Lib_Comparable.eqb := fun x y => x == y; eqb_leibniz := fun x y => RelationClasses.symmetry (rwP eqP) |}. *) *)
(*   (* Instance v_G_t_Eq : t_Eq v_G := _. *) *)

(*   Instance v_G_t_Copy : t_Copy v_G := _. *)
(*   Instance v_G_t_PartialEq : t_PartialEq v_G v_G := _. *)
(*   Instance v_G_t_Clone : t_Clone v_G := _. *)
(*   Instance v_G_t_Serialize : t_Serialize v_G := _. *)
(*   Instance v_G_t_Eq : t_Eq v_G := _. *)

(*   Instance v_G_t_Group : t_Group v_G := t_g_z_89__t_Group. *)

(*   Definition v_A : choice_type := 'nat. *)
(*   Instance v_A_t_Sized : t_Sized v_A. Admitted. *)
(*   Definition v_A_t_HasActions : t_HasActions v_A. *)
(*   Proof. *)
(*     constructor. *)
(*     refine (ret_both (0%nat : 'nat)). *)
(*   Defined. *)

(*   Instance f_field_type_Serializable : Serializable.Serializable v_G_t_Group.(f_Z). Admitted. *)
(*   Instance f_group_type_Serializable : Serializable.Serializable v_G. Admitted. *)

(* End Z89_impl. *)

(* Module Z89_group_operations <: GroupOperationProperties Z89_impl. *)
(*   Include Z89_impl. *)

(*   Ltac unfold_both_eq := *)
(*     intros ; *)
(*     apply both_equivalence_is_pure_eq ; *)
(*     cbn ; *)
(*     repeat (try unfold lift2_both at 1 ; try unfold lift1_both at 1 ; simpl). *)

(* (* (a + b) + c = a + (b + c) *) *)

(*   Corollary both_equivalence_bind_comm : forall {A} {a : both A} {b : both A} {f : A -> A -> both A}, *)
(*       bind_both a (fun x => *)
(*       bind_both b (fun y => f x y)) *)
(*         ≈both *)
(*       bind_both b (fun y => bind_both a (fun x => f x y)) *)
(*       . *)
(*   Proof. *)
(*     intros. *)
(*     cbn. *)
(*     unfold both_equivalence. *)
(*     now rewrite <- both_pure. *)
(*   Qed. *)

(*   Lemma f_sub_by_opp : forall x y, f_sub x y ≈both f_add x (f_opp y). *)
(*   Proof. Admitted. *)
(*   (*   intros. *) *)
(*   (*   simpl. *) *)

(*   (*   repeat unfold Build_t_z_89_ at 1. *) *)

(*   (*   repeat unfold f_z_val at 1. *) *)
(*   (*   repeat unfold ".-" at 1. *) *)
(*   (*   repeat unfold ".+" at 1. *) *)
(*   (*   repeat unfold ".%" at 1. *) *)
(*   (*   unfold_both_eq. *) *)

(*   (*   Set Printing Coercions. *) *)

(*   (*   set (x' := is_pure _). *) *)
(*   (*   set (y' := is_pure _). *) *)

(*   (*   set (int_xO _); change (Hacspec_Lib_Pre.int_sub (int_xI s) _) with (@int_xO U8 s); subst s. *) *)
(*   (*   set (n88 := int_xO _). *) *)

(*   (*   replace (wrepr U8 0) with (Hacspec_Lib_Pre.zero (WS := U8)). *) *)
(*   (*   2: admit. *) *)
(*   (*   rewrite add_zero_l. *) *)



(*   (*   rewrite !add_repr. *) *)


(*   (*   replace (Hacspec_Lib_Pre.int_sub 89 1) with *) *)
(*   (*     (88). *) *)

(*   (*   unfold Hacspec_Lib_Pre.int_sub. *) *)
(*   (*   unfold Hacspec_Lib_Pre.int_add. *) *)
(*   (*   unfold Hacspec_Lib_Pre.int_mod. *) *)

(*   (*   (* unfold wrepr. *) *) *)
(*   (*   (* set (unsigned _ mod _) ; fold (wrepr U8 z) ; subst z. *) *) *)
(*   (*   (* set (unsigned _ mod _) at 2 ; fold (wrepr U8 z) ; subst z. *) *) *)

(*   (*   assert (forall x, wrepr U8 (urepr x) = x) by apply ureprK. *) *)

(*   (*   unfold unsigned. *) *)
(*   (*   unfold sub_word. *) *)

(*   (*   (* unfold wrepr. *) *) *)
(*   (*   change (nat_of_wsize U8) with (wsize_size_minus_1 U8).+1. *) *)
(*   (*   set (z := urepr _ - _) ; fold (wrepr U8 z) ; subst z. *) *)
(*   (*   set (z := urepr _ - _) at 2 ; fold (wrepr U8 z) ; subst z. *) *)
(*   (*   set (z := urepr _ - _) at 3 ; fold (wrepr U8 z) ; subst z. *) *)
(*   (*   set (z := urepr _ - _) at 4 ; fold (wrepr U8 z) ; subst z. *) *)
(*   (*   set (z := urepr _ - _) at 5 ; fold (wrepr U8 z) ; subst z. *) *)
(*   (*   set (z := urepr _ - _) at 6 ; fold (wrepr U8 z) ; subst z. *) *)
(*   (*   set (z := urepr _ - _) at 7 ; fold (wrepr U8 z) ; subst z. *) *)

(*   (*   set (int_xO _); change (urepr (int_xI s) - _) with (urepr (@int_xO U8 s)); subst s. *) *)
(*   (*   set (n88 := int_xO _). *) *)

(*   (*   unfold add_word. *) *)
(*   (*   set (z := urepr _ + _) ; fold (wrepr U8 z) ; subst z. *) *)
(*   (*   set (z := urepr _ + _) at 2 ; fold (wrepr U8 z) ; subst z. *) *)
(*   (*   set (z := urepr _ + _) at 3 ; fold (wrepr U8 z) ; subst z. *) *)
(*   (*   rewrite !H. *) *)

(*   (*   rewrite wrepr_add. *) *)
(*   (*   rewrite !H. *) *)

(*   (*   rewrite wrepr_sub. *) *)
(*   (*   rewrite !H. *) *)

(*   (*   set (urepr _). *) *)
(*   (*   set (urepr _). *) *)

(*   (* Admitted. *) *)

(*   Lemma f_addA : forall x y z, f_add x (f_add y z) ≈both f_add (f_add x y) z. *)
(*   Admitted. *)
(*   (* Proof. unfold_both_eq. now rewrite Zp_addA. Qed. *) *)

(*   Lemma f_addC: forall x y, f_add x y ≈both f_add y x. *)
(*   Proof. Admitted. *)
(*     (* Proof. unfold_both_eq. now rewrite Zp_addC. Qed. *) *)
(*   (* Axiom f_mul_addr: right_distributive (f_mul) (f_add). *) *)
(*   (* Axiom f_mul_addl: left_distributive (f_mul) (f_add). *) *)
(*   Lemma f_add0z: forall x, f_add f_field_zero x ≈both x. *)
(*   Proof. Admitted. *)
(*   (* Proof. *) *)
(*   (*   unfold_both_eq. *) *)
(*   (*   replace (inord _) with (Zp0 (p' := 88 (* 89 *))) by now apply ord_inj ; rewrite inordK. *) *)
(*   (*   now rewrite Zp_add0z. *) *)
(*   (* Qed. *) *)

(*   Lemma f_addNz: forall x, f_add (f_opp x) x ≈both f_field_zero. *)
(*   Proof. Admitted. *)
(*   (* Proof. *) *)
(*   (*   unfold_both_eq. *) *)
(*   (*   replace (inord _) with (Zp0 (p' := (* 89 *) 88)) by now apply ord_inj ; rewrite inordK. *) *)
(*   (*   rewrite Zp_add0z. *) *)
(*   (*   now rewrite Zp_addNz. *) *)
(*   (* Qed. *) *)

(*   (* Lemma nat_of_ord_helper : *) *)
(*   (*   (forall (a b : v_G), (nat_of_ord a * nat_of_ord b)%nat = nat_of_ord (a * b)). *) *)
(*   (* Admitted. *) *)

(*   Definition prod_pow_add_mul : ∀ x y z : both f_Z, f_prod (f_g_pow x) (f_pow (f_g_pow z) y) ≈both f_g_pow (f_add x (f_mul z y)). *)
(*   Proof. Admitted. *)
(*   (* Proof. *) *)
(*   (*   unfold_both_eq ; repeat setoid_rewrite <- expgnE. *) *)

(*   (*   (* unfold Zp_mul. *) *) *)
(*   (*   (* rewrite nat_of_ord_helper. *) *) *)

(*   (*   (* rewrite modZp. *) *) *)

(*   (*   unfold expgn at 1, expgn_rec. *) *)
(*   (*   unfold Zp_mul. *) *)
(*   (*   unfold expgn at 1, expgn_rec. *) *)
(*   (* Admitted. *) *)

(*   Definition prod_pow_pow : forall h x a b, f_prod (f_pow h x) (f_pow (f_pow h a) b) ≈both f_pow h (f_add x (f_mul a b)). *)
(*   Proof. Admitted. *)
(*   (*   intros. *) *)
(*   (*   unfold_both_eq ; repeat setoid_rewrite <- expgnE. *) *)
(*   (*   Set Printing Coercions. *) *)
(*   (*   (* unfold Zp_mul. *) *) *)

(*   (*   set (h' := is_pure (both_prog _)). *) *)
(*   (*   set (x' := nat_of_ord _). *) *)
(*   (*   set (a' := nat_of_ord _). *) *)
(*   (*   set (b' := nat_of_ord _). *) *)

(*   (*   unfold Zp_mul. *) *)
(*   (*   rewrite nat_of_ord_helper. *) *)
(*   (*   rewrite valZpK. *) *)

(*   (*   rewrite <- expgM. *) *)
(*   (*   rewrite <- expgD. *) *)

(*   (*   (* f_equal. *) *) *)

(*   (*   rewrite <- modnDm. *) *)
(*   (*   rewrite modn_mod. *) *)
(*   (*   rewrite modnDm. *) *)

(*   (*   rewrite expg_mod ; [reflexivity | ]. *) *)

(*   (*   apply ord_inj. *) *)
(*   (*   simpl. *) *)

(*   (*   destruct h' ; simpl. *) *)
(*   (*   repeat (discriminate || (destruct m as [ | m ] ; [ reflexivity | ])). (* SLOW *) *) *)
(*   (* Qed. *) *)

(*   Definition div_prod_cancel : forall x y, f_div (f_prod x y) y ≈both x. Admitted. *)

(*   Definition mul_comm : forall x y, f_mul x y ≈both f_mul y x. Admitted. *)

(*   (* HB.instance Definition sort_group : hasChoice (Choice.sort (chElement v_G)) := _. (* Choice.clone (Choice.sort (chElement v_G)) _.  *) *) *)

(*   (* HB.instance Definition Choice_choice : Choice v_G := _. *) *)
(*   Definition v_G_countable : Choice_isCountable (Choice.sort (chElement v_G)) := [ Countable of v_G by <: ]. *)
(*   Definition v_G_isFinite : isFinite (Choice.sort (chElement v_G)). *)
(*   Proof. Admitted. *)
(*     (* [ Finite of v_G by <: ]. *) *)

(*   Definition v_Z_countable : Choice_isCountable (Choice.sort (chElement v_G_t_Group.(f_Z))) := [ Countable of v_G_t_Group.(f_Z) by <: ]. *)
(*   Definition v_Z_isFinite : isFinite (Choice.sort (chElement v_G_t_Group.(f_Z))). *)
(*   Proof. Admitted. *)
(*       (* [ Finite of v_G_t_Group.(f_Z) by <: ]. *) *)

(*   Definition f_prodA : associative (lower2 f_prod). Admitted. *)
(*   Definition f_prod1 : associative (lower2 f_prod). Admitted. *)
(*   Definition f_prod_left_id : left_id (is_pure f_group_one) (lower2 f_prod). Admitted. *)
(*   Definition f_invK : involutive (lower1 f_inv). Admitted. *)
(*   Definition f_invM : {morph (lower1 f_inv)  : x y / (lower2 f_prod) x y >-> (lower2 f_prod)  y x}. Admitted. *)

(*   Definition v_Z_Field : GRing.Field (v_G_t_Group.(f_Z)). Admitted. *)

(*   Definition prod_inv_cancel : forall x, f_prod (f_inv x) x ≈both f_group_one. Admitted. *)

(* End Z89_group_operations. *)

(* Module Z89_secure_group <: SecureGroup Z89_impl Z89_group_operations. *)
(*   Module Group := HacspecGroup Z89_impl Z89_group_operations. *)
(*   Include Group. *)

(*   (* Lemma prime_q : prime (nat_of_ord (is_pure f_q)). *) *)
(*   (* Proof. *) *)
(*   (*   rewrite inordK. *) *)
(*   (*   simpl. *) *)
(*   (* Qed. *) *)

(*   (* Lemma prime_g : prime (nat_of_ord (is_pure f_g)). *) *)
(*   (* Proof. now rewrite inordK. Qed. *) *)

(*   Lemma lower2_cancel_lift2_both : forall {A B C : choice_type} (f : A -> B -> C) x y, lower2 (lift2_both f) x y = f x y. *)
(*   Proof. reflexivity. Qed. *)

(*   Lemma v_G_prime_order : prime #[(is_pure f_g : v_G_is_group)]. *)
(*     simpl. *)
(*   Admitted. *)
(*   (* Proof. *) *)
(*   (*   intros. *) *)
(*   (*   simpl. *) *)
(*   (*   (* replace (inord 1) with (inord 89). *) *) *)
(*   (*   (* pose (order_Zp1 88). *) *) *)
(*   (*   (* unfold Zp1 in e. *) *) *)
(*   (*   epose order1. *) *)
(*   (*   Set Printing All. *) *)
(*   (*   replace (inZp _) with (inord (n' := 88) 1) in e. *) *)
(*   (*   - rewrite order1. *) *)
(*   (*     rewrite order1 in e. *) *)
(*   (*     Set Printing All. *) *)

(*   (*     unfold v_G_is_group. *) *)
(*   (*     simpl. *) *)
(*   (*     unfold order. *) *)
(*   (*     simpl. *) *)
(*   (*     rewrite e. *) *)
(*   (*     easy. *) *)
(*   (*   - apply ord_inj; now rewrite inordK. *) *)
(*   (* Qed. *) *)

(*   Lemma v_G_g_gen : [set : v_G_is_group] = <[ is_pure f_g : v_G_is_group]>. Admitted. *)
(* End Z89_secure_group. *)

(* (* Module OVN_schnorr_proof_params_Z89 <: OVN_schnorr_proof_preconditions Z89_impl Z89_group_operations Z89_secure_group. *) *)
(* (*   Include Z89_secure_group. *) *)

(* (*   Module HacspecGroup := HacspecGroupParam Z89_impl Z89_group_operations Z89_secure_group. *) *)
(* (*   Module Schnorr := Schnorr HacspecGroup. *) *)

(* (*   Import Schnorr.MyParam. *) *)
(* (*   Import Schnorr.MyAlg. *) *)

(* (*   Import Schnorr.Sigma.Oracle. *) *)
(* (*   Import Schnorr.Sigma. *) *)

(* (*   Definition StatementToGroup : Statement -> v_G := id. *) *)

(* (*   (* Lemma group_size : #[HacspecGroup.g].-2.+2 = 89. *) *) *)
(* (*   (* Proof. *) *) *)
(* (*   (*   rewrite totient_gen. *) *) *)
(* (*   (*   epose (@generator_order v_G_is_group (is_pure f_g) (1)). *) *) *)
(* (*   (*   rewrite e. *) *) *)
(* (*   (*   2:{ *) *) *)
(* (*   (*     simpl. *) *) *)
(* (*   (*     pose (cycle_generator). *) *) *)
(* (*   (*     unfold generator. *) *) *)
(* (*   (*     reflexivity. *) *) *)
(* (*   (*   epose (@generator_cycle v_G_is_group (is_pure f_g)). *) *) *)
(* (*   (*   simpl in i. *) *) *)
(* (*   (*   unfold generator in i. *) *) *)

(* (*   (*   assert (HacspecGroup.g = inZp 1). *) *) *)
(* (*   (*   { *) *) *)
(* (*   (*     unfold inZp. *) *) *)
(* (*   (*     unfold HacspecGroup.g. *) *) *)
(* (*   (*     simpl. *) *) *)
(* (*   (*     unfold inord. *) *) *)
(* (*   (*     unfold ord0. *) *) *)
(* (*   (*     unfold insubd. *) *) *)
(* (*   (*     unfold insub. *) *) *)
(* (*   (*     unfold odflt. *) *) *)
(* (*   (*     unfold oapp. *) *) *)
(* (*   (*     unfold sub. *) *) *)
(* (*   (*     destruct idP. *) *) *)
(* (*   (*     - simpl. *) *) *)


(* (*   (*     simpl. *) *) *)

(* (*   (*     simpl. *) *) *)


(* (*   (*   cbn. *) *) *)
(* (*   (*   rewrite card_Aut_cycle. *) *) *)
(* (*   (*   reflexivity. *) *) *)

(* (*   Lemma inord_is_inZp : forall {n} x, (x < n.+1)%nat -> inord (n' := n) x = inZp (p' := n) x. *) *)
(* (*   Proof. *) *)
(* (*     intros n x H. *) *)
(* (*     rewrite <- (inordK (m := x) (n' := n)) ; [ | assumption ]. *) *)
(* (*     rewrite (valZpK (inord (n' := n) x)). *) *)
(* (*     rewrite inord_val. *) *)
(* (*     reflexivity. *) *)
(* (*   Qed. *) *)

(* (*   Definition WitnessToField : Witness -> v_G_t_Group.(f_Z) := fun x => mkword _ (Z.of_nat ((nat_of_ord x) %% Schnorr.q)). *) *)
(* (*   Definition FieldToWitness : v_G_t_Group.(f_Z) -> Witness := fun x => inord ((Z.to_nat (unsigned x)) %% Schnorr.q). *) *)

(* (*   Lemma group_size_is_q : (Schnorr.q = Z.to_nat (unsigned (is_pure (HacspecGroup.v_G_t_Group.(f_Z_t_Field).(f_q))))). *) *)
(* (*   Admitted. *) *)


(* (*   Lemma in_equality : forall v u, is_true (0 <= v < u)%R <-> is_true (Z.to_nat v < Z.to_nat u)%N. *) *)
(* (*   Admitted. *) *)

(* (*   Lemma WitnessToFieldCancel : forall x, WitnessToField (FieldToWitness x) = x. *) *)
(* (*   Proof. *) *)
(* (*     intros. *) *)
(* (*     simpl in *. *) *)

(* (*     destruct x. *) *)
(* (*     unfold WitnessToField, FieldToWitness. *) *)
(* (*     simpl. *) *)
(* (*     rewrite !inordK. *) *)
(* (*     2:{ *) *)
(* (*       simpl. *) *)
(* (*       rewrite Schnorr.order_ge1. *) *)
(* (*       simpl. *) *)
(* (*       Set Printing Coercions. *) *)
(* (*       unfold unsigned. *) *)
(* (*       unfold urepr. *) *)
(* (*       simpl. *) *)

(* (*       apply ltn_pmod. *) *)
(* (*       now rewrite group_size_is_q. *) *)
(* (*     } *) *)
(* (*     apply word_ext. *) *)
(* (*     rewrite modn_mod. *) *)
(* (*     rewrite modnZE ; [ |  now rewrite group_size_is_q]. *) *)
(* (*     rewrite Z2Nat.id ; [ | now destruct toword ]. *) *)
(* (*     cbn. *) *)

(* (*     rewrite group_size_is_q. *) *)
(* (*     cbn. *) *)
(* (*     rewrite Z2Nat.id ; [ | easy ]. *) *)
(* (*     unfold Build_t_z_89_ at 1. *) *)
(* (*     simpl. *) *)
(* (*     set (Z.pos _). *) *)
(* (*     rewrite (Z.mod_small z). *) *)
(* (*     - rewrite Z.mod_small. *) *)



(* (*     (* assert (forall p b x, Z.pos p <= b -> x mod (Z.pos p) mod b = x mod (Z.pos p)). *) *) *)
(* (*     (* { *) *) *)
(* (*     (*   intros. *) *) *)
(* (*     (*   rewrite Z.mod_small_iff. *) *) *)

(* (*     (*   epose (Znumtheory.Zmod_div_mod b (Z.pos p) xa). *) *) *)
(* (*     (*   rewrite <- e. *) *) *)

(* (*     (*   induction p. *) *) *)
(* (*     (*   - *) *) *)
(* (*     (*     cbn. *) *) *)
(* (*   Admitted. *) *)



(* (*   Lemma FieldToWitnessCancel : *) *)
(* (*     forall x, FieldToWitness (WitnessToField x) = x. *) *)
(* (*   Proof. *) *)
(* (*     intros. *) *)
(* (*     unfold WitnessToField, FieldToWitness. *) *)
(* (*     unfold unsigned. *) *)
(* (*     rewrite mkwordK. *) *)
(* (*     simpl. *) *)
(* (*     rewrite Zmod_small. *) *)
(* (*     2: { *) *)
(* (*       destruct x. *) *)
(* (*       cbn. *) *)
(* (*       rewrite Schnorr.order_ge1 in i. *) *)

(* (*     (* rewrite Nat2Z.id. *) *) *)
(* (*   (*   now rewrite inord_val. *) *) *)
(* (*       (* Qed. *) *) *)
(* (*       Admitted. *) *)

(* (*   Axiom WitnessToFieldAdd : forall x y, WitnessToField (Zp_add x y) = is_pure (f_add (ret_both (WitnessToField x)) (ret_both (WitnessToField y))). *) *)
(* (*   Axiom WitnessToFieldMul : forall x y, WitnessToField (Zp_mul x y) = is_pure (f_mul (ret_both (WitnessToField x)) (ret_both (WitnessToField y))). *) *)

(* (*   Axiom randomness_sample_is_bijective : *) *)
(* (*     bijective *) *)
(* (*     (λ x : 'I_(2 ^ 32), *) *)
(* (*        fto *) *)
(* (*          (FieldToWitness *) *)
(* (*             (is_pure *) *)
(* (*                (f_random_field_elem (ret_both (Hacspec_Lib_Pre.repr _ (Z.of_nat (nat_of_ord x)))))))). *) *)

(* (*   Axiom hash_is_psudorandom : *) *)
(* (*     forall {A B} i (H : Positive i) f pre post (c0 : _ -> raw_code A) (c1 : _ -> raw_code B) l, *) *)
(* (*             bijective f *) *)
(* (*             → (∀ x1 : Arit (uniform i), ⊢ ⦃ pre ⦄ c0 x1 ≈ c1 (f x1) ⦃ post ⦄) -> *) *)
(* (*             ⊢ ⦃ pre ⦄ *) *)
(* (*           e ← sample uniform i ;; *) *)
(* (*           c0 e ≈ *) *)
(* (*           x ← is_state *) *)
(* (*             (f_hash (t_Group := v_G_t_Group) *) *)
(* (*                (impl__into_vec *) *)
(* (*                   (unsize *) *)
(* (*                      (box_new *) *)
(* (*                         (array_from_list l))))) ;; c1 x ⦃ post ⦄. *) *)

(* (*   Axiom conversion_is_true : *) *)
(* (*     forall (b : both (v_G_t_Group.(f_Z))), StatementToGroup *) *)
(* (*     (HacspecGroup.g ^+ FieldToWitness (is_pure b)) = is_pure (f_g_pow b). *) *)

(* (* End OVN_schnorr_proof_params_Z89. *) *)

(* (* Module OVN_schnorr_proof_Z89 := OVN_schnorr_proof Z89_impl Z89_group_operations . *) *)

(* (* Schnorr_Z89.Sigma.RUN_interactive *) *)

(* (* Import Schnorr_Z89.Sigma. *) *)
(* (* Import Schnorr_Z89.MyAlg. *) *)
(* (* Import Schnorr_Z89.Sigma.Oracle. *) *)

(* (* Import Z89_impl. *) *)
