sed -i -z 's/Require Import Concordium_std.\nExport Concordium_std.\n//g' extraction/Hacspec_ovn_Ovn_traits.v
sed -i "s/(t_PartialEq f_Z)/(t_PartialEq f_Z f_Z)/g" extraction/Hacspec_ovn_Ovn_traits.v

# `:>` becomes `::` (version based syntax)

# Order in type class of generated elements from trait
# - f_Z_t_Field moved up, and t_PartialEq got an extra f_Z added

# Remove imports
sed -i -z "s/Require Import Concordium_std_derive.\nExport Concordium_std_derive.\n//g" extraction/Hacspec_ovn_Ovn_group.v
sed -i -z 's/Require Import Concordium_std.\nExport Concordium_std.\n//g' extraction/Hacspec_ovn_Ovn_group.v
sed -i "s/[(][*] From Jasmin Require Import word. [*][)]/From SSProve.Crypt Require Import jasmin_word./g" extraction/Hacspec_ovn_Ovn_group.v

# Import names changed:
# ```
# Require Import Crate_Ovn_traits.
# Export Crate_Ovn_traits.
# ```
# becomes
# ```
# From OVN Require Import Hacspec_ovn_Ovn_traits.
# Export Hacspec_ovn_Ovn_traits.
# ```

# and put type class instances into section context, that is move function arguments of the form
# ```
#  {v_Z : _} `{ t_Sized v_Z} `{ t_Field v_Z}
# ```
# to the top of the section. Helps Coq resolve call dependencies. This also requires fixing one some type annotations, by removing the extra arguments.

# Need to add instantionations.
# ```
# Context {v_G : choice_type}.
#
# (* TODO: Cannot find instance in hacspec lib? *)
# Instance v_G_t_copy : t_Copy v_G := _.
# Instance v_G_t_partial_eq : t_PartialEq v_G v_G := _.
# Instance v_G_t_eq : t_Eq v_G := _.
# Instance v_G_t_clone : t_Clone v_G := _.
# Instance v_G_t_serialize : t_Serialize v_G := _.
#
# Context {v_G_t_Group : t_Group v_G}.
# Instance v_G_t_Group_temp : t_Group v_G := v_G_t_Group.
#
# Context {v_A : choice_type}.
# Context {v_A_t_Sized : t_Sized v_A}.
# Instance v_A_t_Sized_temp : t_Sized v_A := v_A_t_Sized.
#
# Context {v_A_t_HasActions : t_HasActions v_A}.
# Instance v_A_t_HasActions_temp : t_HasActions v_A := v_A_t_HasActions.
#
# Context {n : both uint_size}.
#
# (* Extra from code *)
# Context {v_G_t_Sized : t_Sized v_G}.
# Instance v_G_t_Sized_temp : t_Sized v_G := v_G_t_Sized.
#
# Notation v_Z := f_Z.
# ```

sed -i -z "s/Require Import Crate_Ovn_traits.\nExport Crate_Ovn_traits./From OVN Require Import Hacspec_ovn_Ovn_traits.\nExport Hacspec_ovn_Ovn_traits.\n\nNotation \" x \'.a[\' a \']\'\" := (array_index x (* (n_seq_array_or_seq x _) *) a) (at level 40).\n\nModule Type HacspecOvnParameter.\n  (** Move arguments to context *)\n  Parameter (v_G : choice_type).\n\n  Parameter (v_G_t_Group : t_Group v_G).\n\n  Parameter (v_A : choice_type).\n  Parameter (v_A_t_Sized : t_Sized v_A).\n\n  Parameter (v_A_t_HasActions : t_HasActions v_A).\n\n  Parameter (n : both uint_size).\n  Parameter (n_pos : Positive (is_pure n)).\n\n  (* Extra from code *)\n  Parameter (v_G_t_Sized : t_Sized v_G).\n\n  Notation \"'v_Z'\" := f_Z : hacspec_scope.\nEnd HacspecOvnParameter.\n\nModule HacspecOvn (HOP : HacspecOvnParameter).\n  Include HOP.\n\n  Existing Instance v_G_t_Group.\n  Existing Instance v_A_t_Sized.\n  Existing Instance v_A_t_HasActions.\n  Existing Instance v_G_t_Sized.\n\n  (* TODO: Cannot find instance in hacspec lib? *)\n  Existing Instance copy.\n  Existing Instance partial_eq.\n  Existing Instance is_eq.\n  Existing Instance clone.\n  Existing Instance serialize.\n(** * Generated code *)\n/g" extraction/Hacspec_ovn_Ovn_group.v

# List of replacements or removed objects.
#   (* {v_Z : _} `{ t_Sized v_Z} `{ t_Field v_Z} *)
sed -i "s/ {v_Z : _} \`{ t_Sized v_Z} \`{ t_Field v_Z}//g" extraction/Hacspec_ovn_Ovn_group.v
#   (* {v_G : _} `{ t_Sized v_G} `{ t_Group v_G} *)
sed -i "s/ {v_G : _} \`{ t_Sized v_G} \`{ t_Group v_G}//g" extraction/Hacspec_ovn_Ovn_group.v
#   (* t_SchnorrZKPCommit v_G *)
sed -i "s/t_SchnorrZKPCommit v_G/t_SchnorrZKPCommit/g" extraction/Hacspec_ovn_Ovn_group.v
#   (* t_OrZKPCommit v_G *)
sed -i "s/t_OrZKPCommit v_G/t_OrZKPCommit/g" extraction/Hacspec_ovn_Ovn_group.v
#   (* {v_G : _} {n : both uint_size} `{ t_Sized v_G} `{ t_Group v_G} *)
sed -i "s/ {v_G : _} {n : both uint_size} \`{ t_Sized v_G} \`{ t_Group v_G}//g" extraction/Hacspec_ovn_Ovn_group.v
#   (* t_OvnContractState v_G (both uint_size) *)
sed -i "s/t_OvnContractState v_G (both uint_size)/t_OvnContractState/g" extraction/Hacspec_ovn_Ovn_group.v
#   (*  {v_G : _} {n : both uint_size} {v_A : _} {impl_574521470_ : _} `{ t_Sized v_G} `{ t_Sized v_A} `{ t_Sized impl_574521470_} `{ t_Group v_G} `{ t_HasActions v_A} `{ t_HasReceiveContext impl_574521470_ 'unit} *)
sed -i "s/ {v_G : _} {n : both uint_size} {impl_108907986_ : _} \`{ t_Sized v_G} \`{ t_Sized impl_108907986_} \`{ t_Group v_G} \`{ t_HasInitContext impl_108907986_ 'unit}//g" extraction/Hacspec_ovn_Ovn_group.v
#   (* {v_G : _}  {impl_108907986_ : _} `{ t_Sized v_G} `{ t_Sized impl_108907986_} `{ t_Group v_G} `{ t_HasInitContext impl_108907986_ 'unit} *)
sed -i "s/impl_108907986_/'unit/g" extraction/Hacspec_ovn_Ovn_group.v
#   (* impl_108907986_ *)
sed -i "s/ {v_G : _} {n : both uint_size} {v_A : _} {impl_574521470_ : _} \`{ t_Sized v_G} \`{ t_Sized v_A} \`{ t_Sized impl_574521470_} \`{ t_Group v_G} \`{ t_HasActions v_A} \`{ t_HasReceiveContext impl_574521470_ 'unit}//g" extraction/Hacspec_ovn_Ovn_group.v
#   (* impl_574521470_ -> t_CastVoteParam or t_RegisterParam or t_TallyParameter *)
sed -i "s/cast_vote (ctx : both impl_574521470_)/cast_vote (ctx : both t_CastVoteParam)/" extraction/Hacspec_ovn_Ovn_group.v
sed -i "s/commit_to_vote (ctx : both impl_574521470_)/commit_to_vote (ctx : both t_CastVoteParam)/" extraction/Hacspec_ovn_Ovn_group.v
sed -i "s/register_vote (ctx : both impl_574521470_)/register_vote (ctx : both t_RegisterParam)/" extraction/Hacspec_ovn_Ovn_group.v
sed -i "s/tally_votes (_ : both impl_574521470_)/tally_votes (_ : both t_TallyParameter)/" extraction/Hacspec_ovn_Ovn_group.v

# # Add instance (Should be done via attributes)
# sed -i -z "s/Equations cast_vote/(* Automatically generated outline, manually filled in *)\n  #[global] Program Instance t_CastVoteParam_t_HasReceiveContext : t_HasReceiveContext t_CastVoteParam 'unit :=\n    {| f_get := (fun  (ctx : _) => (solve_lift (@ret_both (t_ParamType × t_Result t_CastVoteParam t_ParseError)) (tt, inl ctx)) : _)|}.\n  Fail Next Obligation.\n  #[global] Program Instance t_CastVoteParam_t_Sized : t_Sized t_CastVoteParam :=\n    fun x =>\n      x.\n  Fail Next Obligation.\n\nEquations cast_vote/g" extraction/Hacspec_ovn_Ovn_group.v

# sed -i -z "s/Equations register_vote/(* Automatically generated outline, manually filled in *)\n#[global] Program Instance t_RegisterParam_t_HasReceiveContext : t_HasReceiveContext t_RegisterParam 'unit :=\n    {| f_get := (fun  (ctx : _) => (solve_lift (@ret_both (t_ParamType × t_Result t_RegisterParam t_ParseError)) (tt, inl ctx)) : _)|}.\n  Fail Next Obligation.\n  #[global] Program Instance t_RegisterParam_t_Sized : t_Sized t_RegisterParam :=\n    fun x =>\n      x.\n  Fail Next Obligation.\n\nEquations register_vote/g" extraction/Hacspec_ovn_Ovn_group.v



sed -i "s/:= out/:= impl__map_err out f_from/g" extraction/Hacspec_ovn_Ovn_group.v

sed -i "s/(WS2 := _)/(WS2 := U32)/g" extraction/Hacspec_ovn_Ovn_group.v

# add:
# ```coq
#   Solve All Obligations with now intros ; destruct from_uint_size.
# ```
# to help resolve obligations, for memory loctions.

sed -i -z "s/div prod1 prod2 : both v_G.\nFail Next Obligation./div prod1 prod2 : both v_G.\nSolve All Obligations with now intros ; destruct from_uint_size.\nFail Next Obligation./g" extraction/Hacspec_ovn_Ovn_group.v

# Comment away `t_ParseError` from `letm[ _ ]` (incorrect infered type)
sed -i "s/bind_code t_ParseError/bind_code _ (* t_ParseError *)/g" extraction/Hacspec_ovn_Ovn_group.v

# Replace ControlFlow_ with v_
sed -i "s/ControlFlow_Break/v_Break/g" extraction/Hacspec_ovn_Ovn_group.v

# Comment away `t_ControlFlow` (does not exists)
sed -i "s/(t_ControlFlow (t_Result (v_A × t_OvnContractState) t_ParseError) 'unit)/_/g" extraction/Hacspec_ovn_Ovn_group.v

# Comment away `ParseError` does not exists and incorrect type.
sed -i "s/ ParseError/ _/g" extraction/Hacspec_ovn_Ovn_group.v

# Replace not with negb, incorrect name!
sed -i -z "s/not/negb/g" extraction/Hacspec_ovn_Ovn_group.v

# Add Result_Ok to accumulator for foldi_both_list, incorrect type?
sed -i "s/(ret_both (tt : 'unit)) in/(Result_Ok (ret_both (tt : 'unit))) in/g" extraction/Hacspec_ovn_Ovn_group.v

# Remove extra
sed -i "s/{n : both uint_size}//g" extraction/Hacspec_ovn_Ovn_group.v

sed -i -z "s/Fail Next Obligation./Solve All Obligations with now intros ; destruct from_uint_size.\nFail Next Obligation./g" extraction/Hacspec_ovn_Ovn_group.v

sed -i -z "s/Admitted/_ (Build_t_OvnContractState (f_g_pow_xis := repeat f_group_one n) (f_zkp_xis := repeat (Build_t_SchnorrZKPCommit (f_schnorr_zkp_u := f_group_one) (f_schnorr_zkp_z := f_field_zero) (f_schnorr_zkp_c := f_field_zero)) n) (f_commit_vis := repeat f_field_zero n) (f_g_pow_xi_yi_vis := repeat f_group_one n) (f_zkp_vis := repeat (Build_t_OrZKPCommit (f_or_zkp_x := f_group_one) (f_or_zkp_y := f_group_one) (f_or_zkp_a1 := f_group_one) (f_or_zkp_b1 := f_group_one) (f_or_zkp_a2 := f_group_one) (f_or_zkp_b2 := f_group_one) (f_or_zkp_c := f_field_zero) (f_or_zkp_d1 := f_field_zero) (f_or_zkp_d2 := f_field_zero) (f_or_zkp_r1 := f_field_zero) (f_or_zkp_r2 := f_field_zero)) n) (f_tally := ret_both (0 : int32)) (f_round1 := repeat (ret_both (false : 'bool)) n))/g" extraction/Hacspec_ovn_Ovn_group.v

echo "End HacspecOvn." >> extraction/Hacspec_ovn_Ovn_group.v
