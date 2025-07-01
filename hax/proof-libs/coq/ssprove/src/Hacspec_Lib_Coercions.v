Global Set Warnings "-ambiguous-paths".
Global Set Warnings "-uniform-inheritance".
Global Set Warnings "-auto-template".
Global Set Warnings "-disj-pattern-notation".
Global Set Warnings "-notation-overridden,-ambiguous-paths".

Require Import Lia.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Sumbool.

From mathcomp Require Import fintype.

From SSProve Require Import choice_type Package Prelude.
Import PackageNotation.
From extructures Require Import ord fset fmap.

From Coq Require Import ZArith List.
Import List.ListNotations.

Import choice.Choice.Exports.

(********************************************************)
(*   Implementation of all Hacspec library functions    *)
(* for Both types.                                      *)
(********************************************************)

Declare Scope hacspec_scope.

From Hacspec Require Import ChoiceEquality.
From Hacspec Require Import LocationUtility.
From Hacspec Require Import Hacspec_Lib_Comparable.
From Hacspec Require Import Hacspec_Lib_Pre.

Open Scope bool_scope.
Open Scope hacspec_scope.
Open Scope nat_scope.
Open Scope list_scope.

From Hacspec Require Import Hacspec_Lib_Natmod.

(**** Integers to arrays *)
Definition uint16_to_le_bytes (n : int16) : both ((nseq_ int8 2)) := ret_both (uint16_to_le_bytes n).
Definition uint16_to_be_bytes (n : int16) : both ((nseq_ int8 2)) := ret_both (uint16_to_be_bytes n).
Definition uint16_from_le_bytes (n : (nseq_ int8 2)) : both ((int16)) := ret_both (uint16_from_le_bytes n).
Definition uint16_from_be_bytes (n : (nseq_ int8 2)) : both ((int16)) := ret_both (uint16_from_be_bytes n).
Definition uint32_to_le_bytes (n : int32) : both ((nseq_ int8 4)) := ret_both (uint32_to_le_bytes n).
Definition uint32_to_be_bytes (n : int32) : both ((nseq_ int8 4)) := ret_both (uint32_to_be_bytes n).
Definition uint32_from_le_bytes (n : (nseq_ int8 4)) : both ((int32)) := ret_both (uint32_from_le_bytes n).
Definition uint32_from_be_bytes (n : (nseq_ int8 4)) : both ((int32)) := ret_both (uint32_from_be_bytes n).
Definition uint64_to_le_bytes (n : int64) : both ((nseq_ int8 8)) := ret_both (uint64_to_le_bytes n).
Definition uint64_to_be_bytes (n : int64) : both ((nseq_ int8 8)) := ret_both (uint64_to_be_bytes n).
Definition uint64_from_le_bytes (n : (nseq_ int8 8)) : both ((int64)) := ret_both (uint64_from_le_bytes n).
Definition uint64_from_be_bytes (n : (nseq_ int8 8)) : both ((int64)) := ret_both (uint64_from_be_bytes n).
Definition uint128_to_le_bytes (n : int128) : both ((nseq_ int8 16)) := ret_both (uint128_to_le_bytes n).
Definition uint128_to_be_bytes (n : int128) : both ((nseq_ int8 16)) := ret_both (uint128_to_be_bytes n).
Definition uint128_from_le_bytes (n : (nseq_ int8 16)) : both (int128) := ret_both (uint128_from_le_bytes n).
Definition uint128_from_be_bytes (n : (nseq_ int8 16)) : both ((int128)) := ret_both (uint128_from_be_bytes n).
Definition u32_to_le_bytes (n : int32) : both ((nseq_ int8 4)) := ret_both (u32_to_le_bytes n).
Definition u32_to_be_bytes (n : int32) : both ((nseq_ int8 4)) := ret_both (u32_to_be_bytes n).
Definition u32_from_le_bytes (n : (nseq_ int8 4)) : both ((int32)) := ret_both (u32_from_le_bytes n).
Definition u32_from_be_bytes (n : (nseq_ int8 4)) : both ((int32)) := ret_both (u32_from_be_bytes n).
Definition u64_to_le_bytes (n : int64) : both ((nseq_ int8 8)) := ret_both (u64_to_le_bytes n).
Definition u64_from_le_bytes (n : (nseq_ int8 8)) : both ((int64)) := ret_both (u64_from_le_bytes n).
Definition u128_to_le_bytes (n : int128) : both ((nseq_ int8 16)) := ret_both (u128_to_le_bytes n).
Definition u128_to_be_bytes (n : int128) : both ((nseq_ int8 16)) := ret_both (u128_to_be_bytes n).
Definition u128_from_le_bytes (n : (nseq_ int8 16)) : both ((int128)) := ret_both (u128_from_le_bytes n).
Definition u128_from_be_bytes (n : (nseq_ int8 16)) : both ((int128)) := ret_both (u128_from_be_bytes n).

(*** Casting *)

Section TodoSection2.

Definition uint128_from_usize (n : uint_size) : both int128 := ret_both (repr _ (unsigned n)).
Definition uint64_from_usize (n : uint_size) : both int64 := ret_both (repr _ (unsigned n)).
Definition uint32_from_usize (n : uint_size) : both int32 := ret_both (repr _ (unsigned n)).
Definition uint16_from_usize (n : uint_size) : both int16 := ret_both (repr _ (unsigned n)).
Definition uint8_from_usize (n : uint_size) : both int8 := ret_both (repr _ (unsigned n)).

Definition uint128_from_uint8 (n : int8) : both int128 := ret_both (repr _ (unsigned n)).
Definition uint64_from_uint8 (n : int8) : both int64 := ret_both (repr _ (unsigned n)).
Definition uint32_from_uint8 (n : int8) : both int32 := ret_both (repr _ (unsigned n)).
Definition uint16_from_uint8 (n : int8) : both int16 := ret_both (repr _ (unsigned n)).
Definition usize_from_uint8 (n : int8) : both uint_size := ret_both (repr _ (unsigned n)).

Definition uint128_from_uint16 (n : int16) : both int128 := ret_both (repr _ (unsigned n)).
Definition uint64_from_uint16 (n : int16) : both int64 := ret_both (repr _ (unsigned n)).
Definition uint32_from_uint16 (n : int16) : both int32 := ret_both (repr _ (unsigned n)).
Definition uint8_from_uint16 (n : int16) : both int8 := ret_both (repr _ (unsigned n)).
Definition usize_from_uint16 (n : int16) : both uint_size := ret_both (repr _ (unsigned n)).

Definition uint128_from_uint32 (n : int32) : both int128 := ret_both (repr _ (unsigned n)).
Definition uint64_from_uint32 (n : int32) : both int64 := ret_both (repr _ (unsigned n)).
Definition uint16_from_uint32 (n : int32) : both int16 := ret_both (repr _ (unsigned n)).
Definition uint8_from_uint32 (n : int32) : both int8 := ret_both (repr _ (unsigned n)).
Definition usize_from_uint32 (n : int32) : both uint_size := ret_both (repr _ (unsigned n)).

Definition uint128_from_uint64 (n : int64) : both int128 := ret_both (repr _ (unsigned n)).
Definition uint32_from_uint64 (n : int64) : both int32 := ret_both (repr _ (unsigned n)).
Definition uint16_from_uint64 (n : int64) : both int16 := ret_both (repr _ (unsigned n)).
Definition uint8_from_uint64 (n : int64) : both int8 := ret_both (repr _ (unsigned n)).
Definition usize_from_uint64 (n : int64) : both uint_size := ret_both (repr _ (unsigned n)).

Definition uint64_from_uint128 (n : int128) : both int64 := ret_both (repr _ (unsigned n)).
Definition uint32_from_uint128 (n : int128) : both int32 := ret_both (repr _ (unsigned n)).
Definition uint16_from_uint128 (n : int128) : both int16 := ret_both (repr _ (unsigned n)).
Definition uint8_from_uint128 (n : int128) : both int8 := ret_both (repr _ (unsigned n)).
Definition usize_from_uint128 (n : int128) : both uint_size := ret_both (repr _ (unsigned n)).

End TodoSection2.
