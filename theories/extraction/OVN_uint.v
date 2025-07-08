From Coq Require Import List.
From Coq Require Import ZArith.
From Coq Require Import Lia.
From ConCert.Utils Require Import Extras.
From ConCert.Utils Require Import RecordUpdate.
From ConCert.Execution Require Import Blockchain.
From ConCert.Execution Require Import Containers.
From ConCert.Execution Require Import Monad.
From ConCert.Execution Require Import ResultMonad.
From ConCert.Execution Require Import Serializable.
From ConCert.Execution Require Import ContractCommon. Import AddressMap.
From OVN Require Import ConCert_ovn.
From OVN Require sha256.
From compcert.lib Require Integers.
From Coq Require Import Uint63.

Import ListNotations.



Module Type GroupParams.
  Parameter prime : int.
  Parameter generator : int.
  Parameter values : list int.
End GroupParams.

Module OVN_Uint63 (G : GroupParams).
  Include G.

  Module OVN_ <: OVNParams.
    Definition AddrSize : N := 64.
    Definition ContractAddrBase : N := AddrSize / 2.

    Definition T : Type := int.
    Definition ser_T : Serializable T. Admitted.
    Definition base : ChainBase := {|
      Address := N;
      address_eqb := N.eqb;
      address_eqb_spec := N.eqb_spec;
      address_is_contract a := (ContractAddrBase <=? a)%N
    |}.

    #[bypass_check(guard)]
    Program Fixpoint egcd_aux
            (n : int)
            (r0 a0 b0 r1 a1 b1 : int) {measure (Z.to_nat (to_Z n))} : int * int :=
      (if n =? 0
      then (0, 0)
      else
        let m := n - 1 in
        let (q, r) := diveucl r0 r1 in
        if eqb r 0
        then (a1, b1)
        else egcd_aux n r1 a1 b1 r (a0 - q*a1) (b0 - q*b1)
      )%uint63.
    Next Obligation.
    Admitted.
    Final Obligation.
    Admitted.

    Definition sgn (n : int) : int :=
      (if n =? 0
      then 0
      else 1)%uint63.

    (* returns (x, y) such that x*m + y*n = Z.gcd(x, y) *)
    Definition egcd (m n : int) : int * int :=
      (if eqb m 0 then
        (0, sgn n)
      else if eqb n 0 then
        (sgn m, 0)
      else
        (* let num_steps := (Z.log2 (abs m) + Z.log2 (abs n)) + 1 in *)
        let num_steps := ((m) + (n)) in
        if m <? n then
          let (x, y) := egcd_aux num_steps (n) 1 0 (m) 0 1 in
          (sgn m * y, sgn n * x)
        else
          let (x, y) := egcd_aux num_steps (m) 1 0 (n) 0 1 in
          (sgn m * x, sgn n * y))%uint63.

    Definition mod_inv (a : int) (p : int) : int :=
      let x := (egcd a p) in
      (fst x) mod p.

    Fixpoint mod_pow_pos_aux (a : int) (x : positive) (m : int) (r : int) : int :=
      match x with
      | x~0%positive => mod_pow_pos_aux (a * a mod m) x m r
      | x~1%positive => mod_pow_pos_aux (a * a mod m) x m (r * a mod m)
      | _ => r * a mod m
      end.

    Definition mod_pow_pos (a : int) (x : positive) (m : int) : int :=
      mod_pow_pos_aux a x m 1.

    Definition mod_pow (a x p : int) : int :=
      (if x =? 0
      then 1
      else (
        if 0 <=? x
        then mod_pow_pos a (Z.to_pos (to_Z x)) p
        else mod_inv (mod_pow_pos a (Z.to_pos (Z.abs (to_Z x))) p) p
      ))%uint63.



    Definition hash_f (x : list T) : T :=
      let is := sha256.intlist_to_bytelist (map Integers.Int.repr (map to_Z x)) in
      let h := sha256.SHA_256' is in
      match (sha256.bytelist_to_intlist h) with
      | y :: _ => of_Z (Integers.Int.unsigned y)
      | [] => 14%uint63
      end.



    Definition field_int : Field int :=
      (* let f_q := 9223372036854775782%uint63 in *)
      let f_q := prime%uint63 in
      let q := f_q in
      {|
        f_q := f_q;
        f_zero := 0%uint63;
        f_one := 1%uint63;
        f_add x y :=
          ((add x y) mod q)%uint63;
        f_opp x :=
          sub q x;
        f_mul x y :=
          ((mul x y) mod q)%uint63;
        f_inv x :=
          mod_inv x q;
      |}.

    Definition group_int : Group int :=
      let g_f := field_int in
      (* let g_g := 3%uint63 in *)
      let g_g := generator in
      let q := g_f.(f_q) in
      let g_prod x y :=
        ((mul x y) mod q)%uint63 in
      let g_pow x y :=
        mod_pow x y q in
    {|
      g_f := g_f;
      g_g := g_g;
      g_g_pow x := g_pow g_g x;
      g_pow := g_pow;
      g_one := 1%uint63;
      g_prod := g_prod;
      g_inv x :=
        mod_inv x q;
      (* hash := fun a => 14%uint63; *)
      hash := hash_f;
    |}.

    Definition group : Group T := group_int.

    Definition t_eqb := eqb.
    Definition t_eqb_spec : forall x y, Bool.reflect (x = y) (t_eqb x y). Admitted.

  End OVN_.

  Module OVN' := OVN OVN_.
  Include OVN'.

End OVN_Uint63.


Module G_9223372036854775783 <: GroupParams.
  Definition prime : int := 9223372036854775782%uint63.
  (* Generators: 2, 3, 17, 23, 319279, 456065899 *)
  Definition generator : int := 3%uint63.

  Definition values : list int := [].
End G_9223372036854775783.

Module G_4294967291 <: GroupParams.
  Definition prime : int := 4294967290%uint63.
  Definition generator : int := 6%uint63.

  Definition values : list int := [].
End G_4294967291.

Module G_251 <: GroupParams.
  Definition prime : int := 250%uint63.
  Definition generator : int := 3%uint63.

  Definition values : list int := [].
End G_251.
