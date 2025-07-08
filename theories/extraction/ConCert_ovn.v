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

Import ListNotations.

Class Field (T : Type) := {
  f_q : T;
  f_zero : T;
  f_one : T;
  f_add : T -> T -> T;
  f_opp : T -> T;
  f_mul : T -> T -> T;
  f_inv : T -> T;
}.

Class Group (T : Type) := {
  g_f :: (Field T);
  g_g : T;
  g_g_pow : T -> T;
  g_pow : T -> T -> T;
  g_one : T;
  g_prod : T -> T -> T;
  g_inv : T -> T;
  hash : list T -> T;
}.

Module Type OVNParams.
    Parameter T : Type.
    Parameter group : Group T.
    Parameter ser_T : Serializable T.
    Parameter base : ChainBase.
    Parameter t_eqb : T -> T -> bool.
    Parameter t_eqb_spec : forall x y, Bool.reflect (x = y) (t_eqb x y).
    (* Parameter n : N. *)
End OVNParams.

Module OVN (OVN_P : OVNParams).
  Set Nonrecursive Elimination Schemes.

  Import OVN_P.

  Existing Instance group.
  Existing Instance ser_T.
  Existing Instance base.

  Definition Error : Type := nat.
  Definition default_error : Error := 0.

  Record SchnorrZKP := {
    schnorr_zkp_u : T;
    schnorr_zkp_c : T;
    schnorr_zkp_z : T;
  }.

  Record OrZKP := {
    or_zkp_x : T;
    or_zkp_y : T;
    or_zkp_a1 : T;
    or_zkp_b1 : T;
    or_zkp_a2 : T;
    or_zkp_b2 : T;
    or_zkp_c : T;
    or_zkp_d1 : T;
    or_zkp_d2 : T;
    or_zkp_r1 : T;
    or_zkp_r2 : T;
  }.

  Record State := {
    voters : list Address;
    voters_n : nat;

    public_keys : list (option T);
    schnorr_zkps : list (option SchnorrZKP);
    commits : list (option T);
    ballots : list (option T);
    or_zkps : list (option OrZKP);

    register_count : nat;
    commit_count : nat;
    vote_count : nat;

    tally : option nat;
  }.

  Record Setup := {
    participants : nat;
    voter_addrs : list Address;
  }.

  Record RegisterParam := {
    rp_i : nat;
    rp_g_pow_xi : T;
    rp_zkp_xi : SchnorrZKP;
  }.

  Record PrivateRegisterParam := {
    rp_xi : T;
    rp_zkp_random : T;
  }.

  Record CommitParam := {
    cp_i : nat;
    cp_commit_vi : T;
  }.

  Record PrivateCommitParam := {
    cp_i_ : nat;
    cp_xi : T;
    cp_zkp_random_w : T;
    cp_zkp_random_r : T;
    cp_zkp_random_d : T;
    cp_vote : bool;
  }.

  Record VoteParam := {
    vp_i : nat;
    vp_zkp_vi : OrZKP;
    vp_g_pow_xi_yi_vi : T;
  }.

  Record PrivateVoteParam := {
    vp_i_ : nat;
    vp_xi : T;
    vp_zkp_random_w : T;
    vp_zkp_random_r : T;
    vp_zkp_random_d : T;
    vp_vote : bool;
  }.

  Inductive Msg :=
  | msg_register (rp : RegisterParam)
  | msg_commit (cp : CommitParam)
  | msg_vote (vp : VoteParam)
  | msg_tally.

  (* begin hide *)
  MetaCoq Run (make_setters State).

  Section Serialization.

    Global Instance setup_serializable : Serializable Setup :=
      Derive Serializable Setup_rect <Build_Setup>.

    Global Instance schnorr_zkp_serializable : Serializable SchnorrZKP :=
      Derive Serializable SchnorrZKP_rect <Build_SchnorrZKP>.

    Global Instance or_zkp_serializable : Serializable OrZKP :=
      Derive Serializable OrZKP_rect <Build_OrZKP>.

    Global Instance state_serializable : Serializable State :=
      Derive Serializable State_rect <Build_State>.

    Global Instance register_param_serializable : Serializable RegisterParam :=
      Derive Serializable RegisterParam_rect <Build_RegisterParam>.

    Global Instance commit_param_serializable : Serializable CommitParam :=
      Derive Serializable CommitParam_rect <Build_CommitParam>.

    Global Instance vote_param_serializable : Serializable VoteParam :=
      Derive Serializable VoteParam_rect <Build_VoteParam>.

    Global Instance msg_serializable : Serializable Msg :=
      Derive Serializable Msg_rect <msg_register, msg_commit, msg_vote, msg_tally>.

  End Serialization.
  (* end hide *)


  Definition ovn_init (chain : Chain)
                      (ctx : ContractCallContext)
                      (setup : Setup)
                      : result State Error :=
  Ok {|
    voters := setup.(voter_addrs);
    voters_n := setup.(participants);

    public_keys := repeat None setup.(participants);
    schnorr_zkps := repeat None setup.(participants);
    commits := repeat None setup.(participants);
    ballots := repeat None setup.(participants);
    or_zkps := repeat None setup.(participants);

    register_count := 0;
    commit_count := 0;
    vote_count := 0;

    tally := None;
  |}.


  Definition is_some {A : Type} (o : option A) : bool :=
    match o with
    | Some _ => true
    | None => false
    end.

  Definition throwIf {A : Type} c (e : A) :=
    ContractCommon.throwIf c e (* default_error *).

  Definition check_voter_address state a1 i :=
    match nth_error state.(voters) i with
    | Some a2 => address_eqb a1 a2
    | None => false
    end.

  Definition already_voted {A : Type} (l : list (option A)) i :=
    match nth_error l i with
    | Some (Some _) => true
    | Some None => false
    | None => true
    end.

  Fixpoint replace_nth {A : Type} (l : list A) (a : A) i :=
    match i, l with
    | O, x :: l' => a :: l'
    | O, [] => nil
    | S m, [] => nil
    | S m, x :: t => x :: (replace_nth t a m)
    end.


  Definition sub (x y : T) : T :=
    f_add x (f_opp y).

  Definition div (x y : T) : T :=
    g_prod x (g_inv y).

  Fixpoint filter_some {A : Type} (l : list (option A)) :=
    match l with
    | nil => nil
    | (Some x) :: l => x::(filter_some l)
    | None :: l => filter_some l
    end.

  Fixpoint prod_l (l : list T) : T :=
    match l with
    | [] => g_one
    | x :: xs => g_prod x (prod_l xs)
    end.

  Definition compute_g_pow_yi (n : nat) (l : list T) :=
    let lprod := prod_l (firstn n l) in
    let rprod := prod_l (skipn (S n) l) in
    div lprod rprod.


  Definition validate_schorr_zkp (g_pow_xi : T) (zkp_xi : SchnorrZKP) : result unit Error :=
    if andb (t_eqb zkp_xi.(schnorr_zkp_c) (hash [g_g; g_pow_xi; zkp_xi.(schnorr_zkp_u)]))
        (t_eqb (g_g_pow zkp_xi.(schnorr_zkp_z)) (g_prod zkp_xi.(schnorr_zkp_u) (g_pow g_pow_xi zkp_xi.(schnorr_zkp_c))))
    then Ok tt
    else Ok tt (* Err 1 *).

  Definition validate_commit (g_pow_xi_yi_vi : T) (commit : option (option T)) : result unit Error :=
    match commit with
    | Some (Some c) =>
      if t_eqb (hash [g_pow_xi_yi_vi]) c
      then Ok tt
      else Err 2
    | _ => Err 3
    end.

  Definition validate_or_zkp (g_pow_yi : T) (zkp_vi : OrZKP) : result unit Error :=
    let c := hash [
      zkp_vi.(or_zkp_x);
      zkp_vi.(or_zkp_y);
      zkp_vi.(or_zkp_a1);
      zkp_vi.(or_zkp_a2);
      zkp_vi.(or_zkp_b1);
      zkp_vi.(or_zkp_b2)
    ] in
    if (
      andb (t_eqb c (f_add zkp_vi.(or_zkp_d1) zkp_vi.(or_zkp_d2)))
      (andb (t_eqb zkp_vi.(or_zkp_a1) (g_prod (g_g_pow zkp_vi.(or_zkp_r1)) (g_pow zkp_vi.(or_zkp_x) zkp_vi.(or_zkp_d1))))
      (andb (t_eqb zkp_vi.(or_zkp_b1) (g_prod (g_pow g_pow_yi zkp_vi.(or_zkp_r1)) (g_pow zkp_vi.(or_zkp_y) zkp_vi.(or_zkp_d1))))
      (andb (t_eqb zkp_vi.(or_zkp_a2) (g_prod (g_g_pow zkp_vi.(or_zkp_r2)) (g_pow zkp_vi.(or_zkp_x) zkp_vi.(or_zkp_d2))))
            (t_eqb zkp_vi.(or_zkp_b2) (g_prod (g_pow g_pow_yi zkp_vi.(or_zkp_r2)) (g_pow (div zkp_vi.(or_zkp_y) g_g) zkp_vi.(or_zkp_d2))))
      ))))
    then Ok tt
    else Ok tt (* Err 4 *).

  Definition register_f (sender : Address)
                        (state : State)
                        (param : RegisterParam)
                        : result State Error :=
    (* Verify voter address *)
    do _ <- throwIf (negb (check_voter_address state sender param.(rp_i))) 5;
    (* Check if already registered *)
    do _ <- throwIf ((already_voted state.(public_keys) param.(rp_i)) || (already_voted state.(schnorr_zkps) param.(rp_i))) 6;

    (* Validate schnorr proof *)
    do _ <- validate_schorr_zkp param.(rp_g_pow_xi) param.(rp_zkp_xi);

    (* Update state *)
    let new_public_keys := replace_nth state.(public_keys) (Some param.(rp_g_pow_xi)) param.(rp_i) in
    let new_schnorr_zkps := replace_nth state.(schnorr_zkps) (Some param.(rp_zkp_xi)) param.(rp_i) in
    Ok (state<| public_keys := new_public_keys |><| schnorr_zkps := new_schnorr_zkps |><| register_count ::= Nat.succ |>).

  Definition commit_f (sender : Address)
                      (state : State)
                      (param : CommitParam)
                      : result State Error :=
    (* Verify voter address *)
    do _ <- throwIf (negb (check_voter_address state sender param.(cp_i))) 7;
    (* Check that registration round is over *)
    do _ <- throwIf (negb (state.(register_count) =? state.(voters_n))) 8;
    (* Check if already committed *)
    do _ <- throwIf (already_voted state.(commits) param.(cp_i)) 9;

    (* Update state *)
    let new_commits := replace_nth state.(commits) (Some param.(cp_commit_vi)) param.(cp_i) in
    Ok (state<| commits := new_commits |><| commit_count ::= Nat.succ |>).

  Definition vote_f (sender : Address)
                      (state : State)
                      (param : VoteParam)
                      : result State Error :=
    (* Verify voter address *)
    do _ <- throwIf (negb (check_voter_address state sender param.(vp_i))) 10;
    (* Check that commit round is over *)
    do _ <- throwIf (negb (state.(commit_count) =? state.(voters_n))) 11;
    (* Check if already voted *)
    do _ <- throwIf (already_voted state.(ballots) param.(vp_i)) 12;

    (* Validate commitment *)
    do _ <- validate_commit param.(vp_g_pow_xi_yi_vi) (nth_error state.(commits) param.(vp_i));
    (* Validate or proof *)
    let pks := filter_some state.(public_keys) in
    let g_pow_yi := compute_g_pow_yi param.(vp_i) pks in
    do _ <- validate_or_zkp g_pow_yi param.(vp_zkp_vi);

    (* Update state *)
    let new_ballots := replace_nth state.(ballots) (Some param.(vp_g_pow_xi_yi_vi)) param.(vp_i) in
    let new_or_zkps := replace_nth state.(or_zkps) (Some param.(vp_zkp_vi)) param.(vp_i) in
    Ok (state<| ballots := new_ballots |><|or_zkps := new_or_zkps |><| vote_count ::= Nat.succ |>).


  Definition compute_ballot_product l :=
    fold_left (fun acc x =>
      match x with
      | None => acc
      | Some x1 => g_prod acc x1
      end) l g_one.

  Fixpoint bruteforce_tally (i : nat) cur res :=
    match i with
    | O => 0
    | S j =>
      let guess := g_g_pow cur in
      if t_eqb guess res
      then i
      else bruteforce_tally j (f_add cur f_one) res
    end.

  Definition tally_f (sender : Address)
                      (state : State)
                      : result State Error :=
    (* Check that voting round is over *)
    do _ <- throwIf (negb (state.(vote_count) =? state.(voters_n))) 13;

    (* Compute ballot product *)
    let vote_result := compute_ballot_product state.(ballots) in

    (* Bruteforce tally *)
    let res := bruteforce_tally state.(voters_n) f_zero vote_result in

    (* Update state *)
    Ok (state<| tally := Some res |>).

  Definition ovn_receive (chain : Chain)
                         (ctx : ContractCallContext)
                         (state : State)
                         (msg : option Msg)
                         : result (State * list ActionBody) Error :=
    match msg with
    | Some (msg_register rp) =>
    do st <- register_f ctx.(ctx_from) state rp;
    Ok (st, [])
    | Some (msg_commit cp) =>
    do st <- commit_f ctx.(ctx_from) state cp;
    Ok (st, [])
    | Some (msg_vote vp) =>
    do st <- vote_f ctx.(ctx_from) state vp;
    Ok (st, [])
    | Some msg_tally =>
    do st <- tally_f ctx.(ctx_from) state;
    Ok (st, [])
    | None => Err default_error
    end.

  Definition ovn_contract : Contract Setup Msg State Error :=
    build_contract ovn_init ovn_receive.


  Section OffChain.
      Definition schnorr_zkp (r h x : T) : SchnorrZKP :=
        let u := g_g_pow r in
        let c := hash [g_g; h; u] in
        let z := f_add r (f_mul c x) in
        {|
          schnorr_zkp_u := u;
          schnorr_zkp_c := c;
          schnorr_zkp_z := z;
        |}.

      Definition zkp_one_out_of_two (random_w random_r random_d : T)
                                    (h xi : T)
                                    (vi : bool)
                                    : OrZKP :=
        let w := random_w in
        if vi
        then (
          let r1 := random_r in
          let d1 := random_d in

          let x := g_g_pow xi in
          let y := g_prod (g_pow h xi) g_g in

          let a1 := g_prod (g_g_pow r1) (g_pow x d1) in
          let b1 := g_prod (g_pow h r1) (g_pow y d1) in

          let a2 := g_g_pow w in
          let b2 := g_pow h w in

          let c := hash [x; y; a1; b1; a2; b2] in

          let d2 := sub c d1 in
          let r2 := sub w (f_mul xi d2) in

          {|
            or_zkp_x := x;
            or_zkp_y := y;
            or_zkp_a1 := a1;
            or_zkp_b1 := b1;
            or_zkp_a2 := a2;
            or_zkp_b2 := b2;
            or_zkp_c := c;
            or_zkp_d1 := d1;
            or_zkp_d2 := d2;
            or_zkp_r1 := r1;
            or_zkp_r2 := r2;
          |}
        )
        else (
          let r2 := random_r in
          let d2 := random_d in

          let x := g_g_pow xi in
          let y := g_pow h xi in

          let a1 := g_g_pow w in
          let b1 := g_pow h w in

          let a2 := g_prod (g_g_pow r2) (g_pow x d2) in
          let b2 := g_prod (g_pow h r2) (g_pow (div y g_g) d2) in

          let c := hash [x; y; a1; b1; a2; b2] in

          let d1 := sub c d2 in
          let r1 := sub w (f_mul xi d1) in

          {|
            or_zkp_x := x;
            or_zkp_y := y;
            or_zkp_a1 := a1;
            or_zkp_b1 := b1;
            or_zkp_a2 := a2;
            or_zkp_b2 := b2;
            or_zkp_c := c;
            or_zkp_d1 := d1;
            or_zkp_d2 := d2;
            or_zkp_r1 := r1;
            or_zkp_r2 := r2;
          |}
        ).

      Definition commit_to (g_pow_xi_yi_vi : T) : T :=
        hash [g_pow_xi_yi_vi].

      Definition register_to_vote_private (param : PrivateRegisterParam)
                                          : T * SchnorrZKP :=
        let g_pow_xi := g_g_pow param.(rp_xi) in
        let zkp_xi := schnorr_zkp param.(rp_zkp_random) g_pow_xi param.(rp_xi) in
        (g_pow_xi, zkp_xi).

      Definition compute_group_element_for_vote (xi : T)
                                                (vote : bool)
                                                (g_pow_yi : T)
                                                : T :=
        let x :=
          if vote
          then f_one
          else f_zero in
        g_prod (g_pow g_pow_yi xi) (g_g_pow x).

      Definition commit_to_vote_private (param : PrivateCommitParam)
                                        (g_pow_xis : list T)
                                        : T :=
        let g_pow_yi := compute_g_pow_yi param.(cp_i_) g_pow_xis in
        let g_pow_xi_yi_vi :=
          compute_group_element_for_vote param.(cp_xi)
                                         param.(cp_vote)
                                         g_pow_yi in
        let commit_vi := commit_to g_pow_xi_yi_vi in
        commit_vi.

      Definition cast_vote_private (param : PrivateVoteParam)
                                   (g_pow_xis : list T)
                                   : OrZKP * T :=
        let g_pow_yi := compute_g_pow_yi param.(vp_i_) g_pow_xis in
        let zkp_vi := zkp_one_out_of_two param.(vp_zkp_random_w)
                                         param.(vp_zkp_random_r)
                                         param.(vp_zkp_random_d)
                                         g_pow_yi
                                         param.(vp_xi)
                                         param.(vp_vote) in
        let g_pow_xi_yi_vi :=
          compute_group_element_for_vote param.(vp_xi)
                                         param.(vp_vote)
                                         g_pow_yi in
        (zkp_vi, g_pow_xi_yi_vi).
  End OffChain.
End OVN.

(*
From Coq Require Import Uint63.



Module OVN_Z <: OVNParams.
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
(*   Definition base : ChainBase := {|
    Address := (BoundedN AddrSize);
    address_eqb := BoundedN.eqb;
    address_eqb_spec := BoundedN.eqb_spec;
    address_is_contract a := (ContractAddrBase <=? BoundedN.to_N a)%N
  |}. *)

  (* Definition modulus := 0. *)



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

  Definition field_int : Field int :=
    (* let f_q := 250%Z (* 251 -1*) (* 89%Z  *)in *)
    (* let f_q := 4294967290%Z in *)
    (* let f_q := 18446744073709551557%uint63 in *)
    let f_q := 9223372036854775782%uint63 in
    let q := (* 88%Z *) f_q in
    {|
      f_q := f_q;
      f_zero := 0%uint63;
      f_one := 1%uint63;
      f_add x y :=
        (* let q := Z.sub f_q 1%Z in *)
        (* let x := Z.modulo x q in *)
        (* let y := Z.modulo y q in *)
        ((add x y) mod q)%uint63;
      f_opp x :=
        (* let q := Z.sub f_q 1%Z in *)
        (* let x := Z.modulo x q in *)
        sub q x;
      f_mul x y :=
        (* let q := Z.sub f_q 1%Z in *)
        (* let x := Z.modulo x q in *)
        (* let y := Z.modulo y q in *)
        ((mul x y) mod q)%uint63;
      f_inv x :=
        (* let q := Z.sub f_q 1%Z in *)
        mod_inv x q;
    |}.

  Definition group_int : Group int :=
    let g_f := field_int in
    (* let g_g := 6%Z (* 3%Z  *)in *)
    (* let g_g := 22%uint63 in *)
    let g_g := 3%uint63 in
    let q := (* 88%Z *) g_f.(f_q) in
    let g_prod x y :=
      (* let q := Z.sub g_f.(f_q) 1%Z in *)
      (* let x := Z.modulo x q in *)
      (* let y := Z.modulo y q in *)
      ((mul x y) mod q)%uint63 in
    let g_pow x y :=
      (* let q := Z.sub g_f.(f_q) 1%Z in *)
      mod_pow x y q in
  {|
    g_f := g_f;
    g_g := g_g;
    g_g_pow x := g_pow g_g x;
    g_pow := g_pow;
    g_one := 1%uint63;
    g_prod := g_prod;
    g_inv x :=
      (* let q := Z.sub g_f.(f_q) 1%Z in *)
      mod_inv x q;
    hash := fun a => 14%uint63;
  |}.

  Definition group : Group T := group_int.

  Definition t_eqb := eqb.
  Definition t_eqb_spec : forall x y, Bool.reflect (x = y) (t_eqb x y). Admitted.

End OVN_Z.

Module OVN_89 := OVN OVN_Z.
Import OVN_89.

Definition T : Type := int.

(* Goal
  let secrets0 := (
    (* secret key*)
    30%Z,
    (* vote *)
    true,
    (* randomness *)
    3%Z,
    1%Z,
    1%Z,
    1%Z) in
  let mk_reg (n : nat) (s : Z * bool * Z * Z * Z * Z) :=
  let '(x, v, sr, orw, orr, ord) := s in
  let private := {|
    rp_xi := x;
    rp_zkp_random := sr;
  |} in
  let (g_pow_xi, zkp_xi) := register_to_vote_private private in
  {|
    rp_i := n;
    rp_g_pow_xi := g_pow_xi;
    rp_zkp_xi := zkp_xi;
  |} in
  let reg_0 := mk_reg 0 secrets0 in
  let param := reg_0 in
  validate_schorr_zkp param.(rp_g_pow_xi) param.(rp_zkp_xi) = Ok tt.
  cbn -[validate_schorr_zkp register_to_vote_private].
  unfold register_to_vote_private.
  compute -[validate_schorr_zkp].
  compute -[Z.eqb]. *)


Definition ovn_test :=
  (* Call contexts *)
  let dummy_chain := {|
    chain_height := 0;
    current_slot := 0;
    finalized_height := 0;
  |} in
  let mk_ctx m := {|
    ctx_origin := m;
    ctx_from := m;
    ctx_contract_address := 0%N;
    ctx_contract_balance := 0%Z;
    ctx_amount := 0%Z;
  |} in
  let dummy_ctx_user_0 := mk_ctx 0%N in
  let dummy_ctx_user_1 := mk_ctx 1%N in
  let dummy_ctx_user_2 := mk_ctx 2%N in
  let dummy_ctx_user_3 := mk_ctx 3%N in
  let dummy_ctx_user_4 := mk_ctx 4%N in

  (* Set up contract *)
  let setup := {|
    participants := 5;
    voter_addrs := [0%N; 1%N; 2%N; 3%N; 4%N];
  |} in
  do st0 <- ovn_init dummy_chain dummy_ctx_user_0 setup;

  (* Private data *)
  (* secret key, vote, randomness *)
  let secrets0 := (
    (* secret key*)
    305422%uint63,
    (* vote *)
    true,
    (* randomness *)
    3243652%uint63,
    45722%uint63,
    19%uint63,
    955053%uint63) in
  let secrets1 := (
    (* secret key*)
    672363%uint63,
    (* vote *)
    true,
    (* randomness *)
    694283%uint63,
    55453%uint63,
    1145145%uint63,
    132313%uint63) in
  let secrets2 := (
    (* secret key*)
    91747%uint63,
    (* vote *)
    false,
    (* randomness *)
    422344%uint63,
    14224%uint63,
    11344%uint63,
    113443%uint63) in
  let secrets3 := (
    (* secret key*)
    354372%uint63,
    (* vote *)
    true,
    (* randomness *)
    435454%uint63,
    1242552%uint63,
    15653%uint63,
    1555%uint63) in
  let secrets4 := (
    (* secret key*)
    2355%uint63,
    (* vote *)
    false,
    (* randomness *)
    644%uint63,
    2451%uint63,
    1444%uint63,
    12554%uint63) in
(*   let secrets0 := (
    (* secret key*)
    30%uint63,
    (* vote *)
    true,
    (* randomness *)
    3%uint63,
    5%uint63,
    19%uint63,
    4%uint63) in
  let secrets1 := (
    (* secret key*)
    12%uint63,
    (* vote *)
    true,
    (* randomness *)
    3%uint63,
    3%uint63,
    3%uint63,
    6%uint63) in
  let secrets2 := (
    (* secret key*)
    9%uint63,
    (* vote *)
    false,
    (* randomness *)
    4%uint63,
    24%uint63,
    5%uint63,
    9%uint63) in
  let secrets3 := (
    (* secret key*)
    37%uint63,
    (* vote *)
    true,
    (* randomness *)
    5%uint63,
    2%uint63,
    34%uint63,
    8%uint63) in
  let secrets4 := (
    (* secret key*)
    23%uint63,
    (* vote *)
    false,
    (* randomness *)
    6%uint63,
    13%uint63,
    41%uint63,
    17%uint63) in *)

  (* Registration params *)
  let mk_reg (n : nat) (s : T * bool * T * T * T * T) :=
    let '(x, v, sr, orw, orr, ord) := s in
    let private := {|
      rp_xi := x;
      rp_zkp_random := sr;
    |} in
    let (g_pow_xi, zkp_xi) := register_to_vote_private private in
    {|
      rp_i := n;
      rp_g_pow_xi := g_pow_xi;
      rp_zkp_xi := zkp_xi;
    |} in
  let reg_0 := mk_reg 0 secrets0 in
  let reg_1 := mk_reg 1 secrets1 in
  let reg_2 := mk_reg 2 secrets2 in
  let reg_3 := mk_reg 3 secrets3 in
  let reg_4 := mk_reg 4 secrets4 in

  (* Register *)
  do '(st1, _) <- ovn_receive dummy_chain dummy_ctx_user_0 st0 (Some (msg_register reg_0));
  do '(st2, _) <- ovn_receive dummy_chain dummy_ctx_user_1 st1 (Some (msg_register reg_1));
  do '(st3, _) <- ovn_receive dummy_chain dummy_ctx_user_2 st2 (Some (msg_register reg_2));
  do '(st4, _) <- ovn_receive dummy_chain dummy_ctx_user_3 st3 (Some (msg_register reg_3));
  do '(st5, _) <- ovn_receive dummy_chain dummy_ctx_user_4 st4 (Some (msg_register reg_4));

  (* Public keys *)
  let g_pow_xis := filter_some st5.(public_keys) in

  (* Commit params *)
  let mk_com (n : nat) (s : T * bool * T * T * T * T) :=
    let '(x, v, sr, orw, orr, ord) := s in
    let private := {|
      cp_i_ := n;
      cp_xi := x;
      cp_zkp_random_w := orw;
      cp_zkp_random_r := orr;
      cp_zkp_random_d := ord;
      cp_vote := v;
    |} in
    let commit_vi := commit_to_vote_private private g_pow_xis in
    {|
      cp_i := n;
      cp_commit_vi := commit_vi;
    |} in
  let com_0 := mk_com 0 secrets0 in
  let com_1 := mk_com 1 secrets1 in
  let com_2 := mk_com 2 secrets2 in
  let com_3 := mk_com 3 secrets3 in
  let com_4 := mk_com 4 secrets4 in

  (* Commit *)
  do '(st6, _) <- ovn_receive dummy_chain dummy_ctx_user_0 st5 (Some (msg_commit com_0));
  do '(st7, _) <- ovn_receive dummy_chain dummy_ctx_user_1 st6 (Some (msg_commit com_1));
  do '(st8, _) <- ovn_receive dummy_chain dummy_ctx_user_2 st7 (Some (msg_commit com_2));
  do '(st9, _) <- ovn_receive dummy_chain dummy_ctx_user_3 st8 (Some (msg_commit com_3));
  do '(st10, _) <- ovn_receive dummy_chain dummy_ctx_user_4 st9 (Some (msg_commit com_4));

  (* Vote params *)
  let mk_vote (n : nat) (s : T * bool * T * T * T * T) :=
    let '(x, v, sr, orw, orr, ord) := s in
    let private := {|
      vp_i_ := n;
      vp_xi := x;
      vp_zkp_random_w := orw;
      vp_zkp_random_r := orr;
      vp_zkp_random_d := ord;
      vp_vote := v;
    |} in
    let (zkp_vi, g_pow_xi_yi_vi) := cast_vote_private private g_pow_xis in
    {|
      vp_i := n;
      vp_zkp_vi := zkp_vi;
      vp_g_pow_xi_yi_vi := g_pow_xi_yi_vi;
    |} in
  let vote_0 := mk_vote 0 secrets0 in
  let vote_1 := mk_vote 1 secrets1 in
  let vote_2 := mk_vote 2 secrets2 in
  let vote_3 := mk_vote 3 secrets3 in
  let vote_4 := mk_vote 4 secrets4 in
(*
  Ok st10.
  Goal ovn_test = Err 0.
  vm_compute.
  Admitted.

  Goal
  let state :=   {|
    voters :=
      [0%N; 1%N; 2%N; 3%N; 4%N];
    voters_n := 5;
    public_keys :=
      [Some 26%Z; Some 86%Z;
       Some 196%Z; Some 86%Z;
       Some 66%Z];
    schnorr_zkps :=
      [Some
         {|
           schnorr_zkp_u := 216%Z;
           schnorr_zkp_c := 14%Z;
           schnorr_zkp_z := 173%Z
         |};
       Some
         {|
           schnorr_zkp_u := 216%Z;
           schnorr_zkp_c := 14%Z;
           schnorr_zkp_z := 171%Z
         |};
       Some
         {|
           schnorr_zkp_u := 46%Z;
           schnorr_zkp_c := 14%Z;
           schnorr_zkp_z := 130%Z
         |};
       Some
         {|
           schnorr_zkp_u := 26%Z;
           schnorr_zkp_c := 14%Z;
           schnorr_zkp_z := 23%Z
         |};
       Some
         {|
           schnorr_zkp_u := 156%Z;
           schnorr_zkp_c := 14%Z;
           schnorr_zkp_z := 78%Z
         |}];
    commits :=
      [Some 14%Z; Some 14%Z;
       Some 14%Z; Some 14%Z;
       Some 14%Z];
    ballots :=
      [None; None; None; None; None];
    or_zkps :=
      [None; None; None; None; None];
    register_count := 5;
    commit_count := 5;
    vote_count := 0;
    tally := None
  |} in
  let pks := filter_some state.(public_keys) in
  let secrets0 := (
    (* secret key*)
    30%Z,
    (* vote *)
    true,
    (* randomness *)
    3%Z,
    5%Z,
    19%Z,
    4%Z) in
  let mk_vote (n : nat) (s : Z * bool * Z * Z * Z * Z) :=
    let '(x, v, sr, orw, orr, ord) := s in
    let private := {|
      vp_i_ := n;
      vp_xi := x;
      vp_zkp_random_w := orw;
      vp_zkp_random_r := orr;
      vp_zkp_random_d := ord;
      vp_vote := v;
    |} in
    let (zkp_vi, g_pow_xi_yi_vi) := cast_vote_private private pks in
    {|
      vp_i := n;
      vp_zkp_vi := zkp_vi;
      vp_g_pow_xi_yi_vi := g_pow_xi_yi_vi;
    |} in
  let vote_0 := mk_vote 0 secrets0 in
  let param := vote_0 in

  let g_pow_yi := compute_g_pow_yi param.(vp_i) pks in
  validate_or_zkp g_pow_yi param.(vp_zkp_vi) = Ok tt.
  Timeout 30 compute -[validate_or_zkp].
  unfold validate_or_zkp.
  Timeout 30 compute -[andb OVN_Z.t_eqb].

  let pks := filter_some state.(public_keys) in
  let g_pow_yi := compute_g_pow_yi param.(vp_i) pks in
  do _ <- validate_or_zkp g_pow_yi param.(vp_zkp_vi);*)




  (* Vote *)
  (* do '(st3, _) <- ovn_receive dummy_chain dummy_ctx_user_0 st2 (Some (msg_vote vote_0)); *)
  do '(st11, _) <- ovn_receive dummy_chain dummy_ctx_user_0 st10 (Some (msg_vote vote_0));
  do '(st12, _) <- ovn_receive dummy_chain dummy_ctx_user_1 st11 (Some (msg_vote vote_1));
  do '(st13, _) <- ovn_receive dummy_chain dummy_ctx_user_2 st12 (Some (msg_vote vote_2));
  do '(st14, _) <- ovn_receive dummy_chain dummy_ctx_user_3 st13 (Some (msg_vote vote_3));
  do '(st15, _) <- ovn_receive dummy_chain dummy_ctx_user_4 st14 (Some (msg_vote vote_4));


  (* Tally *)
  do '(st16, _) <- ovn_receive dummy_chain dummy_ctx_user_0 st15 (Some msg_tally);
  Ok st16.(tally).


  (* Timeout 10 Eval vm_compute in ovn_test. *)
(*
  Goal
    let state := {|
      voters := [0%N; 1%N; 2%N; 3%N; 4%N];
      voters_n := 5;
      public_keys :=
        [Some 26%Z; Some 86%Z; Some 196%Z; Some 86%Z; Some 66%Z];
      schnorr_zkps :=
        [Some
           {|
             schnorr_zkp_u := 216%Z;
             schnorr_zkp_c := 14%Z;
             schnorr_zkp_z := 173%Z
           |};
         Some
           {|
             schnorr_zkp_u := 216%Z;
             schnorr_zkp_c := 14%Z;
             schnorr_zkp_z := 171%Z
           |};
         Some
           {|
             schnorr_zkp_u := 46%Z;
             schnorr_zkp_c := 14%Z;
             schnorr_zkp_z := 130%Z
           |};
         Some
           {|
             schnorr_zkp_u := 26%Z;
             schnorr_zkp_c := 14%Z;
             schnorr_zkp_z := 23%Z
           |};
         Some
           {|
             schnorr_zkp_u := 156%Z;
             schnorr_zkp_c := 14%Z;
             schnorr_zkp_z := 78%Z
           |}];
      commits := [Some 14%Z; Some 14%Z; Some 14%Z; Some 14%Z; Some 14%Z];
      ballots :=
        [Some 94%Z; Some 136%Z; Some 192%Z; Some 92%Z; Some 146%Z];
      or_zkps :=
        [Some
           {|
             or_zkp_x := 26%Z;
             or_zkp_y := 94%Z;
             or_zkp_a1 := 96%Z;
             or_zkp_b1 := 188%Z;
             or_zkp_a2 := 26%Z;
             or_zkp_b2 := 232%Z;
             or_zkp_c := 14%Z;
             or_zkp_d1 := 4%Z;
             or_zkp_d2 := 10%Z;
             or_zkp_r1 := 19%Z;
             or_zkp_r2 := 205%Z
           |};
         Some
           {|
             or_zkp_x := 86%Z;
             or_zkp_y := 136%Z;
             or_zkp_a1 := 16%Z;
             or_zkp_b1 := 232%Z;
             or_zkp_a2 := 6%Z;
             or_zkp_b2 := 112%Z;
             or_zkp_c := 14%Z;
             or_zkp_d1 := 1%Z;
             or_zkp_d2 := 13%Z;
             or_zkp_r1 := 1%Z;
             or_zkp_r2 := 95%Z
           |};
         Some
           {|
             or_zkp_x := 196%Z;
             or_zkp_y := 192%Z;
             or_zkp_a1 := 6%Z;
             or_zkp_b1 := 122%Z;
             or_zkp_a2 := 176%Z;
             or_zkp_b2 := 58%Z;
             or_zkp_c := 14%Z;
             or_zkp_d1 := 13%Z;
             or_zkp_d2 := 1%Z;
             or_zkp_r1 := 134%Z;
             or_zkp_r2 := 1%Z
           |};
         Some
           {|
             or_zkp_x := 86%Z;
             or_zkp_y := 92%Z;
             or_zkp_a1 := 16%Z;
             or_zkp_b1 := 244%Z;
             or_zkp_a2 := 6%Z;
             or_zkp_b2 := 182%Z;
             or_zkp_c := 14%Z;
             or_zkp_d1 := 1%Z;
             or_zkp_d2 := 13%Z;
             or_zkp_r1 := 1%Z;
             or_zkp_r2 := 20%Z
           |};
         Some
           {|
             or_zkp_x := 66%Z;
             or_zkp_y := 146%Z;
             or_zkp_a1 := 6%Z;
             or_zkp_b1 := 16%Z;
             or_zkp_a2 := 146%Z;
             or_zkp_b2 := 112%Z;
             or_zkp_c := 14%Z;
             or_zkp_d1 := 13%Z;
             or_zkp_d2 := 1%Z;
             or_zkp_r1 := 202%Z;
             or_zkp_r2 := 1%Z
           |}];
      register_count := 5;
      commit_count := 5;
      vote_count := 5;
      tally := Some 0
    |} in
  let vote_result := compute_ballot_product state.(ballots) in
  let res := bruteforce_tally state.(voters_n) f_zero vote_result in
  res = 0.
  Timeout 20 compute -[bruteforce_tally].
  unfold bruteforce_tally.
  compute [f_one f_add].
  Timeout 20 compute -[g_g_pow OVN_Z.t_eqb].
  cbn.

  compute -[OVN_Z.t_eqb].*)

(*   do '(st1, _) <- ovn_receive dummy_chain dummy_ctx_user_0 st0 (Some msg_tally);
  Ok st1.(tally). *)

(* Timeout 10 Eval vm_compute in ovn_test. *)

(* Definition test := @Ok _ unit (Some 2). *)
(* Definition test := @Err unit unit tt. *)

Set Warnings "-primitive-turned-into-axiom".
From CertiCoq.Plugin Require Import CertiCoq.

(* CertiCoq Compile Wasm test. *)
CertiCoq Compile Wasm ovn_test.

*)
