Require Export cpt1basics.

(*
  It's hard to be organized in larger proofs. 
  So we define Cases!
*)

Require String. Open Scope string_scope.

Ltac move_to_top x :=
  match reverse goal with
  | H : _ |- _ => try move x after H
  end.

Tactic Notation "assert_eq" ident(x) constr(v) :=
  let H := fresh in
  assert (x = v) as H by reflexivity;
  clear H.

Tactic Notation "Case_aux" ident(x) constr(name) :=
  first [
    set (x := name); move_to_top x
  | assert_eq x name; move_to_top x
  | fail 1 "because we are working on a different case" ].

Tactic Notation "Case" constr(name) := Case_aux Case name.
Tactic Notation "SCase" constr(name) := Case_aux SCase name.
Tactic Notation "SSCase" constr(name) := Case_aux SSCase name.
Tactic Notation "SSSCase" constr(name) := Case_aux SSSCase name.
Tactic Notation "SSSSCase" constr(name) := Case_aux SSSSCase name.
Tactic Notation "SSSSSCase" constr(name) := Case_aux SSSSSCase name.
Tactic Notation "SSSSSSCase" constr(name) := Case_aux SSSSSSCase name.
Tactic Notation "SSSSSSSCase" constr(name) := Case_aux SSSSSSSCase name.

(* Example of how Case is used *)
Theorem andb_true_elim1 : forall b c : bool,
  andb b c = true -> b = true.
Proof.
  intros b c H.
  destruct b.
  Case "b = true". (* <----- here *)
    reflexivity.
  Case "b = false". (* <---- and here *)
    rewrite <- H.
    reflexivity.
Qed.

(* Case simply adds a string that we choose to the context
  for the curernt coal. When subgoals are generated, this string
  is carried over into their contexts *)


(* Exercise - andb_true_elim2 *)

(* Prove andb_true_eli2, marking cases when you use destruct *)

Theorem andb_true_elim2 : forall b c : bool,
  andb b c = true -> c = true.
Proof.
  intros b c H.
  destruct c.
  Case "c = true".
    reflexivity.
  Case "c = false".
    rewrite <- H.
    destruct b.
    reflexivity.
    reflexivity.
Qed.

(* Proof by Induction *)

Theorem plus_0_r_firsttry : forall n:nat,
  n + 0 = n.

(* this cannot be proved in the same simple way *)

Proof.
  intros n.
  simpl. (* Does nothing! *)
Abort.

(* reasoning by destruct doesn't do much either *)
(* since n can be arbitrarily large, we will never be done *)
Theorem plus_0_r_secondtry : forall n:nat,
  n + 0 = n.
Proof.
  intros n.
  destruct n as [| n'].
  Case "n = 0".
    reflexivity. (* so far so good *)
  Case "n = S n'".
    simpl. (*STUCK!*)
Abort.

(* This is where we use induction! *)

(* If P(n) is some proposition involving a natural number n
  and we want to show that P holds for all numbers n
    show that P(0) holds
    show that for any n', if P(n') holds, so does P(S n')
    conclude that P(n) holds for all n
*)

(* In Coq, the steps are the same, but the order is backwards!
    Prove P(n) for all n by breaking down into two separate subgoals
      show P(0)
      show P(n') -> P(S n')
*)

Theorem plus_0_r : forall n:nat,
  n+0 = n.
Proof.
  intros n.
  induction n as [| n'].
  Case "n = 0".
    reflexivity.
  Case "n = S n'".
    simpl.
    rewrite -> IHn'. (* what is IHn'? -> Induction hypothesis for n' *)
    reflexivity.
Qed.

Theorem minus_diag : forall n,
  minus n n = 0.
Proof.
  intros n.
  induction n as [|n'].
  Case "n = 0".
    simpl.
    reflexivity.
  Case "n = S n'".
    simpl.
    rewrite -> IHn'.
    reflexivity.
Qed.

(* Exercise - basic_induction *)

Theorem mult_0_r : forall n:nat,
  n × 0 = 0.
Proof.
  intros n.
  induction n as [|n'].
  Case "n = 0".
    simpl.
    reflexivity.
  Case "n = S n'".
    simpl.
    rewrite -> IHn'.
    reflexivity.
Qed.

Theorem plus_n_Sm : forall n m : nat,
  S (n + m) = n + (S m).
Proof.
  intros n m.
  induction n as [|n'].
  Case "n = 0".
    simpl.
    reflexivity.
  Case "n = S n'".
    simpl.
    rewrite -> IHn'.
    reflexivity.
Qed.

Theorem plus_comm : forall n m : nat,
  n + m = m + n.
Proof.
  intros n m.
  induction n as [|n'].
  Case "0".
    simpl.
    rewrite -> plus_0_r.
    reflexivity.
  Case "S n'".
    simpl.
    rewrite <- plus_n_Sm.
    rewrite -> IHn'.
    reflexivity.
Qed.

Theorem plus_assoc : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  intros n m p.
  induction n as [|n'].
  Case "0".
    simpl.
    reflexivity.
  Case "S n'".
    simpl.
    rewrite -> IHn'.
    reflexivity.
Qed.

(* Exercise - double_plus *)

Fixpoint double (n : nat) :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.

(* Use induction to prove this simple fact about double *)
Lemma double_plus : forall n,
  double n = n + n.
Proof.
  intros n.
  induction n as [|n'].
  Case "n = 0".
    simpl.
    reflexivity.
  Case "n = S n'".
    simpl.
    rewrite <- plus_comm.
    simpl.
    rewrite -> IHn'.
    reflexivity.
Qed.

(* Proofs within proofs *)
    

