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
    
(* convenient to be able to simply state and prove
    the neede "sub-theorem" where it's used. 
    This is where assert comes in *)

Theorem mult_0_plus' : forall n m: nat,
  (0 + n) × m = n × m.
Proof.
  intros n m.
  assert (H: 0 + n = n).
    Case "Proof of assertion".
      reflexivity.
  rewrite -> H.
  reflexivity.
Qed.

(* assert introduces two sub-goals.
    The assertion itself (by prefixing it with H:)
    The same as the one at the point we invoke assert
      in the context, we have the assumption H.
  So, assert generates one subgoal where we must
    prove the asserted fact and a second subgoal  
    where we can use the asserted fact to make progress
*)
(* ex. (n + m) + (p + q) = (m + n) + (p + q).
    rewrite command is dumb when it comes to the
    location where it applies.
*)
Theorem plus_rearrange_firsttry : forall n m p q : nat,
  (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros n m p q.
  rewrite -> plus_comm.
Abort.

(* we introduce a local lemma stating that
    m + n = n + m.
*)
Theorem plus_rearrange : forall n m p q : nat,
  (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros n m p q.
  assert (H: n + m = m + n).
    Case "Proof of assertion".
    rewrite -> plus_comm.
    reflexivity.
  rewrite -> H.
  reflexivity.
Qed.
  

Theorem plus_swap : forall n m p : nat,
  n + (m + p) = m + (n + p).
Proof.
  intros n m p.
  rewrite -> plus_comm.
  rewrite <- plus_assoc.
  assert (H: p + n = n + p).
    rewrite -> plus_comm.
    reflexivity.
  rewrite -> H.
  reflexivity.
Qed.

Theorem mult_0 : forall n, 
  n*0 = 0.
Proof.
  intros n.
  induction n as [|n'].
    reflexivity.
    simpl.
    rewrite -> IHn'.
    reflexivity.
Qed.

Theorem mult_1: forall n, 
  n*1 = n.
Proof.
  intros n. induction n as [|n'].
  simpl.
  reflexivity.
  simpl.
  rewrite -> IHn'.
  reflexivity.
Qed.

Theorem mult_comm_lemma : forall n m,
  m * S n = m + m * n.
Proof.
  intros n m.
  induction m as [|m'].
  Case "m = 0".
    simpl.
    reflexivity.
  Case "m != 0".
    simpl.
    rewrite -> plus_swap.
    rewrite -> IHm'.
    reflexivity.
Qed.
  
Theorem mult_comm : forall m n : nat,
  m × n = n × m.
Proof.
  intros n m.
  induction n as [|n'].
  Case "0".
    simpl.
    rewrite -> mult_0.
    reflexivity.
  Case "S n'".
    simpl.
    rewrite -> IHn'.
    rewrite -> mult_comm_lemma.
    reflexivity.
Qed.


(* More Exercises *)

(* reading group stuff *)
Check nat_ind.
(* 
nat_ind
     : forall P : nat -> Prop,
       P 0 -> (forall n : nat, P n -> P (S n)) -> forall n : nat, P n

  - this is natural number induction principle
*)
Print nat_ind.
(*
=> arg of lamda  and body of lambda separate
-> arrow for type
*)

(* Proof is just a program! *)
(* Induction is not built in but you make it work by definitions *)
Print nat_rect.

Inductive list (A:Set) : Set :=
  | Nil : list A
  | Cons : A -> list A -> list A. (* rightmost arrow: return type, left: args *)
Check list_ind.
(* form of list is identical to form of nats *)
(* proposition for inner part of the list holds -> can show
  it works for cons'ing arbitrary a on the list *)

(*
  Cons 0 : list A -> list A.
    HOFuns....
  Cons : A x list A -> list A (we pass in a "pair")
*)

Inductive Foo : Set :=
  | A : Foo (* a is a constant of type Foo *)
  | B : nat -> Foo -> Foo -> Foo (* func that produces Foo *)
  | C : Foo -> list Foo -> Foo
  | D : Foo.

(* induction proof involving Foo
    induction on Foo -> 3 cases
      A: base case. Foo is Foo
      B: shape of Foo obj is B.
          get 2 inductive hypotheses
      C: shape of Foo object is C.
          C f l -> that whole thing is type Foo
          f is a smaller instance of Foo.
          induction hypothesis over f.
            my claim holds over this f.
*)

Check Foo_ind.

(*
  prove that my proposition holds for A
  Foo has form B n f0 f1 -> assume that P HOLDS FOR F0 AND F1, N IS ARBITRARY NATURAL NUMBER.
  C has form C f1 l -> assume P holds for f, l = arbitrary list.
  prove that my prop holds for D
 *)