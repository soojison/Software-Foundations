(* March 1st, 2016. We skipped a lot of chapters *)

Inductive list (A:Type) : Type :=
  | Nil : list A
  | Cons : A -> list A -> list A.

Inductive ev : nat -> Prop :=
  | ev_0: ev 0 (* constructor declaration *)
  | ev_SS: forall (n:nat), ev n -> ev (S (S n)). (* also a constructor *)

Theorem ev_example : ev 0.
Proof.
  apply ev_0.
Qed.

Theorem ev_example_nonzero : ev 14.
Proof.
  repeat apply ev_SS.
  apply ev_0.
Abort.

(* What's different from evenb *)
Fixpoint evenb (n:nat) : bool :=
  match n with
  | 0 => true
  | S 0 => false
  | S (S n) => evenb n
end.

Fixpoint even (n:nat) : Prop := evenb n = true.

Theorem even_ex : even 0.
Proof.
  simpl.
  reflexivity.
Qed.

Theorem even_ex_bad : even 1.
Proof.
  simpl.
Abort.

Theorem even_ex_big : even 14.
Proof.
  simpl.
  auto.
Qed.

(* Inference rule: bottom conclusion, top hypothesis

          ev n
------  ----------
 ev 0    ev (n+2)

*)

Inductive beautiful : nat -> Prop :=
| b_0 : beautiful 0
| b_3 : beautiful 3
| b_5 : beautiful 5
| b_sum : forall n m, beautiful n -> beautiful m -> beautiful (n+m).


(*
                               beautiful n beautiful m
-------- ---------   --------  ------------------------
  b_0      b_3         b_5         beautiful(n+m)

*)

Theorem b_times2: forall n, beautiful n -> beautiful (2 * n).
Proof.
  intros n beau. (* premises to a lemma *)
  apply b_sum.
  apply beau.
  apply b_sum.
  apply beau.
  apply b_0.
Qed.

(* when to use computational vs. inductive definitions? *)
(* Inductive defs are more flexible than computational ones *)


