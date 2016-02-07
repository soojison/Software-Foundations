(* Declaration - defining a new set of data values, a type *)
Inductive day : Type :=
  | monday    : day
  | tuesday   : day
  | wednesday : day
  | thursday  : day
  | friday    : day
  | saturday  : day
  | sunday    : day.

(* the type is called "day", and its members are MTWTF...*)

(* Function that operates on days *)
Definition next_weekday (d:day) : day :=
  match d with
    | monday    => tuesday
    | tuesday   => wednesday
    | wednesday => thursday
    | thursday  => friday
    | friday    => monday
    | saturday  => monday
    | sunday    => monday
  end.

(* argument types and return types are explicitly declared *)

Eval compute in (next_weekday friday).
Eval compute in (next_weekday (next_weekday saturday)).

(* record what we expect the result to be in the form of example *)
Example test_next_weekday:
  (next_weekday (next_weekday saturday)) = tuesday.
(* makes an assertion, and gives the assertion a name *)

(* ask Coq to verify it *)
Proof. simpl. reflexivity. Qed.
(* basically says that the assertion we've just made can be proved
  by observing that both sides of the equality evaluate to the same thing *)

(* we can ask Coq to extract from the Definition a program
  in some other pg. lgs. such as OCaml, Scheme, Haskell *)

(* defining standard type bool of booleans *)
Inductive bool : Type :=
  | true  : bool
  | false : bool.

(* functions over booleans *)
Definition negb (b:bool) : bool :=
  match b with 
  | true  => false
  | false => true
  end.

Definition andb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => b2
  | false => false
  end.

Definition orb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => true
  | false => b2
  end.

(* "unit tests" *)
Example test_orb1: (orb true false) = true.
Proof. reflexivity. Qed.
Example test_orb2: (orb false false) = false.
Proof. reflexivity. Qed.
Example test_orb3: (orb false true) = true.
Proof. reflexivity. Qed.
Example test_orb4: (orb true true) = true.
Proof. reflexivity. Qed.
(* notice how we dropped simpl. in the proofs.
  this is because reflexivity automatically performs simplification *)

(* Exercise - nandb *)
Definition nandb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => (negb b2)
  | false => true
  end.

Example test_nandb1: (nandb true false) = true.
Proof. reflexivity. Qed.
Example test_nandb2: (nandb false false) = true.
Proof. reflexivity. Qed.
Example test_nandb3: (nandb false true) = true.
Proof. reflexivity. Qed.
Example test_nandb4: (nandb true true) = false.
Proof. reflexivity. Qed.

(* Exercise - andb3 *)
Definition andb3 (b1:bool) (b2:bool) (b3:bool) : bool :=
  match b1 with
  | true => (andb b2 b3)
  | false => false
  end.
Example test_andb31: (andb3 true true true) = true.
Proof. reflexivity. Qed.
Example test_andb32: (andb3 false true true) = false.
Proof. reflexivity. Qed.
Example test_andb33: (andb3 true false true) = false.
Proof. reflexivity. Qed.
Example test_andb34: (andb3 true true false) = false.
Proof. reflexivity. Qed.

(* Function types *)
(* check command causes Coq to print the type of an expression *)
Check true.
(* ===> true : bool *)
Check (negb true).
(* ===> negb true : bool *)

(* functions are also data values - function types *)
Check negb.
(* ===> negb : bool -> bool *)

(* Numbers *)
(* digression: if we disclose declarations between Module X and End X, 
  the definitions will be refered by X.foo. We use type nat so that it
  does not shadow the one from the standard library *)
Module Playground1.

(* instead of giving enumerated types, we give inductive rules for elements *)
Inductive nat : Type :=
  | O : nat
  | S : nat -> nat.
(* O is a natural number
  S is a constructor that takes a natural number and yields another one *)

(* O e nat
  if n e nat, S n e nat
  expressions formed in these two ways are the only ones belonging to the set nat *)

(* Functions taht pattern match on natural numbers *)
Definition pred (n : nat) : nat :=
  match n with 
  | O => O
  | S n' => n' (* if n has the form S n' for some n', return n' *)
  end.

End Playground1.

Definition minustwo (n:nat) : nat :=
  match n with
  | O => O
  | S O => O
  | S (S n') => n'
  end.

Check (S (S (S (S O)))). (* not sure what's happening here.. how does it get 4*)
Eval compute in (minustwo 5).
Check S.
Check pred.
Check minustwo.
(* functions like pred and minustwo come with computation rules *)
(* but S has no such behavior attached, it doesn't do anything at all *)

(* we need to use recursion for most function definitions over numbers *)
Fixpoint evenb (n:nat) : bool :=
  match n with
  | O => true
  | S O => false
  | S (S n') => evenb n'
  end.

Fixpoint oddb (n:nat) : bool := negb(evenb n).

Example test_oddb1: (oddb (S O)) = true. (* oooh i see, so (S O) constructs a nat*)
Proof. reflexivity. Qed.
Example test_oddb2: (oddb (S (S (S (S O))))) = false.
Proof. reflexivity. Qed. (* oh no this is like scheme *)

(* multi argument functions by recursion *)
Module Playground2.

Fixpoint plus (n:nat) (m:nat) : nat :=
  match n with
  | O => m  (* base case *)
  | S n' => S (plus n' m) (* recursive case *)
  end.

Eval compute in (plus (S (S (S O))) (S (S O))).
(*  plus (S (S (S O))) (S (S O))    
==> S (plus (S (S O)) (S (S O))) by the second clause of the match
==> S (S (plus (S O) (S (S O)))) by the second clause of the match
==> S (S (S (plus O (S (S O))))) by the second clause of the match
==> S (S (S (S (S O))))          by the first clause of the match
*)

(* if two or more args have the same type, they can be written together *)
Fixpoint mult (n m:nat) : nat :=
  match n with
  | O => O
  | S n' => plus m (mult n' m)
  end.
(* recursive define so that we add n m times *)

Example test_mult1: (mult 3 3) = 9.
Proof. reflexivity. Qed.

(* match two expressions at once by putting a comma between them *)
Fixpoint minus (n m:nat) : nat :=
  match n, m with
  | O , _ => O (* 0 minus something is 0 in nat world *)
  | S _ , O => n (* nonzero minus 0 is the original number *)
  | S n', S m' => minus n' m' (* if not, we subtract *)
  end.
(* _ is a wildcard pattern. same as writing some variable that doesn't get used
  on the right hand side. This avoids the need to invent a bogus var name *)

End Playground2.

Fixpoint exp (base power : nat) : nat :=
  match power with
  | O => S O
  | S p => mult base (exp base p)
  end.

(* Exercise - factorial *)
Fixpoint factorial (n:nat) : nat :=
  match n with
  | O => S O (* factorial(0) = 1 *)
  | S n' => mult n (factorial n')
  end.

Example test_factorial1: (factorial 3) = 6.
Proof. reflexivity. Qed.
Example test_factorial2: (factorial 5) = (mult 10 12).
Proof. reflexivity. Qed.

(* we can make numerical expressions a little easier by introducing
    "notations" for addition, multiplication, subtraction *)
Notation "x + y" := (plus x y).
Notation "x - y" := (minus x y).
Notation "x × y" := (mult x y)
                      (at level 40, left associativity)
                      :nat_scope.

Check ((0 + 1) + 1).

(* equality testing for numbers is not natively defined *)
(* beq_nat test natural #s for equality, yielding a boolean *)
Fixpoint beq_nat (n m: nat): bool :=
  match n with
  | O => match m with
         | O => true
         | S m' => false
         end
  | S n' => match m with
            | O => false
            | S m' => beq_nat n' m'
            end
  end.
(* we could have used simultaneous match like minus *)

(* ble_nat tests natural #s for less or equal, yielding a boolean *)
Fixpoint ble_nat (n m : nat) : bool :=
  match n with
  | O => true
  | S n' =>
      match m with 
      | O => false
      | S m' => ble_nat n' m'
      end
  end.

Example test_ble_nat1: (ble_nat 2 2) = true.
Proof. reflexivity. Qed.
Example test_ble_nat2: (ble_nat 2 4) = true.
Proof. reflexivity. Qed.
Example test_ble_nat3: (ble_nat 4 2) = false.
Proof. reflexivity. Qed.

(* Exercise - blt_nat *)

(* tests natural numbers for less than yielding a boolean *)
Definition blt_nat (n m : nat) : bool := 
  (andb (negb (beq_nat n m)) (ble_nat n m)).

Example test_blt_nat1: (blt_nat 2 2) = false.
Proof. reflexivity. Qed.
Example test_blt_nat2: (blt_nat 2 4) = true.
Proof. reflexivity. Qed.
Example test_blt_nat3: (blt_nat 4 2) = false.
Proof. reflexivity. Qed.
Example test_blt_nat4: (blt_nat 1 2) = true.
Proof. reflexivity. Qed.



























