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


(* Proof by simplification *)
(* How to state and prove properties of their behavior? *)

Theorem plus_0_n : forall n : nat, 0 + n = n.
Proof.
  intros n. reflexivity. Qed.
(* 0 is a "neutral element" for + on the left
    is proved by just observing that 0 + n reduces to n
    no matter what n is, a fact that can be read directly 
    off the definition of plue *)

(* difference: we used Theorem instead of Example
    which is just a matter of style.
    Theorem, Example, Lemma, Fact, Remark mean the same thing *)

(* intros n moves the quantifier from the goal to a "context"
    of current assumptions. It's the same as saying
    "Suppose n is some arbitrary number." *)

Theorem plus_n_0: forall n, n + 0 = n.
Proof.
  simpl. (* doesn't do anything *)
Abort.

(* because the subgoal doesn't change into evaluating
    n+0 in this case *)

Theorem plus_1_1 : forall n : nat, 1 + n = S n.
Proof.
  intros n. reflexivity. Qed.

Theorem mult_0_1: forall n : nat, 0 × n = 0.
Proof.
  intros n. reflexivity. Qed.


(* Proof by Rewriting *)

Theorem plus_id_example : forall n m:nat,
  n = m ->
  n + n = m + m.

(* specialized property that holds only when m = n.
    the -> symbol means "implies" *)

(* since m and n are arbitrary numbers, we cannot just use
    simplification to prove this theorem. 
   We prove it by observing that if n = m, 
    we can replace n with m in the goal and obtain equality.
  This tactic in Coq is called rewrite *)
Proof.
  intros n m. (* move both quantifiers into the context *)
  intros H. (* move the hypothesis into the context n = m *)
  rewrite -> H. (* rewrite the goal to m+m = m+m using the hypothesis *)
  (* you could do rewrite <- H and see what happens. 
    basically it changes to n + n = n + n*)  
  reflexivity. Qed.

(* Exercise - plus_id exercise *)
Theorem plus_id_exercise: forall n m o: nat, 
  n = m -> m = o -> n + m = m + o.
Proof.
  intros n m o.
  intros H.
  rewrite -> H.
  intros I.
  rewrite -> I.
  reflexivity. Qed.

Theorem mult_0_plus : forall n m: nat,
  (0 + n) × m = n × m.
Proof.
  intros n m.
  rewrite -> plus_0_n.
  reflexivity. Qed.
(* using the rewrite tactic with a previously proved theorem
    rather than a hypothesis from the context *)

(* Exercise mult_S_1 *)
Theorem mult_S_1 : forall n m : nat,
  m = S n ->
  m × (1 + n) = m × m.
Proof.
  intros n m.
  intros H.
  rewrite -> H.
  reflexivity.
  Qed.

(* Proof by Case Analysis *)
(* trying to prove the following using simpl. will get stuck *)
Theorem plus_1_neq_0_firsttry : forall n : nat,
  beq_nat (n + 1) 0 = false.
Proof.
  intros n.
  simpl. (* does nothing! *) 
Abort.
(* definitions of beq_nat and + begin by performing a match
    but here, the first arg to + is the unknown n, and the
    arg to beq_nat is the compound expression n+1.
    they cannot be simplified *)

(* consider the possible forms of n separately.
    If n is O, then we can calculate beq_nat(n+1) 0 and check false
    If n = S n' for some n', we don't know what n+1 is, but
      we can at least calculate it will begin with one S,
      that's close enought to calculate beq_nat(n+1) 0 = false.
*)

Theorem plus_1_neq_0 : forall n : nat,
  beq_nat (n + 1) 0 = false.
Proof.
  intros n. destruct n as [ | n'].
    reflexivity.
    reflexivity.
  Qed.

(* destruct generates cases where n = O where n = S n'.
    generates two goals that gets proved separately, 
    in order to get Coq to accept the Thm as proved *)

(* as [ | n'] is an intro pattern. It wells Coq what
    varnames to introduce in each subgoal.
    a list of names separated by | gets generated.
    Here, the first component is emptyu, since O is nullary.
    The second component gives a single name n', since S is a unary constructor
*)

Theorem negb_involutive : forall b : bool,
  negb (negb b) = b.
Proof.
  intros b. destruct b.
  reflexivity.
  reflexivity.
Qed.

(* Exercise - zero_nbeq_plus_1 *)
Theorem zero_nbeq_plus_1 : forall n : nat,
  beq_nat 0 (n + 1) = false.
Proof.
  intros n.
  destruct n.
  reflexivity.
  reflexivity.
Qed.

(* More exercises *)
Theorem identity_fn_applied_twice :
  forall (f: bool -> bool),
  (forall (x: bool), f x = x) ->
  forall (b : bool), f (f b) = b.
Proof.
  intros.
  rewrite -> H.
  rewrite -> H.
  reflexivity.
Qed.

Theorem negation_fn_applied_twice :
  forall (f: bool -> bool),
  (forall (x: bool), f x = negb x) ->
  forall (b : bool), f (f b) = b.
Proof. 
  intros.
  rewrite -> H.
  rewrite -> H.
  destruct b.
  compute.
  reflexivity.
  compute.
  reflexivity.
Qed.
  

Theorem andb_eq_orb :
  forall(b c : bool),
  (andb b c = orb b c) ->
  b = c.
Proof.
  intros b c.
  destruct b.
  destruct c.
  compute.
  reflexivity.
  compute.
  intro H.
  rewrite -> H.
  reflexivity.
  destruct c.
  compute.
  intro H.
  rewrite -> H.
  reflexivity.
  compute.
  reflexivity.
Qed.

(* Exercise - binary *)
Inductive bin : Type :=
  | SO   : bin
  | S1  : bin -> bin
  | S2  : bin -> bin.

Fixpoint incr (b : bin) : bin :=
  match b with
  | SO => S2 SO
  | S1 n => S2 n
  | S2 n => S1 (incr n)
  end.

Fixpoint bin_to_nat (b : bin) : nat :=
  match b with
  | SO => 0
  | S1 n => 2 × (bin_to_nat n)
  | S2 n => 1 + (2 × (bin_to_nat n))
  end.

Fixpoint nat_to_bin (n : nat) : bin :=
  match n with 
  | O => SO
  | S n' => incr (nat_to_bin n')
end.

Theorem bin_correct :
  forall n : nat,
  forall b : bin,
  (nat_to_bin n = b) ->
  (bin_to_nat b = n).

