Require Export cpt3structureddata.

(* Polymorphism *)
(* Polymorphic lists *)

(* new inductive datatype? we can do polymorphic inductive type defs! *)
Inductive list (X:Type) : Type :=
| nil : list X
| cons : X -> list X -> list X.

(* Exactly like the def. of natlist but nat arg is replaced with arbitary X *)

Check nil.
Check cons.

(* Now we can make polymorphic or "generic" versions of all list funcs! *)

Fixpoint length (X:Type) (l:list X) : nat :=
  match l with
    | nil _ => 0 (* underscore added since arg is noninformative *)
    | cons _ h t => S (length X t) (* some update in coq version i think *)
  end.

Example test_length1 :
    length nat (cons nat 1 (cons nat 2 (nil nat))) = 2.
Proof. reflexivity. Qed.
Example test_length2 :
    length bool (cons bool true (nil bool)) = 1.
Proof. reflexivity. Qed.

Fixpoint app (X : Type) (l1 l2 : list X)
                : (list X) :=
  match l1 with
  | nil _ => l2
  | cons _ h t => cons X h (app X t l2)
  end.

Fixpoint snoc (X:Type) (l:list X) (v:X) : (list X) :=
  match l with
  | nil _ => cons X v (nil X)
  | cons _ h t => cons X h (snoc X t v)
  end.

Fixpoint rev (X:Type) (l:list X) : list X :=
  match l with
  | nil _ => nil X
  | cons _ h t => snoc X (rev X t) h
  end.

Example test_rev1 :
    rev nat (cons nat 1 (cons nat 2 (nil nat)))
  = (cons nat 2 (cons nat 1 (nil nat))).
Proof. reflexivity. Qed.

Example test_rev2:
  rev bool (nil bool) = nil bool.
Proof. reflexivity. Qed.

Module MumbleBaz.

  Inductive mumble : Type :=
  | a : mumble
  | b : mumble -> nat -> mumble
  | c : mumble.
  Inductive grumble (X:Type) : Type :=
  | d : mumble -> grumble X
  | e : X -> grumble X.

  (* Exercise 2 baz_num_elts *)

  Inductive baz : Type :=
  | x : baz -> baz
  | y : baz -> bool -> baz.

End MumbleBaz.

(* Type annotation inference *)

Fixpoint app' X l1 l2 : list X :=
  match l1 with
  | nil _      => l2
  | cons _ h t => cons X h (app' X t l2)
  end.

(* What type did Coq assign to app'? *)
Check app'.
Check app.

(* Type argument synthesis *)

Fixpoint length' (X:Type) (l:list X) : nat :=
  match l with
    | nil _ => 0
    | cons _ h t => S (length' _ t)
  end.
(* length using implicit args *)

(* Implicit args *)

Arguments nil {X}.
Arguments cons {X} _ _.
Arguments length {X} l.
Arguments app {X} l1 l2.
Arguments rev {X} l.
Arguments snoc {X} l v.

Definition list123'' := cons 1 (cons 2 (cons 3 nil)).
Check (length list123'').

(* OR we could declare an arg to be implicit while defininging the func
itself, by surrounding the arg in curly braces *)
Fixpoint length'' {X:Type} (l:list X) : nat :=
  match l with
    | nil => 0
    | cons h t => S (length'' t)
  end.

(* Sometimes coq doesn't have enough local info to determine type argument
so we define something *)

(* Polymorphic lists exercises *)
Fixpoint repeat {X:Type} (n:X) (count:nat) : list X :=
  match count with
    | 0 => nil
    | S m => n :: repeat n m
  end.

Example test_repeat1:
  repeat true 2 = cons true (cons true nil).
Proof. simpl. reflexivity. Qed.

Theorem nil_app : forall X:Type, forall l:list X,
                    app [] l = l.
Proof.
  simpl. reflexivity.
Qed.

Theorem rev_snoc : forall X : Type,
                   forall v : X,
                   forall s : list X,
                     rev (snoc s v) = v :: (rev s).
Proof.
  intros.
  induction s.
  simpl. reflexivity.
  simpl. rewrite -> IHs. simpl. reflexivity.
Qed.


