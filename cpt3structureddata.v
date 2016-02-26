Require Export cpt2induction.

Module NatList.


  (* Working with Structured Data - Lists *)

  (* Pairs of numbers *)

  (* Inductive type definition
   * each constructor can take any number of arguments
   * none, one, more than one, etc. *)

Inductive natprod : Type :=
  pair : nat -> nat -> natprod.
(* "There is just one way to construct a pair of numbers:
    by applying the constructor pair to two arguments of type nat" *)

(* element of natprod *)
Check (pair 3 5).


(* function definition for extracting the first and second componenets
   of a pair *)

Definition fst (p : natprod) : nat :=
  match p with
    | pair x y => x
  end.
Definition snd (p : natprod) : nat :=
  match p with
    | pair x y => y
  end.

Eval compute in (fst (pair 3 5)).

(* tell Coq to allow mathematical notation *)
Notation "( x , y )" := (pair x y).

Eval compute in (fst (3,5)).

(* Notation can be used in expressions and pattern matches! *)
Definition fst' (p : natprod) : nat :=
  match p with
    | (x,y) => x
  end.
Definition and' (p : natprod) : nat :=
  match p with
    | (x,y) => y
  end.
Definition swap_pair (p : natprod) : natprod :=
  match p with
    | (x,y) => (y,x)
  end.

(* Proving simple facts about pairs *)
Theorem surjective_pairing' : forall(n m : nat),
                                (n,m) = (fst (n,m), snd (n,m)).
Proof.
  reflexivity.
Qed.

(* reflexivity is not enough if we state the lemma in a natural way *)
Theorem surjective_pairing_stuck: forall (p:natprod),
                                    p = (fst p, snd p).
Proof.
  simpl. (* Doesn't reduce anything *)
Abort.

(* have to expose the structure of p so that simpl can perform the 
   pattern match in fst and snd! Use destruct *)
Theorem surjective_pairing : forall (p : natprod),
                               p = (fst p, snd p).
Proof.
  intros p.
  destruct p as [n m].
  simpl.
  reflexivity.
Qed.

(* Exercise snd_fst_is_swap *)
Theorem snd_fst_is_swap : forall (p : natprod),
                            (snd p, fst p) = swap_pair p.
Proof.
  intros p.
  destruct p as [n m].
  simpl.
  reflexivity.
Qed.

(* Exercise fst_swap_is_snd *)
Theorem fst_swap_is_snd : forall (p : natprod),
                            fst(swap_pair p) = snd p.
Proof.
  intros p.
  destruct p as [n m].
  simpl.
  reflexivity.
Qed.

(* List of Numbers *)

(* We can describe the type of lists of numbers *)
(* A List is either the empty list or else a pair of number and another list *)

Inductive natlist : Type :=
    | nil : natlist
    | cons : nat -> natlist -> natlist.

(* Example: 3 element list *)
Definition mylist := cons 1 (cons 2 (cons 3 nil)).

(* more convenient to write lists in familiar programming notation  *)
Notation "x :: l" := (cons x l) (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x , .. , y ]" := (cons x .. (cons y nil) ..).

Check [1,2,3].
Check 1::2::3::nil.
Check (cons 1 (cons 2 (cons 3 nil))).
(* These three mean the same thing *)

Fixpoint repeat (n count : nat) : natlist  :=
  match count with
    | O => []
    | S count' => n::(repeat n count')
  end.

(* Length *)
Fixpoint length (l : natlist) : nat :=
  match l with
    | nil => O
    | h :: t => S (length t)
  end.

(* append *)
Fixpoint app (l1 l2 : natlist) : natlist := 
  match l1 with
  | nil => l2
  | h :: t => h :: (app t l2)
  end.

Notation "x ++ y" := (app x y) 
                     (right associativity, at level 60).

Example test_app1: [1,2,3] ++ [4,5] = [1,2,3,4,5].
Proof. reflexivity. Qed.
Example test_app2: nil ++ [4,5] = [4,5].
Proof. reflexivity. Qed.
Example test_app3: [1,2,3] ++ nil = [1,2,3].
Proof. reflexivity. Qed.

(* Head with default and Tail *)

Definition hd (default:nat) (l:natlist) : nat :=
  match l with
  | nil => default
  | h :: t => h
  end.

Definition tl (l:natlist) : natlist :=
  match l with
  | nil => nil 
  | h :: t => t
  end.

Example test_hd1: hd 0 [1,2,3] = 1.
Proof. reflexivity. Qed.
Example test_hd2: hd 0 [] = 0.
Proof. reflexivity. Qed.
Example test_tl: tl [1,2,3] = [2,3].
Proof. reflexivity. Qed.

(* Exercise list_funs *)
Fixpoint nonzeros (l:natlist) : natlist :=
  match l with
    | [] => []
    | 0 :: t => nonzeros t
    | h :: t => h :: (nonzeros t)
  end.

Example test_nonzeros: nonzeros [0,1,0,2,3,0,0] = [1,2,3].
Proof.
  reflexivity.
Qed.

Fixpoint oddnumbers (l:natlist) : natlist :=
  match l with
    | [] => []
    | h :: t => match (oddb h) with
                    | true => h::(oddnumbers t)
                    |false => oddnumbers t
  end
end.

Example test_oddnumbers: oddnumbers [0,1,0,2,3,0,0] = [1,3].
Proof.
  reflexivity.
Qed.

Fixpoint countoddnumbers (l:natlist) : nat :=
  match l with
    | [] => 0
    | h :: t => match (oddb h) with
                  | true => S (countoddnumbers t)
                  | false => countoddnumbers t
                end
  end.

Example test_countoddmembers1: countoddnumbers [1,0,3,1,4,5] = 4.
Proof.
  reflexivity.
Qed.

Example test_countoddmembers2: countoddnumbers [0,2,4] = 0.
Proof.
  reflexivity.
Qed.
Example test_countoddnumbers3: countoddnumbers nil = 0.
Proof.
  reflexivity.
Qed.

(* Exercise alternate *)
