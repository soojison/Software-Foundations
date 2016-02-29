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
Fixpoint alternate (l1 l2 : natlist) : natlist :=
  match l2 with
    | [] => l1
    | h2::t2 => match l1 with
                  | [] => l2
                  | h1::t1 => h1::h2 :: (alternate t1 t2)
                end
  end.
Example test_alternate1: alternate [1,2,3] [4,5,6] = [1,4,2,5,3,6].
Proof.
  reflexivity.
Qed.
Example test_alternate2: alternate [1] [4,5,6] = [1,4,5,6].
Proof.
  reflexivity.
Qed.
Example test_alternate3: alternate [1,2,3] [4] = [1,4,2,3].
Proof.
  reflexivity.
Qed.
Example test_alternate4: alternate [] [20,30] = [20,30].
Proof.
  reflexivity.
Qed.

(* Bags via Lists *)
(* Bag or a multiset is like a set, but each element can appear multiple times
 instead of just once *)
Definition bag := natlist.

(* Ex. bag_functions *)
Fixpoint count (v:nat) (s:bag) : nat :=
  match s with
    | [] => 0
    | h::t => if beq_nat v h then S (count v t) else count v t
  end.

Example test_count1: count 1 [1,2,3,1,4,1] = 3.
Proof.
  reflexivity.
Qed.

Example test_count2: count 6 [1,2,3,1,4,1] = 0.
Proof.
  reflexivity.
Qed.

(* su is similar to union *)

Definition sum : bag -> bag -> bag := app.
Example test_sum1: count 1 (sum [1,2,3] [1,4,1]) = 3.
Proof.
  reflexivity.
Qed.


Definition add (v:nat) (b:bag) := cons v b.

Example test_add1: count 1 (add 1 [1,4,1]) = 3.
reflexivity.
Qed.

Example test_add2: count 5 (add 1 [1,4,1]) = 0.
reflexivity.
Qed.

Definition member (v:nat) (s:bag) : bool :=
  negb (beq_nat (count v s) O).

Example test_member1: member 1 [1,4,1] = true.
reflexivity.
Qed.

Example test_member2: member 2 [1,4,1] = false.
  reflexivity.
Qed.
Fixpoint remove_one (v:nat) (s:bag) : bag :=
  match s with
    | [] => []
    | h::t => if (beq_nat h v) then t else h::(remove_one v t)
  end.

Example test_remove_one1: count 5 (remove_one 5 [2,1,5,4,1]) = 0.
reflexivity.
Qed.
Example test_remove_one2: count 5 (remove_one 5 [2,1,4,1]) = 0.
reflexivity.
Qed.
Example test_remove_one3: count 4 (remove_one 5 [2,1,4,5,1,4]) = 2.
reflexivity.
Qed.
Example test_remove_one4:
  count 5 (remove_one 5 [2,1,5,4,5,1,4]) = 1.
reflexivity.
Qed.

Fixpoint remove_all (v:nat) (s:bag) : bag :=
  match s with
    | [] => []
    | h::t => if (beq_nat h v) then (remove_all v t) else h::(remove_all v t)
  end.

Example test_remove_all1: count 5 (remove_all 5 [2,1,5,4,1]) = 0.
reflexivity.
Qed.

Example test_remove_all2: count 5 (remove_all 5 [2,1,4,1]) = 0.
reflexivity.
Qed.

Example test_remove_all3: count 4 (remove_all 5 [2,1,4,5,1,4]) = 2.
reflexivity.
Qed.

Example test_remove_all4: count 5 (remove_all 5 [2,1,5,4,5,1,4,5,1,4]) = 0.
reflexivity.
Qed.

Fixpoint subset (s1:bag) (s2:bag) : bool :=
  match s1 with
    | [] => true
    | h::t => if (member h s2) then (subset t (remove_one h s2)) else false
  end.


Example test_subset1: subset [1,2] [2,1,4,1] = true.
Proof.
reflexivity.
Qed.  

Example test_subset2: subset [1,2,2] [4,1] = false.
reflexivity.
Qed.

Example test_subset3: subset [1,2,2] [2,1,2] = true.
reflexivity.
Qed.

(* Reasoning about Lists *)

Theorem nil_app : forall l:natlist,
  [] ++ l = l.
Proof.
  reflexivity.
Qed.

Theorem tl_length_pred : forall l:natlist,
  pred (length l) = length (tl l).
  Proof.
    destruct l as [| n l'].
    reflexivity.
    reflexivity.
  Qed.

Theorem app_assoc : forall l1 l2 l3 : natlist,
  (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
Proof.
  intros l1 l2 l3.
  induction l1 as [| n l1'].
  Case "l1 = nil".
  reflexivity.
  Case "l1 = cons n l1'".
  simpl.
  rewrite -> IHl1'.
  reflexivity.
Qed.

Theorem app_length : forall l1 l2 : natlist,
  length (l1 ++ l2) = (length l1) + (length l2).
Proof.
  intros l1 l2.
  induction l1 as [|n l'].
  reflexivity.
  simpl.
  rewrite -> IHl'.
  reflexivity.
Qed.

Fixpoint snoc (l:natlist) (v:nat) : natlist :=
  match l with
    | nil => [v]
    | h :: t => h :: (snoc t v)
  end.
Fixpoint rev (l:natlist) : natlist :=
  match l with
    | [] => []
    | h :: t => (snoc (rev t) h)
  end.

Lemma length_snoc: forall (l:natlist) (n:nat),
  length (snoc l n) = S (length l).
Proof.
  intros l n.
  induction l as [| n' l' ].
  reflexivity.
  simpl.
  rewrite -> IHl'.
  reflexivity.
Qed.

Theorem rev_length : forall l : natlist,
  length (rev l) = length l.
Proof.
  intro l.
  induction l as [| n l'].
  reflexivity.
  simpl.
  rewrite -> length_snoc.
  rewrite -> IHl'.
  reflexivity.
Qed.

Theorem app_nil_end : forall l : natlist,
  l ++ [] = l.
Proof.
  intro l.
  induction l as [|n l'].
  reflexivity.
  simpl.
  rewrite -> IHl'.
  reflexivity.
Qed.

Theorem rev_snoc : forall (n:nat) (l:natlist),
  rev (snoc l n)   = n :: (rev l).
Proof.
  intros n l.
  induction l as [| n' l'].
  reflexivity.
  simpl.
  rewrite -> IHl'.
  reflexivity.
Qed.
Theorem rev_involutive : forall l : natlist,
  rev (rev l) = l.
  Proof.
    intro l.
    induction l as [| n l'].
    reflexivity.
    simpl.
    rewrite -> rev_snoc.
    rewrite IHl'.
    reflexivity.
  Qed.


(* Homework *)
Lemma snoc_app: forall (l1 l2:natlist) (n:nat),
 snoc (l1 ++ l2) n = l1 ++ snoc l2 n.
Proof.
  intros l1 l2 n.
  induction l1.
  reflexivity.
  simpl.
  rewrite IHl1.
  reflexivity.
Qed.

Theorem distr_rev : forall l1 l2 : natlist,
  rev (l1 ++ l2) = (rev l2) ++ (rev l1).
Proof.
  intros l1 l2.
  induction l1 as [| n l1'].
  simpl.
  rewrite -> app_nil_end.
  reflexivity.
  simpl.
  rewrite -> IHl1'.
  rewrite -> snoc_app.
  reflexivity.
Qed.
  
Theorem snoc_append : forall (l:natlist) (n:nat),
  snoc l n = l ++ [n].
Proof.
  intros l n.
  induction l.
  reflexivity.
  simpl.
  rewrite IHl.
  reflexivity.
Qed.

Theorem app_ass4 : forall l1 l2 l3 l4 : natlist,
  l1 ++ (l2 ++ (l3 ++ l4)) = ((l1 ++ l2) ++ l3) ++ l4.
  Proof.
    intros l1 l2 l3 l4.
    rewrite <- app_assoc.
    rewrite <- app_assoc.
    reflexivity.
  Qed.


Lemma nonzeros_length : forall l1 l2 : natlist,
  nonzeros (l1 ++ l2) = (nonzeros l1) ++ (nonzeros l2).
Proof.
  intros l1 l2.
  induction l1 as [| n l1'].
  reflexivity.
  destruct n as [| n'].
  simpl.
  rewrite -> IHl1'.
  reflexivity.
  simpl.
  rewrite -> IHl1'.
  reflexivity.
Qed.

Theorem count_member_nonzero : forall (s : bag),
  ble_nat 1 (count 1 (1 :: s)) = true.
Proof.
  intro s.
  reflexivity.
Qed.

Theorem ble_n_Sn : forall n,
  ble_nat n (S n) = true.
Proof.
  intro n.
  induction n as [| n'].
  reflexivity.
  simpl.
  rewrite IHn'.
  reflexivity.
Qed.

Theorem remove_decreases_count: forall (s : bag),
  ble_nat (count 0 (remove_one 0 s)) (count 0 s) = true.
Proof.
  intros s.
  induction s as [| n s' ].
  reflexivity.
  destruct n.
  simpl.
  rewrite ble_n_Sn.
  reflexivity.
  simpl.
  rewrite IHs'.
  reflexivity.
Qed.

(* natoption is a way of returning "error codes" from functions *)
Fixpoint index_bad (n:nat) (l:natlist) : nat :=
  match l with
    | nil => 42 (* arbitrary *)
    | a :: l' => match beq_nat n O with
                   | true => a
                   | false => index_bad (pred n) l'
                 end
  end.

Inductive natoption : Type :=
| None : natoption
| Some : nat -> natoption.

Fixpoint index (n:nat) (l:natlist) : natoption :=
  match l with
  | nil => None
  | a :: l' => match beq_nat n O with 
               | true => Some a 
               | false => index (pred n) l' 
               end
  end.

Definition foo (l:natlist) : bool :=
  match index 5 l with
    | Some 3 => true
    | _ => false
  end.

Fixpoint index' (n:nat) (l:natlist) : natoption :=
  match l with
  | nil => None 
  | a :: l' => if beq_nat n O then Some a else index (pred n) l'
  end.

Definition option_elim (d : nat) (o : natoption) : nat :=
  match o with
  | Some n' => n'
  | None => d
  end.

Definition hd_opt (l : natlist) : natoption :=
  match l with 
    | [] => None
    | h :: t => Some h
  end.

Theorem option_elim_hd : forall (l:natlist) (default:nat),
  hd default l = option_elim default (hd_opt l).
Proof.
  intros l default.
  destruct l.
  reflexivity.
  reflexivity.
Qed.

Fixpoint beq_natlist (l1 l2 : natlist) : bool :=
  match l1, l2 with
    | [], [] => true
    | h1 :: t1, h2 :: t2 => if beq_nat h1 h2 then beq_natlist t1 t2 else false
    | _, _ => false
  end.

End NatList.