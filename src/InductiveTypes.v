Require Import Bool Arith List.
Require Import CpdtTactics.

Set Implicit Arguments.
Set Asymmetric patterns.


(* 3.1 - Proof Terms *)
Check (fun x : nat => x).
Check (fun x : True => x).
Check (fun x : False => x).
Check (fun _ : False => I).

(* Coq's metatheory guarantees that any term of type bool evaluates to
   either true or false. On the other hand, most propositions do not
   evaluate to True or False. It's a good thing that there exists no
   algorithm for deciding formalized versions of mathematical theorems,
   for otherwise, we wouldn't be able to formalize undecidable properties,
   such as almost any interesting property of general-purpose programs. *)

(* 3.2 - Enumerations *)
Check unit.
Check tt.

Theorem unit_singleton : forall x : unit, x = tt.
Proof. induction x. reflexivity. Qed.

Check unit_ind.

Check Empty_set.

Theorem the_sky_is_falling : forall x : Empty_set, 2 + 2 = 5.
Proof. destruct 1. Qed.

Check Empty_set_ind.

(* Convert values of Empty_set to values of unit *)
Definition e2u (e : Empty_set) : unit := match e with end.

(* Empty_set is the Curry-Howard equivalence of False *)

Theorem negb_inverse : forall b : bool, negb (negb b) = b.
Proof. destruct b; reflexivity. Qed.

Theorem negb_ineq : forall b : bool, negb b <> b.
Proof. destruct b; discriminate. Qed.

Check bool_ind.

(* 3.3 - Simple Recursive Types *)
Definition isZero (n : nat) : bool :=
  match n with
  | O => true
  | _ => false
  end.

Theorem n_plus_O : forall n : nat, plus n O = n.
Proof.
  induction n as [| n' IHn'].
  - (* n = O *) reflexivity.
  - (* n = S n' *) simpl; rewrite IHn'; reflexivity.
Restart.
  induction n; crush.
Qed.

Theorem S_inj : forall n m : nat, S n = S m -> n = m.
Proof. injection 1; trivial. Qed.

Theorem S_inj' : forall n m : nat, S n = S m -> n = m.
Proof. congruence. Qed.

(* A type of lists of natural numbers *)
Inductive nat_list : Set :=
| NNil : nat_list
| NCons : nat -> nat_list -> nat_list.

Fixpoint nlength (ls : nat_list) : nat :=
  match ls with
  | NNil => O
  | NCons _ ls' => S (nlength ls')
  end.

Fixpoint napp (ls1 ls2 : nat_list) : nat_list :=
  match ls1 with
  | NNil => ls2
  | NCons n ls1' => NCons n (napp ls1' ls2)
  end.

Theorem nlength_app :
  forall ls1 ls2 : nat_list,
  nlength (napp ls1 ls2) = plus (nlength ls1) (nlength ls2).
Proof. induction ls1; crush. Qed.

Check nat_list_ind.

(* A type of binary tree of naturals *)
Inductive nat_btree : Set :=
| NLeaf : nat_btree
| NNode : nat_btree -> nat -> nat_btree -> nat_btree.

Fixpoint nsize (tr : nat_btree) : nat :=
  match tr with
  | NLeaf => S O
  | NNode tr1 _ tr2 => plus (nsize tr1) (nsize tr2)
  end.

Fixpoint nsplice (tr1 tr2 : nat_btree) : nat_btree :=
  match tr1 with
  | NLeaf => NNode tr2 O NLeaf
  | NNode tr1' n tr2' => NNode (nsplice tr1' tr2) n tr2'
  end.

Theorem plus_assoc :
  forall n1 n2 n3 : nat,
  plus (plus n1 n2) n3 = plus n1 (plus n2 n3).
Proof. induction n1; crush. Qed.

Hint Rewrite n_plus_O plus_assoc.

Theorem nsize_nsplice :
  forall tr1 tr2 : nat_btree,
  nsize (nsplice tr1 tr2) = plus (nsize tr2) (nsize tr1).
Proof. induction tr1; crush. Qed.

Check nat_btree_ind.
