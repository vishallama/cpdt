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


(* 3.4 - Parameterized Types *)
Inductive list (T : Set) : Set :=
| Nil : list T
| Cons : T -> list T -> list T.

Fixpoint length T (ls : list T) : nat :=
  match ls with
  | Nil _ => O
  | Cons _ ls' => S (length ls')
  end.

Fixpoint app T (ls1 ls2 : list T) : list T :=
  match ls1 with
  | Nil _ => ls2
  | Cons x ls1' => Cons x (app ls1' ls2)
  end.

Theorem length_app :
  forall T (ls1 ls2 : list T),
  length (app ls1 ls2) = plus (length ls1) (length ls2).
Proof. induction ls1; crush. Qed.

Check list_ind.


(* Mutually Inductive Types *)
Inductive even_list : Set :=
| ENil : even_list
| ECons : nat -> odd_list -> even_list

with odd_list : Set :=
| OCons : nat -> even_list -> odd_list.

Fixpoint elength (el : even_list) : nat :=
  match el with
  | ENil => O
  | ECons _ ol => S (olength ol)
  end

with olength (ol : odd_list) : nat :=
  match ol with
  | OCons _ el => S (elength el)
  end.

Fixpoint eapp (el1 el2 : even_list) : even_list :=
  match el1 with
  | ENil => el2
  | ECons n ol => ECons n (oapp ol el2)
  end

with oapp (ol : odd_list) (el : even_list) : odd_list :=
  match ol with
  | OCons n el' => OCons n (eapp el' el)
  end.

Check even_list_ind.

(* In the case of definitions of mutually inductive types, Coq's generation
   of induction principles is incomplete. We only get non-mutual induction
   principles by default. To get mutual induction principles, we need to
   ask for them using the Scheme command. *)

Scheme even_list_mut := Induction for even_list Sort Prop
with odd_list_mut := Induction for odd_list Sort Prop.

Check even_list_mut.

(* Prove theorem using inductive principle directly, instead of using the
   induction command. *)
Theorem n_plus_O' : forall n : nat, n + O = n.
Proof. apply (nat_ind (fun n => plus n O = n)); crush. Qed.

(* The above technique generalizes to the mutually inductive types *)
Theorem elength_eapp :
  forall el1 el2 : even_list,
  elength (eapp el1 el2) = plus (elength el1) (elength el2).
Proof.
  apply (even_list_mut
    (fun el1 : even_list => forall el2 : even_list,
      elength (eapp el1 el2) = plus (elength el1) (elength el2))
    (fun ol : odd_list => forall el : even_list,
      olength (oapp ol el) = plus (olength ol) (elength el))); crush.
Qed.

(* In the above proof, we just need to specify two predicates, one for each
   of the mutually inductive types. *)


(* 3.6 - Reflexive Types *)

(* Consider a simple formula for a subset of propositional logic *)
Inductive pformula : Set :=
| Truth : pformula
| Falsehood : pformula
| Conjunction : pformula -> pformula -> pformula.

(* We can make the semantics explicit with a recursive function *)
Fixpoint pformulaDenote (f : pformula) : Prop :=
  match f with
  | Truth => True
  | Falsehood => False
  | Conjunction f1 f2 => (pformulaDenote f1) /\ (pformulaDenote f2)
  end.

(* When we consider first-order logic, it is very handy to give constructors
   recursive arguments that are functions. *)
Inductive formula : Set :=
| Eq : nat -> nat -> formula
| And : formula -> formula -> formula
| Forall : (nat -> formula) -> formula.

(* The above is an example of a reflexive type, which includes at least one
   constructor that takes as an argument a function returning the same type
   we are defining. In the above, we avoid needing to include a notion of
   variables in our type, by using Coq functions to encode the syntax of
   quantification. For instance, here is the encoding of
     forall x : nat, x = x *)
Example forall_refl : formula := Forall (fun x => Eq x x).

Fixpoint formulaDenote (f : formula) : Prop :=
  match f with
  | Eq n1 n2 => n1 = n2
  | And f1 f2 => formulaDenote f1 /\ formulaDenote f2
  | Forall f' => forall n : nat, formulaDenote (f' n)
  end.

Fixpoint swapper (f : formula) : formula :=
  match f with
  | Eq n1 n2 => Eq n2 n1
  | And f1 f2 => And (swapper f1) (swapper f2)
  | Forall f' => Forall (fun n => swapper (f' n))
  end.

Theorem swapper_preserves_truty :
  forall f, formulaDenote f -> formulaDenote (swapper f).
Proof. induction f; crush. Qed.

Check formula_ind.

(* Only some of the reflexive types in Coq are legal *)
