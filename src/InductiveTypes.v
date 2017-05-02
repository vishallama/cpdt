Require Import Bool Arith List.
Require Import CpdtTactics.

Set Implicit Arguments.


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


(* 3.7 - An Interlude on Induction Principles *)

(* For most inductive types T, we get not just induction principles T_ind,
   but also recursion principles T_rec. We can use T_rec to write recursive
   definitions without explicit Fixpoint recursion. For example, the
   following two definitions are equivalent: *)
Fixpoint plus_recursive (n : nat) : nat -> nat :=
  match n with
  | O => fun m => m
  | S n' => fun m => S (plus_recursive n' m)
  end.

Definition plus_rec : nat -> nat -> nat :=
  nat_rec (fun _ : nat => nat -> nat) (fun m => m) (fun _ r m => S (r m)).
Print plus_rec.

Theorem plus_equivalent : plus_recursive = plus_rec.
Proof. reflexivity. Qed.

Print nat_rec.
Print nat_rect.

(* nat_rec is implemented in terms of nat_rect, but there is nothing special
   about the latter. We can reimplement it manually. *)
Fixpoint nat_rect' (P : nat -> Type)
  (HO : P O)
  (HS : forall n, P n -> P (S n))
  (n : nat) :=
  match n return (P n) with
  | O => HO
  | S n' => HS n' (nat_rect' P HO HS n')
  end.

(* Reimplement nat_ind using sections *)
Section nat_ind'.
  Variable P : nat -> Type.
  Hypothesis O_case : P O.
  Hypothesis S_case : forall n : nat, P n -> P (S n).

  Fixpoint nat_ind' (n : nat) : P n :=
    match n with
    | O => O_case
    | S n' => S_case (nat_ind' n')
    end.
End nat_ind'.

Print nat_ind'.

(* The Coq nat_ind and our manually constructed nat_ind' are the same *)
Theorem nat_ind_eq_nat_ind' : nat_ind = nat_ind'.
Proof. reflexivity. Qed.

Print even_list_mut.

(* Reimplement even_list_mut manually *)
Section even_list_mut'.
  Variable Peven : even_list -> Prop.
  Variable Podd : odd_list -> Prop.

  Hypothesis ENil_case : Peven ENil.
  Hypothesis ECons_case :
    forall (n : nat) (o : odd_list),
    Podd o -> Peven (ECons n o).
  Hypothesis OCons_case :
    forall (n : nat) (e : even_list),
    Peven e -> Podd (OCons n e).

  Fixpoint even_list_mut' (e : even_list) : Peven e :=
    match e with
    | ENil => ENil_case
    | ECons n o => ECons_case n (odd_list_mut' o)
    end
  with odd_list_mut' (o : odd_list) : Podd o :=
    match o with
    | OCons n e => OCons_case n (even_list_mut' e)
    end.
End even_list_mut'.

Theorem even_list_mut_eq_even_list_mut' : even_list_mut = even_list_mut'.
Proof. reflexivity. Qed.

(* Reimplement induction principles for our reflexive type *)
Section formula_ind'.
  Variable P : formula -> Prop.

  Hypothesis Eq_case : forall n1 n2 : nat, P (Eq n1 n2).
  Hypothesis And_case : forall f1 f2 : formula,
    P f1 -> P f2 -> P (And f1 f2).
  Hypothesis Forall_case : forall f : nat -> formula,
    (forall n : nat, P (f n)) -> P (Forall f).

  Fixpoint formula_ind' (f : formula) : P f :=
    match f with
    | Eq n1 n2 => Eq_case n1 n2
    | And f1 f2 => And_case (formula_ind' f1) (formula_ind' f2)
    | Forall f' => Forall_case f' (fun n => formula_ind' (f' n))
    end.
End formula_ind'.


(* 3.8 - Nested Inductive Types *)

(* Extend binary trees to trees with arbitrary finite branching *)
Inductive nat_tree : Set :=
| NNode' : nat -> list nat_tree -> nat_tree.

(* Automatically generated induction principle for nat_tree is too weak *)
Check nat_tree_ind.

(* But, we can implement a suitable induction principle manually for
   nat_tree. First, we define a predicate capturing the idea that some
   property holds of every element in a list. Here, All duplicates the
   Coq standard library's Forall predicate. *)
Section All.
  Variable T : Set.
  Variable P : T -> Prop.

  Fixpoint All (ls : list T) : Prop :=
    match ls with
    | Nil _ => True
    | Cons h t => P h /\ All t
    end.
End All.

(* Create our induction principle for nat_tree *)
Section nat_tree_ind'.
  Variable P : nat_tree -> Prop.

  Hypothesis NNode'_case : forall (n : nat) (ls : list nat_tree),
    All P ls -> P (NNode' n ls).

  Fixpoint nat_tree_ind' (tr : nat_tree) : P tr :=
    match tr with
    | NNode' n ls => NNode'_case n ls
        ((fix list_nat_tree_ind (ls : list nat_tree) : All P ls :=
          match ls with
          | Nil _ =>
              I
          | Cons tr' rest =>
              conj (nat_tree_ind' tr') (list_nat_tree_ind rest)
          end) ls)
    end.
End nat_tree_ind'.

(* Try out our induction principle by defining some recursive functions
   on nat_tree and proving a theorem about them. *)
Section map.
  Variables T T' : Set.
  Variable F : T -> T'.

  Fixpoint map (ls : list T) : list T' :=
    match ls with
    | Nil _ => Nil _
    | Cons h t => Cons (F h) (map t)
    end.
End map.

Fixpoint sum (ls : list nat) : nat :=
  match ls with
  | Nil _ => O
  | Cons h t => plus h (sum t)
  end.

(* Size function over our trees *)
Fixpoint ntsize (tr : nat_tree) : nat :=
  match tr with
  | NNode' _ trs => S (sum (map ntsize trs))
  end.

(* Tree splicing *)
Fixpoint ntsplice (tr1 tr2 : nat_tree) : nat_tree :=
  match tr1 with
  | NNode' n (Nil _) => NNode' n (Cons tr2 (Nil _))
  | NNode' n (Cons tr trs) => NNode' n (Cons (ntsplice tr tr2) trs)
  end.

Lemma plus_S : forall n1 n2 : nat,
  plus n1 (S n2) = S (plus n1 n2).
Proof. induction n1; crush. Qed.

(* Add Lemma plus_S as a hint *)
Hint Rewrite plus_S.

Theorem ntsize_ntsplice :
  forall tr1 tr2 : nat_tree,
  ntsize (ntsplice tr1 tr2) = plus (ntsize tr2) (ntsize tr1).
Proof.
  induction tr1 using nat_tree_ind'; crush.
  destruct ls; crush.
  (* Automate the proof, so that there is no mention of ls variable *)
  Restart.
  Hint Extern 1
    (ntsize (match ?LS with (Nil _) => _ | Cons _ _ => _ end) = _) =>
      destruct LS; crush.
  induction tr1 using nat_tree_ind'; crush.
Qed.


(* Manual Proofs About Constructors *)

(* Manual proof for discriminate *)
Theorem true_neq_false : true <> false.
Proof.
  (* one step reduction to unfold the definition of logical negation *)
  red.
  intro H.
  change ((fun b : bool =>
             if b then True else False) false).
  rewrite <- H.
  trivial.
Qed.

(* Manual proof for injectivity of the constructor S *)
Theorem S_inj'' : forall n m : nat, S n = S m -> n = m.
Proof.
  intros n m H.
  change (pred (S n) = pred (S m)).
  rewrite H. reflexivity.
Qed.
