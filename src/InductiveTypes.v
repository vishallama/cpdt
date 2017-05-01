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
