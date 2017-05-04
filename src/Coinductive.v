Require Import List.
Require Import CpdtTactics.


(* In Coq, infinite loops are disastrous, since we could use the latter to
   prove any proposition vacuously. The following piece of code is not
   allowed in Coq:

     Fixpoint bad {P : Prop} (u : unit) : P := bad u

   But, if it were, then it would leave us with 'bad tt' as a proof of P,
   where P is any proposition.

  There are also algorithmic considerations that make universal termination
  very desirable. Tactics like reflexivity compare terms up to equivalence
  under computational rules. Calls to recursive, pattern-matching functions
  are simplified automatically with no need for explicit proof steps.

  Coq has special support for a class of lazy data structures that happens
  to contain most examples found in Haskell. That mechanism comprises the
  use of co-inductive types. *)


(* 5.1 - Computing with Infinite Data *)

(* Streams (lazy lists) - most basic type of infinite data *)
Section stream.
  Variable A : Type.

  CoInductive stream : Type :=
  | Cons : A -> stream -> stream.
End stream.

Arguments Cons {A} _ _.

(* Recursive definitions were necessary to 'use' values of recursive inductive
   types effectively. We need co-recursive definitions to 'build' values of
   co-inductive types effectively. *)
CoFixpoint zeroes : stream nat := Cons 0 zeroes.

(* Stream that alternates between true and false *)
CoFixpoint trues_falses : stream bool := Cons true falses_trues
with falses_trues : stream bool := Cons false trues_falses.

(* Co-inductive values as arguments to recursive functions *)
Fixpoint approx {A} (s : stream A) (n : nat) : list A :=
  match n with
  | O => nil
  | S n' =>
    match s with
    | Cons h t => h :: approx t n'
    end
  end.

Example approx_test1 :
  approx zeroes 5 = 0 :: 0 :: 0 :: 0 :: 0 :: nil.
Proof. reflexivity. Qed.

Example approx_test2 :
  approx trues_falses 3 = true :: false :: true :: nil.
Proof. reflexivity. Qed.

(* There are some very important restrictions on the use of co-inductive
   types that are dual to the restrictions on the use of inductive types.
   Fixpoints consume values of inductive types, with restrictions on which
   arguments may be passed in recursive calls. Dually, co-fixpoints produce
   values of co-inductive types, with restrictions on what may be done with
   the results of co-recursive calls.

   The restriction for co-inductive types shows up as the 'guardedness'
   condition. That is, every co-recursive call must be guarded by a
   constructor. In other words, every co-recursive call must be a direct
   argument to a constructor of the co-inductive type we are generating. *)
