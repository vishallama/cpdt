Require Import List.
Require Import CpdtTactics.

Set Implicit Arguments.


(* 4.1 - Propositional Logic *)
Section Propositional.
  Variables P Q R : Prop.

  Theorem obvious : True.
  Proof. apply I. Qed.

  Theorem obvious' : True.
  Proof. constructor. Qed.

  Theorem False_imp : False -> 2 + 2 = 5.
  Proof. destruct 1. Qed.

  Theorem arith_neq : 2 + 2 = 5 -> 9 + 9 = 835.
  Proof. intro. elimtype False. crush. Qed.

  Theorem arith_neq' : ~ (2 + 2 = 5).
  Proof. unfold not; crush. Qed.

  Theorem and_comm : P /\ Q -> Q /\ P.
  Proof. destruct 1; split; assumption. Qed.

  Theorem or_comm : P \/ Q -> Q \/ P.
  Proof. destruct 1; [right | left]; assumption. Qed.

  Theorem or_comm' : P \/ Q -> Q \/ P.
  Proof. tauto. Qed.

  Theorem arith_comm : forall ls1 ls2 : list nat,
    length ls1 = length ls2 \/ length ls1 + length ls2 = 6 ->
    length (ls1 ++ ls2) = 6 \/ length ls1 = length ls2.
  Proof. intuition. rewrite app_length; tauto. Qed.

  Theorem arith_comm' : forall ls1 ls2 : list nat,
    length ls1 = length ls2 \/ length ls1 + length ls2 = 6 ->
    length (ls1 ++ ls2) = 6 \/ length ls1 = length ls2.
  Proof. Hint Rewrite app_length. crush. Qed.
End Propositional.


(* 4.2 - What Does It Mean to Be Constructive? *)

(* Coq implements constructive or intuitionistic logic, wherein classical
   tautologies like ~~ P and P \/ ~P do not always hold. In general, we can
   only prove these tautologies when P is decidable, in the sense of
   computability theory.

   Q. Why doesn't P \/ ~P (law of the excluded middle) always hold?
   A. The Curry-Howard encoding that Coq uses for 'or' allows us to extract
      either a proof of P or a proof of ~P from any proof of P \/ ~P. Since
      a proof in Coq is just a functional program that we can run, a general
      law of the excluded middle would give us a decision procedure for the
      halting problem, where an instantiation of P could be a formula like
      'this particular Turing machine halts'. *)


(* 4.3 - First-Order Logic *)

(* The 'forall' connective in first-order logic is built into Coq. It is the
   dependent function type constructor. Implication and universal
   quantification are just different syntactic shorthands for the same Coq
   mechanism. A formula P -> Q is equivalent to forall x : T, Q, where x does
   not appear in Q.

   Existential quantification is defined in the standard library in terms of
   universal quantification. *)
Print ex.

Theorem exist1 : exists x : nat, x + 1 = 2.
Proof. exists 1; reflexivity. Qed.

Theorem exist2 :
  forall n m : nat,
  (exists x : nat, n + x = m) -> n <= m.
Proof. destruct 1; (* firstorder *) (* intuition *) crush. Qed.


(* 4.4 Predicates with Implicit Equality *)
Inductive isZero : nat -> Prop :=
| IsZero : isZero O.

Theorem isZero_zero : isZero O.
Proof. constructor. Qed.

(* In Coq, equality is just another inductive type. It is the least reflexive
   relation. *)
Print eq.

Theorem isZero_plus :
  forall n m : nat, isZero m -> n + m = n.
Proof. destruct 1; crush. Qed.

Theorem isZero_contra : isZero 1 -> False.
Proof. inversion 1. Qed.


(* 4.5 - Recursive Predicates *)

(* Inductive definition of even *)
Inductive even : nat -> Prop :=
| EvenO : even O
| EvenSS : forall n, even n -> even (S (S n)).

Theorem even_O : even O.
Proof. constructor. Qed.

Theorem even_4 : even 4.
Proof. repeat constructor. Qed.

Hint Constructors even.

Theorem even_4' : even 4.
Proof. auto. Qed.

Theorem even_1_contra : ~ even 1.
Proof. inversion 1. Qed.

Theorem even_3_contra : ~ even 3.
Proof. inversion 1 as [| n H1 H']; inversion H1. Qed.

(* Inductive proofs about even *)
Theorem even_plus :
  forall n m, even n -> even m -> even (n + m).
Proof. induction 1; crush. Qed.


(* Induction on recursive predicates *)
Lemma even_contra' :
  forall n', even n' -> forall n, n' = S (n + n) -> False.
Proof.
  Hint Rewrite <- plus_n_Sm.
  induction 1; crush;
  match goal with
  | [H : S ?N = ?N0 + ?N0 |- _] => destruct N; destruct N0
  end; crush.
Qed.

Theorem even_contra : forall n, ~ even (S (n + n)).
Proof. unfold not; intros; eapply even_contra'; eauto. Qed.

(* Above, we use a variant eapply of apply. eapply will introduce
   unification variables for undetermined arguments. And, eauto is able to
   determine the right values for those unification variables, using a
   variant of the classic algorithm for 'unification'.

   In general, quantified variables and hypotheses that appear before the
   induction object in the theorem statement stay fixed throughout the
   inductive proof. Variables and hypotheses that are quantified after the
   induction object may be varied explicitly in uses of inductive hypotheses.

   Coq implements 'induction' this way for a few reasons. It avoids
   burdening this basic tactic with additional heuristic smarts. Also,
   dealing with more complex inductive hypotheses could cause particular
   automation machinery to fail when it would have succeeded before. In
   general, we want to avoid quantifiers in our proofs whenever we can,
   and that goal is furthered by the refactoring that the induction tactic
   forces us to do. *)
