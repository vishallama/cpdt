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
