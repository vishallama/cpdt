Require Import Bool Arith List.
Require Import CpdtTactics.

Set Implicit Arguments.
Set Asymmetric patterns.


(* 2.1 - Arithmetic Expressions Over Natural Numbers *)

(* Source Language *)
Inductive binop : Set :=
| Plus
| Times.

Inductive exp : Set :=
| Const : nat -> exp
| Binop : binop -> exp -> exp -> exp.

Definition binopDenote (b : binop) : nat -> nat -> nat :=
  match b with
  | Plus => plus
  | Times => mult
  end.

Fixpoint expDenote (e : exp) : nat :=
  match e with
  | Const n => n
  | Binop b e1 e2 => (binopDenote b) (expDenote e1) (expDenote e2)
  end.

Example exp_1 : expDenote (Const 42) = 42.
Proof. reflexivity. Qed.

Example exp_2 : expDenote (Binop Plus (Const 2) (Const 2)) = 4.
Proof. reflexivity. Qed.

Example exp_3 :
  expDenote (Binop Times (Binop Plus (Const 2) (Const 2)) (Const 7)) = 28.
Proof. reflexivity. Qed.

(* Target Language *)
Inductive instr : Set :=
| iConst : nat -> instr
| iBinop : binop -> instr.

Definition prog := list instr.
Definition stack := list nat.

(* An instruction either pushes a constant onto the stack or pops two
   arguments, applies a binary operator to them, and then pushes the
   result onto the stack.
*)

(* Give instructions meanings as functions from stacks to optional
   stacks to handle stack underflows.
*)
Definition instrDenote (i : instr) (s : stack) : option stack :=
  match i with
  | iConst n => Some (n :: s)
  | iBinop b =>
    match s with
    | arg1 :: arg2 :: s' => Some ((binopDenote b) arg1 arg2 :: s')
    | _ => None
    end
  end.
