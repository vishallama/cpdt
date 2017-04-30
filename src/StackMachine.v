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

(* Function which iterates application of instrDenote through a whole
   program.
*)
Fixpoint progDenote (p : prog) (s : stack) : option stack :=
  match p with
  | nil => Some s
  | i :: p' =>
    match (instrDenote i s) with
    | None => None
    | Some s' => progDenote p' s'
    end
  end.

(* Translation *)
Fixpoint compile (e : exp) : prog :=
  match e with
  | Const n => iConst n :: nil
  | Binop b e1 e2 => compile e2 ++ compile e1 ++ iBinop b :: nil
  end.

Example compile_1 :
  compile (Const 42) = iConst 42 :: nil.
Proof. reflexivity. Qed.

Example compile_2 :
  compile (Binop Plus (Const 2) (Const 2))
  = iConst 2 :: iConst 2 :: iBinop Plus :: nil.
Proof. reflexivity. Qed.

Example compile_3 :
  compile (Binop Times (Binop Plus (Const 2) (Const 2)) (Const 7))
  = iConst 7 :: iConst 2 :: iConst 2 :: iBinop Plus :: iBinop Times :: nil.
Proof. reflexivity. Qed.

Example progDenote_1 :
  progDenote (compile (Const 42)) nil = Some (42 :: nil).
Proof. reflexivity. Qed.

Example progDenote_2 :
  progDenote (
    compile (Binop Plus (Const 2) (Const 2)))
    nil = Some (4 :: nil).
Proof. reflexivity. Qed.

Example progDenote_3 :
  progDenote (
    compile (Binop Times (Binop Plus (Const 2) (Const 2)) (Const 7)))
    nil = Some (28 :: nil).
Proof. reflexivity. Qed.
