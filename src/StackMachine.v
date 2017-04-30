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

(* Translation Correctness *)
Theorem compile_correct :
  forall e, progDenote (compile e) nil = Some (expDenote e :: nil).
Proof.
  (* Prove auxiliary lemma that strengthens the induction hypothesis on e *)
Abort.

(* Manual proof *)
Lemma compile_correct'' :
  forall e p s,
  progDenote (compile e ++ p) s = progDenote p (expDenote e :: s).
Proof.
  induction e as [n | b e1 IHe1 e2 IHe2].
  - (* e = Const n *)
    simpl; intros; reflexivity.
  - (* e = Binop b e1 e2 *)
    intros.
    unfold compile.
    fold compile.
    unfold expDenote.
    fold expDenote.
    rewrite app_assoc_reverse.
    rewrite IHe2.
    rewrite app_assoc_reverse.
    rewrite IHe1.
    unfold progDenote at 1.
    simpl.
    fold progDenote.
    reflexivity.
Qed.

(* Automated proof *)
Lemma compile_correct' :
  forall e p s,
  progDenote (compile e ++ p) s = progDenote p (expDenote e :: s).
Proof.
  induction e; crush.
Qed.

Theorem compile_correct :
  forall e, progDenote (compile e) nil = Some (expDenote e :: nil).
Proof.
  intros;
  rewrite (app_nil_end (compile e));
  rewrite compile_correct';
  reflexivity.
Qed.


(* 2.2 - Typed Expressions *)

(* Source Language *)

(* Trivial language of types to classify expressions *)
Inductive type : Set :=
| Nat
| Bool.

(* Expanded set of binary operators *)
Inductive tbinop : type -> type -> type -> Set :=
| TPlus : tbinop Nat Nat Nat
| TTimes : tbinop Nat Nat Nat
| TEq : forall t, tbinop t t Bool
| TLt : tbinop Nat Nat Bool.
