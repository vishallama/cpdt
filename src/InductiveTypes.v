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
