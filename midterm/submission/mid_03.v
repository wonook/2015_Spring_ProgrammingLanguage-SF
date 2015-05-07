Require Export mid_02.

(* problem #03: 10 points *)

(** Medium:
    Define a function [fibonacci] satisfying:

      fibonacci 0 = 0
      fibonacci 1 = 1
      fibonacci (n+2) = fibonacci (n+1) + fibonacci n

 **)

Fixpoint fibonacci (n: nat) : nat :=
  match n with
  | 0 => 0
  | S m => match m with
			| 0 => 1
			| S l => fibonacci m + fibonacci l
			end
  end.

Example fibonacci_example1: fibonacci 5 = 5.
Proof. reflexivity. Qed.

Example fibonacci_example2: fibonacci 10 = 55.
Proof. reflexivity. Qed.

