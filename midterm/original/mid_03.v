Require Export mid_02.

(* problem #03: 10 points *)

(** Medium:
    Define a function [fibonacci] satisfying:

      fibonacci 0 = 0
      fibonacci 1 = 1
      fibonacci (n+2) = fibonacci (n+1) + fibonacci n

 **)

Fixpoint fibonacci (n: nat) : nat :=
  (* FILL IN HERE *) admit.

Example fibonacci_example1: fibonacci 5 = 5.
Proof. (* FILL IN HERE *) admit. Qed.

Example fibonacci_example2: fibonacci 10 = 55.
Proof. (* FILL IN HERE *) admit. Qed.

