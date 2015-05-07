Require Export mid_01.

(* problem #02: 10 points *)

(** Easy:
    Define a function [square_sum] satisfying:

      square_sum n = 1^2 + 2^2 + ... +n^2

 **)

Fixpoint square_sum (n: nat) : nat :=
  (* FILL IN HERE *) admit.

Example square_sum_example1: square_sum 5 = 55.
Proof. (* FILL IN HERE *) admit. Qed.

Example square_sum_example2: square_sum 10 = 385.
Proof. (* FILL IN HERE *) admit. Qed.

