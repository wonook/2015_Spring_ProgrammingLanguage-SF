Require Export mid_01.

(* problem #02: 10 points *)

(** Easy:
    Define a function [square_sum] satisfying:

      square_sum n = 1^2 + 2^2 + ... +n^2

 **)

Fixpoint square_sum (n: nat) : nat :=
match n with
| 0 -> 0
| S m => n*n + square_sum m

Example square_sum_example1: square_sum 5 = 55.
Proof. reflexivity. Qed.

Example square_sum_example2: square_sum 10 = 385.
Proof. reflexivity. Qed.

