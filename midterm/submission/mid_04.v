Require Export mid_03.

(* problem #04: 10 points *)

(** Medium:
    Prove the following theorem.
 **)

Fixpoint odd_sum (n: nat) : nat :=
  match n with
  | 0 => 0
  | S m => 1 + 2*m + odd_sum m
  end.

Theorem odd_sum__square: forall n,
  odd_sum n = n * n.
Proof.
  (* FILL IN HERE *) admit.
Qed.

