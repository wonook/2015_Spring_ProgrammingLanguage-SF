Require Export Assignment05_15.

(* problem #16: 10 points *)







(** 2 stars (b_times2)  *)
Theorem b_times2: forall n, beautiful n -> beautiful (2*n).
Proof.
    intros. simpl. apply b_sum.
    - apply H.
    - apply b_sum. apply H. apply b_0.
Qed.
(** [] *)



