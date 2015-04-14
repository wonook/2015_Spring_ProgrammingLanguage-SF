Require Export Assignment05_12.

(* problem #13: 10 points *)



(** 2 stars, optional (beq_nat_false)  *)
Theorem beq_nat_false : forall n m,
  beq_nat n m = false -> n <> m.
Proof.
    intros n m. unfold not. intros. generalize dependent m. induction n.
    - intros. induction m.
      inversion H.
      inversion H0.
    - intros. induction m.
      inversion H0.
      apply IHn with m. apply H. inversion H0. reflexivity.
Qed.
(** [] *)



