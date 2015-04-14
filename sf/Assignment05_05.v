Require Export Assignment05_04.

(* problem #05: 10 points *)


(** 1 star, optional (or_distributes_over_and)  *)
Theorem or_distributes_over_and : forall P Q R : Prop,
  P \/ (Q /\ R) <-> (P \/ Q) /\ (P \/ R).
Proof.
    intros. split.
    - intros. destruct H.
      split.
        left. apply H.
        left. apply H.
      split.
        right. apply H.
        right. apply H.
    - intros. inversion H. inversion H0.
      left. apply H2.
      inversion H1.
      left. apply H3.
      right. split.
      apply H2.
      apply H3.
Qed.
(** [] *)


