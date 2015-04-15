Require Export Assignment05_38.

(* problem #39: 10 points *)

Theorem ble_nat_false : forall n m,
  ble_nat n m = false -> ~(n <= m).
Proof.
    unfold not.
    intros. generalize dependent m. induction n.
    - intros. inversion H.
    - intros. destruct m.
      inversion H0.
      apply (IHn m). simpl in H. apply H.
      apply Sn_le_Sm__n_le_m. apply H0.
Qed.
(** [] *)

