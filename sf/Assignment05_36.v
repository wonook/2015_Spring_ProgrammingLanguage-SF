Require Export Assignment05_35.

(* problem #36: 10 points *)

Theorem ble_nat_true : forall n m,
  ble_nat n m = true -> n <= m.
Proof. 
    (* hard time.. *)
    intros. generalize dependent n. induction m.
    - intros. destruct n.
      apply le_n.
      inversion H. 
    - intros. destruct n.
      apply O_le_n.
      apply n_le_m__Sn_le_Sm. apply IHm. simpl in H. apply H.
Qed.

