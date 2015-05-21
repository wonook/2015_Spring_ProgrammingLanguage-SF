Require Export Assignment05_36.

(* problem #37: 10 points *)

Theorem le_ble_nat : forall n m,
  n <= m ->
  ble_nat n m = true.
Proof.
  (* Hint: This may be easiest to prove by induction on [m]. *)
    intros. generalize dependent n. induction m.
    - intros. inversion H. reflexivity.
    (* hard time here //*)
    - intros. destruct n.
      simpl. reflexivity.
      simpl. apply IHm. apply Sn_le_Sm__n_le_m. apply H.
Qed.

