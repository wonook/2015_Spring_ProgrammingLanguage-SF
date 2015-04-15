Require Export Assignment05_34.

(* problem #35: 10 points *)

Theorem lt_S : forall n m,
  n < m ->
  n < S m.
Proof.
    unfold lt. intros. 
    apply n_le_m__Sn_le_Sm. assert (n <= S n).
      apply le_S. apply le_n.
      apply le_trans with (n:= S n). apply H0. apply H.
Qed.

