Require Export Assignment08_15.

(* problem #16: 10 points *)

Lemma optimize_0plus_aexp_sound:
  atrans_sound optimize_0plus_aexp.
Proof.
  unfold atrans_sound. intros. unfold aequiv. intros. induction a; try reflexivity.
  - simpl. try (destruct a1; try destruct a2; try destruct n; try rewrite IHa1; try rewrite IHa2; try rewrite plus_0_r; try reflexivity).
    destruct n0. rewrite <- IHa2. simpl. rewrite plus_0_r. reflexivity. reflexivity.
  - simpl. try (destruct a1; try destruct a2; try rewrite IHa1; try rewrite IHa2; try reflexivity).
  - simpl. try (destruct a1; try destruct a2; try rewrite IHa1; try rewrite IHa2; try reflexivity).
Qed.

(*-- Check --*)
Check optimize_0plus_aexp_sound:
  atrans_sound optimize_0plus_aexp.

