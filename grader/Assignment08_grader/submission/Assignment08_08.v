Require Export Assignment08_07.

(* problem #08: 10 points *)

(** **** Exercise: 3 stars (swap_if_branches)  *)
(** Show that we can swap the branches of an IF by negating its
    condition *)

Theorem swap_if_branches: forall b e1 e2,
  cequiv
    (IFB b THEN e1 ELSE e2 FI)
    (IFB BNot b THEN e2 ELSE e1 FI).
Proof.
  intros. split; intros.
  - inversion H; subst. 
    apply E_IfFalse. simpl. rewrite H5. reflexivity. apply H6.
    apply E_IfTrue. simpl. rewrite H5. reflexivity. apply H6.
  - inversion H; subst.
    apply E_IfFalse. simpl in H5. symmetry. rewrite negb_involutive_reverse. rewrite H5. reflexivity. apply H6.
    apply E_IfTrue. simpl in H5. symmetry. rewrite negb_involutive_reverse. rewrite H5. reflexivity. apply H6.
Qed.

(*-- Check --*)
Check swap_if_branches: forall b e1 e2,
  cequiv
    (IFB b THEN e1 ELSE e2 FI)
    (IFB BNot b THEN e2 ELSE e1 FI).

