Require Export mid_04.

(* problem #05: 10 points *)

(** Medium:
    Prove the following theorem.
 **)

Lemma app_tail_cancel: forall X (l1 l2: list X) a
    (EQ: l1 ++ [a] = l2 ++ [a]),
  l1 = l2.
Proof.
  Induction l1; intros.
  - destruct l2; auto.
  	destruct l2; inversion EQ.
  - destruct l2.
  	+ destruct l1; inversion EQ.
  	+ simpl in EQ. inversion EQ.
  	  apply IH1 in H1; subst; auto.
Qed.

