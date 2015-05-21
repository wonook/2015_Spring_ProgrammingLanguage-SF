Require Export Assignment05_11.

(* problem #12: 10 points *)




(** 2 stars (false_beq_nat)  *)
Lemma false_induction : forall P : Prop,
    False -> P.
Proof.
    intros. inversion H.
Qed.

Theorem false_beq_nat : forall n m : nat,
     n <> m ->
     beq_nat n m = false.
Proof.
    (* DIFFICULT *)
    intros n m. unfold not. intros. generalize dependent m. induction n.
    - intros. induction m.
      apply false_induction. apply H. reflexivity.
      simpl. reflexivity.
    - intros. induction m.
      simpl.  reflexivity.
      simpl. apply IHn. intros. apply H. apply f_equal. apply H0.
Qed.
(** [] *)




