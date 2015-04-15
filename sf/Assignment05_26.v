Require Export Assignment05_25.

(* problem #26: 10 points *)











(** 3 star (even__ev)  
    Note that proving [even__ev] directly is hard.
    You might find it easier to prove [even__ev_strong] first
    and then prove [even__ev] using it.
*)

Lemma evenb_SS: forall n: nat,
    evenb n = evenb (S (S n)).
Proof.
  intros. induction n.
  - reflexivity.
  - simpl. reflexivity.
Qed.
Lemma S_pred_n: forall n: nat,
    (pred (S n)) = n.
Proof.
    intros. induction n.
    simpl. reflexivity.
    simpl. reflexivity.
Qed.
Lemma even__ev_strong: forall n : nat, 
  (even (pred n) -> ev (pred n)) /\ (even n -> ev n).
Proof.
    intros. induction n.
    - split. 
      intros. simpl. apply ev_0.
      intros. apply ev_0.
    - split. 
      intros. simpl. apply IHn. simpl in H. apply H.
      intros. inversion IHn. destruct n.
        inversion H.
        inversion H. apply ev_SS. simpl in H0. apply H0. unfold even. apply H3.
Qed.
(** [] *)


