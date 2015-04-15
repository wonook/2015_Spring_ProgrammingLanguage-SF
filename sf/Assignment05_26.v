Require Export Assignment05_25.

(* problem #26: 10 points *)











(** 3 star (even__ev)  
    Note that proving [even__ev] directly is hard.
    You might find it easier to prove [even__ev_strong] first
    and then prove [even__ev] using it.
*)

Lemma even_predpred: forall n: nat,
    even n -> even (S (S n)).
Proof.
  intros. induction n.
  - reflexivity.
  - 
Admitted.
Lemma even__ev_strong: forall n : nat, 
  (even (pred n) -> ev (pred n)) /\ (even n -> ev n).
Proof.
    intros. induction n.
    - split. 
      intros. simpl. apply ev_0.
      intros. apply ev_0.
    - split. 
      intros. simpl. apply IHn. simpl in H. apply H.
      intros. replace (ev (S n)) with (ev (pred n)). apply IHn. replace (even (pred n)) with (even (S n)). apply H.
        unfold even.
Admitted.
(** [] *)


