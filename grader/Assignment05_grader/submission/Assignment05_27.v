Require Export Assignment05_26.

(* problem #27: 10 points *)


Theorem even__ev: forall n : nat,
  even n -> ev n.
Proof.
    intros. induction n.
    - apply ev_0.
    - SearchAbout ev. apply even__ev_strong with (n:=(S n)). apply H.
Qed.
(** [] *)


