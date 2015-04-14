Require Export Assignment05_03.

(* problem #04: 10 points *)



Lemma injinj : forall P Q R : Prop,
    (P -> Q) /\ (Q -> R) -> (P -> R).
Proof.
    intros. inversion H. apply H2 in H1.
    - apply H1.
    - apply H0.
Qed.
Theorem iff_trans : forall P Q R : Prop, 
  (P <-> Q) -> (Q <-> R) -> (P <-> R).
Proof.
    intros. split.
    - intros. apply H in H1. apply H0 in H1. apply H1.
    - intros. apply H0 in H1. apply H in H1. apply H1.
Qed.


