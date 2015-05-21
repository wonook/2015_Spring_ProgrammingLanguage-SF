Require Export Assignment08_10.

(* problem #11: 10 points *)

(** **** Exercise: 2 stars (assign_aequiv)  *)
Lemma update_same : forall n1 x1 x2 (st : state),
  st x1 = n1 ->
    (update st x1 n1) x2 = st x2.
Proof.
  intros. unfold update. rewrite <- H. destruct (eq_id_dec x1 x2).
  - rewrite e. reflexivity.
  - reflexivity.
Qed.

Theorem assign_aequiv : forall X e,
  aequiv (AId X) e -> 
  cequiv SKIP (X ::= e).
Proof.
  intros. split; intros.
  - inversion H0; subst. assert (st' = update st' X (aeval st' e)).
      apply functional_extensionality. intros. rewrite update_same. reflexivity. apply H.
    rewrite H1 at 2. apply E_Ass. reflexivity.
  - inversion H0; subst. assert (st = update st X (aeval st e)).
      apply functional_extensionality. intros. rewrite update_same. reflexivity. apply H.
    rewrite <- H1. apply E_Skip.
Qed.

(*-- Check --*)
Check assign_aequiv : forall X e,
  aequiv (AId X) e -> 
  cequiv SKIP (X ::= e).

