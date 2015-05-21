Require Export Assignment08_08.

(* problem #09: 10 points *)

(** **** Exercise: 2 stars (WHILE_true)  *)
(** Prove the following theorem. _Hint_: You'll want to use
    [WHILE_true_nonterm] here. *)

Lemma WHILE_true_nonterm: forall b c st st',
    bequiv b BTrue -> ~(WHILE b DO c END / st || st').
Proof.
  intros. intros H'. remember (WHILE b DO c END).
  induction H'; inversion Heqc0.
  - subst. rewrite H in H0. inversion H0.
  - subst. apply IHH'2. reflexivity.
Qed.

Theorem WHILE_true: forall b c,
     bequiv b BTrue  ->
     cequiv 
       (WHILE b DO c END)
       (WHILE BTrue DO SKIP END).
Proof.
  intros. split; intros.
  - inversion H0; subst. rewrite H in H5. inversion H5. apply WHILE_true_nonterm in H7. inversion H7. apply H.
  - inversion H0; subst. inversion H5. apply WHILE_true_nonterm in H7. inversion H7. unfold bequiv. reflexivity.
Qed.

(*-- Check --*)
Check WHILE_true: forall b c,
     bequiv b BTrue  ->
     cequiv 
       (WHILE b DO c END)
       (WHILE BTrue DO SKIP END).

