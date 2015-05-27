Require Export Assignment09_06.

(* problem #07: 10 points *)

(** **** Exercise: 3 stars, optional (add_slowly_decoration)  *)
(** The following program adds the variable X into the variable Z
    by repeatedly decrementing X and incrementing Z.
  WHILE X <> 0 DO
     Z ::= Z + 1;;
     X ::= X - 1
  END

    Following the pattern of the [subtract_slowly] example above, pick
    a precondition and postcondition that give an appropriate
    specification of [add_slowly]; then (informally) decorate the
    program accordingly. *)

Lemma stupid' : forall m n,
  m <> 0 -> m - 1 + (n + 1) = m + n.
Proof.
  intros. induction m.
  unfold not in H. apply ex_falso_quodlibet. apply H. reflexivity.
  simpl. omega. 
Qed.

Theorem slow_addition_dec_correct : forall n m,
  {{fun st => st X = n /\ st Y = m }}
  WHILE BNot (BEq (AId X) (ANum 0)) DO
     Y ::= APlus (AId Y) (ANum 1);;
     X ::= AMinus (AId X) (ANum 1)
  END
  {{fun st => st Y = n + m}}.
Proof.
  intros. apply hoare_consequence_pre with (fun st => st X + st Y = n + m). 
  eapply hoare_consequence_post.
  apply hoare_while.
    eapply hoare_seq. apply hoare_asgn. eapply hoare_consequence_pre. apply hoare_asgn.
      intros st [H1 H2]. unfold assn_sub, update. simpl. rewrite stupid'. assumption. unfold beval in H2. apply negb_true in H2. simpl in H2. apply beq_nat_false in H2. assumption.
      intros st [H1 H2]. unfold beval in H2. apply negb_false in H2. simpl in H2. apply beq_nat_true in H2. rewrite H2 in H1. apply H1. 
      intros st H. omega.
Qed.

(*-- Check --*)
Check slow_addition_dec_correct : forall n m,
  {{fun st => st X = n /\ st Y = m }}
  WHILE BNot (BEq (AId X) (ANum 0)) DO
     Y ::= APlus (AId Y) (ANum 1);;
     X ::= AMinus (AId X) (ANum 1)
  END
  {{fun st => st Y = n + m}}.

