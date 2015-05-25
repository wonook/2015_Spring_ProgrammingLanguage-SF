Require Export Assignment09_05.

(* problem #06: 10 points *)

(** **** Exercise: 2 stars (slow_assignment)  *)
(** A roundabout way of assigning a number currently stored in [X] to
    the variable [Y] is to start [Y] at [0], then decrement [X] until
    it hits [0], incrementing [Y] at each step. Here is a program that
    implements this idea:
      {{ X = m }}
    Y ::= 0;;
    WHILE X <> 0 DO
      X ::= X - 1;;
      Y ::= Y + 1
    END
      {{ Y = m }} 
    Write an informal decorated program showing that this is correct. *)

Lemma stupid : forall m n,
  m <> 0 -> m - 1 + (n + 1) = m + n.
Proof.
  intros. induction m.
  unfold not in H. apply ex_falso_quodlibet. apply H. reflexivity.
  simpl. omega. 
Qed.

Theorem slow_assignment : forall m,
    {{ fun st => st X = m }}
    Y ::= ANum 0;;
    WHILE BNot (BEq (AId X) (ANum 0)) DO
      X ::= AMinus (AId X) (ANum 1);;
      Y ::= APlus (AId Y) (ANum 1)
    END
    {{ fun st => st Y = m }}.
Proof.
  intros. apply hoare_consequence_pre with (fun st => st X + 0 = m). 
  apply hoare_seq with (fun st => st X + st Y = m). eapply hoare_consequence_post.
  apply hoare_while.
    eapply hoare_seq. apply hoare_asgn. eapply hoare_consequence_pre. apply hoare_asgn.
      intros st [H1 H2]. unfold assn_sub, update. simpl. rewrite stupid. assumption. unfold beval in H2. apply negb_true in H2. simpl in H2. apply beq_nat_false in H2. assumption.
      intros st [H1 H2]. unfold beval in H2. apply negb_false in H2. simpl in H2. apply beq_nat_true in H2. rewrite H2 in H1. apply H1. 
      eapply hoare_consequence_pre. eapply hoare_asgn. intros st H. apply H. 
      intros st H. omega.
Qed.

(*-- Check --*)
Check slow_assignment : forall m,
    {{ fun st => st X = m }}
    Y ::= ANum 0;;
    WHILE BNot (BEq (AId X) (ANum 0)) DO
      X ::= AMinus (AId X) (ANum 1);;
      Y ::= APlus (AId Y) (ANum 1)
    END
    {{ fun st => st Y = m }}.
  
