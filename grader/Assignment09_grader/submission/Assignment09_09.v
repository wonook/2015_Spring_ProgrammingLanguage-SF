Require Export Assignment09_08.

(* problem #09: 10 points *)

(** **** Exercise: 4 stars (factorial)  *)
(** Recall that [n!] denotes the factorial of [n] (i.e. [n! =
    1*2*...*n]).  Here is an Imp program that calculates the factorial
    of the number initially stored in the variable [X] and puts it in
    the variable [Y]:
    {{ X = m }} 
  Y ::= 1 ;;
  WHILE X <> 0
  DO
     Y ::= Y * X ;;
     X ::= X - 1
  END
    {{ Y = m! }}

    Fill in the blanks in following decorated program:
    {{ X = m }} ->>
    {{                                      }}
  Y ::= 1;;
    {{                                      }}
  WHILE X <> 0
  DO   {{                                      }} ->>
       {{                                      }}
     Y ::= Y * X;;
       {{                                      }}
     X ::= X - 1
       {{                                      }}
  END
    {{                                      }} ->>
    {{ Y = m! }}
*)

Print fact.

Theorem factorial_dec_correct: forall m,
  {{ fun st => st X = m }} 
  Y ::= ANum 1 ;;
  WHILE BNot (BEq (AId X) (ANum 0))
  DO
     Y ::= AMult (AId Y) (AId X) ;;
     X ::= AMinus (AId X) (ANum 1)
  END
  {{ fun st => st Y = fact m }}.
Proof.
  intros.
  apply hoare_consequence_pre with (fun st => 1 * fact (st X) = fact m).
  apply hoare_seq with (fun st => (st Y) * fact (st X) = fact m). eapply hoare_consequence_post.
  apply hoare_while. eapply hoare_seq. apply hoare_asgn. eapply hoare_consequence_pre. apply hoare_asgn.
    intros st [H1 H2]. unfold assn_sub, update. simpl. assert (st X * fact (st X - 1) = fact (st X)).
      induction (st X) eqn:eqn.
        simpl. unfold beval in H2. apply negb_true in H2. simpl in H2. apply beq_nat_false in H2. unfold not in H2. apply ex_falso_quodlibet. apply H2. assumption.
        simpl. rewrite <- minus_n_O. reflexivity.
      rewrite <- H1. rewrite <- H. symmetry. apply mult_assoc.
    intros st [H1 H2]. unfold beval in H2. apply negb_false in H2. apply beq_nat_true in H2. simpl in H2. rewrite H2 in H1. simpl in H1. rewrite mult_1_r in H1. assumption.
    eapply hoare_consequence_pre. apply hoare_asgn. intros st H. unfold assn_sub, update. simpl. apply H.
    intros st H. rewrite H. omega.
Qed.

(*-- Check --*)
Check factorial_dec_correct: forall m,
  {{ fun st => st X = m }} 
  Y ::= ANum 1 ;;
  WHILE BNot (BEq (AId X) (ANum 0))
  DO
     Y ::= AMult (AId Y) (AId X) ;;
     X ::= AMinus (AId X) (ANum 1)
  END
  {{ fun st => st Y = fact m }}.

