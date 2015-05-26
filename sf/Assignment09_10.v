Require Export Assignment09_09.

(* problem #10: 10 points *)

(** **** Exercise: 3 stars (two_loops)  *)
(** Here is a very inefficient way of adding 3 numbers:
  X ::= 0;;
  Y ::= 0;;
  Z ::= c;;
  WHILE X <> a DO
    X ::= X + 1;;
    Z ::= Z + 1
  END;;
  WHILE Y <> b DO
    Y ::= Y + 1;;
    Z ::= Z + 1
  END

    Show that it does what it should by filling in the blanks in the
    following decorated program.

    {{ True }} ->>
    {{                                        }}
  X ::= 0;;
    {{                                        }}
  Y ::= 0;;
    {{                                        }}
  Z ::= c;;
    {{                                        }}
  WHILE X <> a DO
      {{                                        }} ->>
      {{                                        }}
    X ::= X + 1;;
      {{                                        }}
    Z ::= Z + 1
      {{                                        }}
  END;;
    {{                                        }} ->>
    {{                                        }}
  WHILE Y <> b DO
      {{                                        }} ->>
      {{                                        }}
    Y ::= Y + 1;;
      {{                                        }}
    Z ::= Z + 1
      {{                                        }}
  END
    {{                                        }} ->>
    {{ Z = a + b + c }}
*)

Theorem add_three_numbers_correct: forall a b c,
  {{ fun st => True }}                                   
  X ::= ANum 0;;
  Y ::= ANum 0;;
  Z ::= ANum c;;
  WHILE BNot (BEq (AId X) (ANum a)) DO
    X ::= APlus (AId X) (ANum 1);;
    Z ::= APlus (AId Z) (ANum 1)
  END;;
  WHILE BNot (BEq (AId Y) (ANum b)) DO
    Y ::= APlus (AId Y) (ANum 1);;
    Z ::= APlus (AId Z) (ANum 1)
  END
  {{ fun st => st Z = a + b + c }}.
Proof.
  intros.
  apply hoare_consequence_pre with (fun st => c = 0 + 0 + c).
  apply hoare_seq with (fun st => c = (st X) + 0 + c).
  apply hoare_seq with (fun st => c = st X + st Y + c).
  apply hoare_seq with (fun st => st Z = st X + st Y + c).
  apply hoare_seq with (fun st => st Z = a + st Y + c). 
  eapply hoare_consequence_post.
    apply hoare_while. apply hoare_consequence_pre with (fun st => (st Z + 1) = a + (st Y + 1) + c).
      eapply hoare_seq. apply hoare_asgn. eapply hoare_consequence_pre. apply hoare_asgn.
      intros st H. unfold assn_sub, update; simpl. assumption.
    intros st [H1 H2]. omega.
  intros st [H1 H2]. unfold beval in H2. apply negb_false in H2. apply beq_nat_true in H2. simpl in H2. rewrite H2 in H1. assumption.
  eapply hoare_consequence_post.
    apply hoare_while. apply hoare_consequence_pre with (fun st => (st Z + 1) = (st X + 1) + st Y + c).
      eapply hoare_seq. apply hoare_asgn. eapply hoare_consequence_pre. apply hoare_asgn.
      intros st H. unfold assn_sub, update; simpl. assumption.
    intros st [H1 H2]. omega.
  intros st [H1 H2]. unfold beval in H2. apply negb_false in H2. apply beq_nat_true in H2. simpl in H2. rewrite H2 in H1. assumption.
  eapply hoare_consequence_pre. apply hoare_asgn.
    intros st H. unfold assn_sub, update; simpl. assumption.
  eapply hoare_consequence_pre. apply hoare_asgn.
    intros st H. unfold assn_sub, update; simpl. assumption.
  eapply hoare_consequence_pre. apply hoare_asgn.
    intros st H. unfold assn_sub, update; simpl. assumption.
  intros st H. simpl. reflexivity.
Qed.

(*-- Check --*)
Check add_three_numbers_correct: forall a b c,
  {{ fun st => True }}                                   
  X ::= ANum 0;;
  Y ::= ANum 0;;
  Z ::= ANum c;;
  WHILE BNot (BEq (AId X) (ANum a)) DO
    X ::= APlus (AId X) (ANum 1);;
    Z ::= APlus (AId Z) (ANum 1)
  END;;
  WHILE BNot (BEq (AId Y) (ANum b)) DO
    Y ::= APlus (AId Y) (ANum 1);;
    Z ::= APlus (AId Z) (ANum 1)
  END
  {{ fun st => st Z = a + b + c }}.

