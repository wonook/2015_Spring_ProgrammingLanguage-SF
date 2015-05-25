Require Export Assignment09_00.

(* problem #01: 10 points *)

(** **** Exercise: 2 stars (hoare_asgn_examples)  *)

Theorem assn_sub_ex1: 
  {{ (fun st => st X <= 5) [X |-> APlus (AId X) (ANum 1)] }}
      X ::= APlus (AId X) (ANum 1)
  {{ fun st => st X <= 5 }}.
Proof.
  unfold hoare_triple. unfold assn_sub. simpl. intros.
  inversion H; subst. simpl. apply H0.
Qed.

(*-- Check --*)
Check assn_sub_ex1: 
  {{ (fun st => st X <= 5) [X |-> APlus (AId X) (ANum 1)] }}
      X ::= APlus (AId X) (ANum 1)
  {{ fun st => st X <= 5 }}.


(*Require Export Assignment09_01.*)

(* problem #02: 10 points *)

Theorem assn_sub_ex2:
  {{ (fun st => 0 <= st X /\ st X <= 5) [X |-> ANum 3] }}
     X ::= ANum 3
  {{ fun st => 0 <= st X /\ st X <= 5 }}.
Proof.
  unfold hoare_triple. unfold assn_sub. simpl. intros.
  inversion H; subst. simpl. apply H0.
Qed.

(*-- Check --*)
Check assn_sub_ex2:
  {{ (fun st => 0 <= st X /\ st X <= 5) [X |-> ANum 3] }}
     X ::= ANum 3
  {{ fun st => 0 <= st X /\ st X <= 5 }}.


(*Require Export Assignment09_02.*)

(* problem #03: 10 points *)

(** **** Exercise: 4 stars (hoare_asgn_wrong)  *)
(** The assignment rule looks backward to almost everyone the first
    time they see it.  If it still seems backward to you, it may help
    to think a little about alternative "forward" rules.  Here is a
    seemingly natural one:
      ------------------------------ (hoare_asgn_wrong)
      {{ True }} X ::= a {{ X = a }}
    Give a counterexample showing that this rule is incorrect
    (informally). Hint: The rule universally quantifies over the
    arithmetic expression [a], and your counterexample needs to
    exhibit an [a] for which the rule doesn't work. *)

Theorem hoare_asgn_wrong:
  exists a, ~ {{ fun st => True }} X ::= a {{ fun st => st X = aeval st a}}.
Proof.
  unfold hoare_triple. exists (APlus (AId X ) (ANum 1)). 
  simpl. unfold not. intros. 
  assert ((X ::= APlus (AId X) (ANum 1)) / empty_state || update empty_state X 1).
    apply E_Ass. auto.
  assert (update empty_state X 1 X = aeval (update empty_state X 1) (APlus (AId X) (ANum 1))).
    apply H with empty_state; auto.
  simpl in H1. rewrite update_eq in H1. inversion H1.
Qed.

(*-- Check --*)
Check hoare_asgn_wrong:
  exists a, ~ {{ fun st => True }} X ::= a {{ fun st => st X = aeval st a}}.


(*Require Export Assignment09_03.*)

(* problem #04: 10 points *)

(** **** Exercise: 2 stars (hoare_asgn_example4)  *)
(** Translate this "decorated program" into a formal proof:
                   {{ True }} ->>
                   {{ 1 = 1 }}
    X ::= 1;;
                   {{ X = 1 }} ->>
                   {{ X = 1 /\ 2 = 2 }}
    Y ::= 2
                   {{ X = 1 /\ Y = 2 }}
*)

Example hoare_asgn_example4 :
  {{fun st => True}} (X ::= (ANum 1);; Y ::= (ANum 2)) 
  {{fun st => st X = 1 /\ st Y = 2}}.
Proof.
  eapply hoare_seq.
    apply hoare_asgn.
    eapply hoare_consequence.
      apply hoare_asgn.
      intros st H. assert (((fun st : state => st X = 1) [X |-> ANum 1]) st). reflexivity. apply H0.
      intros st H. unfold assn_sub. simpl. unfold update. split.
        destruct (eq_id_dec Y X). inversion e. apply H.
        destruct (eq_id_dec Y Y). reflexivity. unfold not in n. apply ex_falso_quodlibet. apply n. reflexivity.
Qed.

(*-- Check --*)
Check hoare_asgn_example4 :
  {{fun st => True}} (X ::= (ANum 1);; Y ::= (ANum 2)) 
  {{fun st => st X = 1 /\ st Y = 2}}.


(*Require Export Assignment09_04.*)

(* problem #05: 10 points *)

(** **** Exercise: 2 stars (if_minus_plus)  *)
(** Prove the following hoare triple using [hoare_if]: *)

Theorem if_minus_plus :
  {{fun st => True}}
  IFB (BLe (AId X) (AId Y))
    THEN (Z ::= AMinus (AId Y) (AId X))
    ELSE (Y ::= APlus (AId X) (AId Z))
  FI
  {{fun st => st Y = st X + st Z}}. 
Proof.
  eapply hoare_consequence_pre.
    apply hoare_if. 
      apply hoare_asgn. apply hoare_asgn.
      unfold assn_sub, update, assert_implies. simpl.
        intros. split. 
          destruct (ble_nat (st X) (st Y)) eqn:eqn. 
            intros. apply le_plus_minus. apply ble_nat_true in eqn. apply eqn.
            intros. inversion H0.
          destruct (ble_nat (st X) (st Y)) eqn:eqn.
            intros. inversion H0.
            intros. reflexivity.
Qed.

(*-- Check --*)
Check if_minus_plus :
  {{fun st => True}}
  IFB (BLe (AId X) (AId Y))
    THEN (Z ::= AMinus (AId Y) (AId X))
    ELSE (Y ::= APlus (AId X) (AId Z))
  FI
  {{fun st => st Y = st X + st Z}}. 


(*Require Export Assignment09_05.*)

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
  

(*Require Export Assignment09_06.*)

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


(*Require Export Assignment09_07.*)

(* problem #08: 10 points *)

(** The postcondition does not hold at the beginning of the loop,
    since [m = parity m] does not hold for an arbitrary [m], so we
    cannot use that as an invariant.  To find an invariant that works,
    let's think a bit about what this loop does.  On each iteration it
    decrements [X] by [2], which preserves the parity of [X].  So the
    parity of [X] does not change, i.e. it is invariant.  The initial
    value of [X] is [m], so the parity of [X] is always equal to the
    parity of [m]. Using [parity X = parity m] as an invariant we
    obtain the following decorated program:
    {{ X = m }} ->>                              (a - OK)
    {{ parity X = parity m }}
  WHILE 2 <= X DO
      {{ parity X = parity m /\ 2 <= X }}  ->>    (c - OK)
      {{ parity (X-2) = parity m }}
    X ::= X - 2
      {{ parity X = parity m }}
  END
    {{ parity X = parity m /\ X < 2 }}  ->>       (b - OK)
    {{ X = parity m }}

    With this invariant, conditions (a), (b), and (c) are all
    satisfied. For verifying (b), we observe that, when [X < 2], we
    have [parity X = X] (we can easily see this in the definition of
    [parity]).  For verifying (c), we observe that, when [2 <= X], we
    have [parity X = parity (X-2)]. *)


(** **** Exercise: 3 stars, optional (parity_formal)  *)
(** Translate this proof to Coq. Refer to the reduce-to-zero example
    for ideas. You may find the following two lemmas useful: *)

Lemma parity_ge_2 : forall x,
  2 <= x ->
  parity (x - 2) = parity x.
Proof.
  induction x; intro. reflexivity.
  destruct x. inversion H. inversion H1.
  simpl. rewrite <- minus_n_O. reflexivity.
Qed.

Lemma parity_lt_2 : forall x,
  ~ 2 <= x ->
  parity (x) = x.
Proof.
  intros. induction x. reflexivity. destruct x. reflexivity.
    apply ex_falso_quodlibet. apply H. omega.
Qed.

Theorem parity_correct : forall m,
    {{ fun st => st X = m }}
  WHILE BLe (ANum 2) (AId X) DO
    X ::= AMinus (AId X) (ANum 2)
  END
    {{ fun st => st X = parity m }}.
Proof.
  intros. 
  apply hoare_consequence_pre with (fun st => parity (st X) = parity m). 
  eapply hoare_consequence_post.
  apply hoare_while. 
    eapply hoare_consequence_pre. apply hoare_asgn.
    intros st [H1 H2]. unfold assn_sub. simpl. rewrite update_eq. rewrite parity_ge_2. assumption. apply ble_nat_true. apply H2.
  intros st [H1 H2]. rewrite <- H1. symmetry. rewrite <- parity_lt_2. reflexivity. unfold beval in H2. apply ble_nat_false in H2. simpl in H2. assumption.
  intros st H. rewrite H. reflexivity.
Qed.

(*-- Check --*)
Check parity_correct : forall m,
    {{ fun st => st X = m }}
  WHILE BLe (ANum 2) (AId X) DO
    X ::= AMinus (AId X) (ANum 2)
  END
    {{ fun st => st X = parity m }}.


(*Require Export Assignment09_08.*)

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
  exact FILL_IN_HERE.
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


(*Require Export Assignment09_09.*)

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
  exact FILL_IN_HERE.
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


(*Require Export Assignment09_10.*)

(* problem #11: 10 points *)

(** **** Exercise: 3 stars, advanced, optional (is_wp_formal)  *)
(** Prove formally using the definition of [hoare_triple] that [Y <= 4]
   is indeed the weakest precondition of [X ::= Y + 1] with respect to
   postcondition [X <= 5]. *)

Theorem is_wp_example :
  is_wp (fun st => st Y <= 4)
    (X ::= APlus (AId Y) (ANum 1)) (fun st => st X <= 5).
Proof.
  exact FILL_IN_HERE.
Qed.

(*-- Check --*)
Check is_wp_example :
  is_wp (fun st => st Y <= 4)
    (X ::= APlus (AId Y) (ANum 1)) (fun st => st X <= 5).


(*Require Export Assignment09_11.*)

(* problem #12: 10 points *)

(** **** Exercise: 2 stars, advanced (hoare_asgn_weakest)  *)
(** Show that the precondition in the rule [hoare_asgn] is in fact the
    weakest precondition. *)

Theorem hoare_asgn_weakest : forall Q X a,
  is_wp (Q [X |-> a]) (X ::= a) Q.
Proof.
  exact FILL_IN_HERE.
Qed.

(*-- Check --*)
Check hoare_asgn_weakest : forall Q X a,
  is_wp (Q [X |-> a]) (X ::= a) Q.
