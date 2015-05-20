Require Export Assignment08_00.

(* problem #01: 10 points *)

(** **** Exercise: 2 stars (ceval_example2)  *)
Example ceval_example2:
    (X ::= ANum 0;; 
    Y ::= ANum 1;; 
    Z ::= ANum 2) / empty_state ||
    (update (update (update empty_state X 0) Y 1) Z 2).
Proof.
  apply E_Seq with (update empty_state X 0).
  - apply E_Ass. reflexivity.
  - apply E_Seq with (update (update empty_state X 0) Y 1).
    + apply E_Ass. reflexivity.
    + apply E_Ass. reflexivity.
Qed.

(*-- Check --*)
Check ceval_example2 : 
    (X ::= ANum 0;; Y ::= ANum 1;; Z ::= ANum 2) / empty_state ||
    (update (update (update empty_state X 0) Y 1) Z 2).


(*Require Export Assignment08_01.*)

(* problem #02: 10 points *)

(** **** Exercise: 3 stars, advanced (pup_to_n)  *)
(** Write an Imp program that sums the numbers from [1] to
   [X] (inclusive: [1 + 2 + ... + X]) in the variable [Y].
   Prove that this program executes as intended for X = 2
   (this latter part is trickier than you might expect). *)

Definition pup_to_n : com :=
  Y ::= (ANum 0);;
  WHILE BNot (BEq (ANum 0) (AId X)) DO
    Y ::= (APlus (AId X) (AId Y));;
    X ::= (AMinus (AId X) (ANum 1))
  END.

Example pup_to_2_ceval :
  pup_to_n / (update empty_state X 2) ||
    update (update (update (update (update (update empty_state
      X 2) Y 0) Y 2) X 1) Y 3) X 0.
Proof.
  unfold pup_to_n.
  apply E_Seq with (update (update empty_state X 2) Y 0).
  - apply E_Ass. reflexivity.
  - apply E_WhileLoop with (update (update (update (update empty_state X 2) Y 0) Y 2) X 1).
    + reflexivity.
    + apply E_Seq with (update (update (update empty_state X 2) Y 0) Y 2).
      * apply E_Ass. reflexivity.
      * apply E_Ass. reflexivity.
    + apply E_WhileLoop with (update (update (update (update (update (update empty_state X 2) Y 0) Y 2) X 1) Y 3) X 0).
      * reflexivity.
      * apply E_Seq with (update (update (update (update (update empty_state X 2) Y 0) Y 2) X 1) Y 3).
        apply E_Ass. reflexivity.
        apply E_Ass. reflexivity.
      * apply E_WhileEnd. reflexivity.
Qed.

(*-- Check --*)
Check pup_to_2_ceval :
  pup_to_n / (update empty_state X 2) ||
    update (update (update (update (update (update empty_state
      X 2) Y 0) Y 2) X 1) Y 3) X 0.
 

(*Require Export Assignment08_02.*)

(* problem #03: 10 points *)

(** **** Exercise: 3 stars (loop_never_stops)  *)
Theorem loop_never_stops : forall st st',
  ~(loop / st || st').
Proof.
  intros st st' contra. unfold loop in contra.
  remember (WHILE BTrue DO SKIP END) as loopdef eqn:Heqloopdef.
    (* Proceed by induction on the assumed derivation showing that
     [loopdef] terminates.  Most of the cases are immediately
     contradictory (and so can be solved in one step with
     [inversion]). *)
  induction contra; try (inversion Heqloopdef).
  rewrite H1 in H. inversion H.
  apply IHcontra2. rewrite H1. rewrite H2. reflexivity.
Qed.

(*-- Check --*)
Check loop_never_stops : forall st st',
  ~(loop / st || st').


(*Require Export Assignment08_03.*)

(* problem #04: 10 points *)

(** **** Exercise: 4 stars (no_whiles_terminating)  *)
(** Imp programs that don't involve while loops always terminate.
    State and prove a theorem [no_whiles_terminating] that says this. *)

(* Hint *)
Check andb_true_iff.

Theorem no_whiles_terminate: forall c st
    (NOWHL: no_whiles c = true),
  exists st', c / st || st'.
Proof.
  intros. generalize dependent st.
  induction c.
  - intros. exists st. apply E_Skip.
  - intros. exists (update st i (aeval st a)). apply E_Ass. reflexivity.
  - intros.
    assert (exists st' : state, c1 / st || st'). apply IHc1. simpl in NOWHL. rewrite andb_true_iff in NOWHL. apply NOWHL.
    inversion H.
    assert (exists st' : state, c2 / x || st'). apply IHc2. simpl in NOWHL. rewrite andb_true_iff in NOWHL. apply NOWHL.
    inversion H1.
    exists x0. apply E_Seq with x. apply H0. apply H2.
  - intros.
    assert (exists st' : state, c1 / st || st'). apply IHc1. simpl in NOWHL. rewrite andb_true_iff in NOWHL. apply NOWHL.
    assert (exists st' : state, c2 / st || st'). apply IHc2. simpl in NOWHL. rewrite andb_true_iff in NOWHL. apply NOWHL.
    remember (beval st b). destruct b0.
    inversion H. exists x. apply E_IfTrue. symmetry. apply Heqb0. apply H1.
    inversion H0. exists x. apply E_IfFalse. symmetry. apply Heqb0. apply H1.
  - inversion NOWHL.
Qed.

(*-- Check --*)
Check no_whiles_terminate: forall c st
    (NOWHL: no_whiles c = true),
  exists st', c / st || st'.


(*Require Export Assignment08_04.*)

(* problem #05: 20 points *)

(** Write a function which compiles an [aexp] into a stack
    machine program. The effect of running the program should be the
    same as pushing the value of the expression on the stack. *)

Fixpoint s_compile (e : aexp) : list sinstr :=
  match e with
  | ANum n => [SPush n]
  | AId i => [SLoad i]
  | APlus a1 a2 => (s_compile a1)++(s_compile a2)++[SPlus]
  | AMinus a1 a2 => (s_compile a1)++(s_compile a2)++[SMinus]
  | AMult a1 a2 => (s_compile a1)++(s_compile a2)++[SMult]
  end.

(** After you've defined [s_compile], prove the following to test
    that it works. *)

Example s_compile1 :
    s_compile (AMinus (AId X) (AMult (ANum 2) (AId Y)))
  = [SLoad X; SPush 2; SLoad Y; SMult; SMinus].
Proof.
  reflexivity.
Qed.

(** **** Exercise: 3 stars, advanced (stack_compiler_correct)  *)
(** The task of this exercise is to prove the correctness of the
    compiler implemented in the previous exercise.  Remember that
    the specification left unspecified what to do when encountering an
    [SPlus], [SMinus], or [SMult] instruction if the stack contains
    less than two elements.  (In order to make your correctness proof
    easier you may find it useful to go back and change your
    implementation!)

    Prove the following theorem, stating that the [compile] function
    behaves correctly.  You will need to start by stating a more
    general lemma to get a usable induction hypothesis; the main
    theorem will then be a simple corollary of this lemma. *)

Lemma s_compile_app : forall (st : state) (nl: list nat) (l1 l2 : list sinstr),
  s_execute st nl (l1 ++ l2) = s_execute st (s_execute st nl l1) l2.
Proof.
  intros. generalize dependent nl. induction l1.
  - reflexivity.
  - simpl. intros. destruct a.
    + apply IHl1.
    + apply IHl1.
    + destruct nl.
      * apply IHl1.
      * destruct nl. apply IHl1. apply IHl1.
    + destruct nl.
      * apply IHl1.
      * destruct nl. apply IHl1. apply IHl1.
    + destruct nl.
      * apply IHl1.
      * destruct nl. apply IHl1. apply IHl1.
Qed.
Lemma s_compile_correct0 : forall (st: state) (e:aexp) (nl:list nat),
  s_execute st nl (s_compile e) = aeval st e :: nl.
Proof.
  intros. generalize dependent nl. induction e; try (reflexivity); simpl.
  - intros. repeat (rewrite s_compile_app). rewrite IHe1. rewrite IHe2. reflexivity.
  - intros. repeat (rewrite s_compile_app). rewrite IHe1. rewrite IHe2. reflexivity.
  - intros. repeat (rewrite s_compile_app). rewrite IHe1. rewrite IHe2. reflexivity.
Qed.
Theorem s_compile_correct : forall (st : state) (e : aexp),
  s_execute st [] (s_compile e) = [ aeval st e ].
Proof.
  intros. apply s_compile_correct0.
Qed.

(*-- Check --*)
Check s_compile1 :
    s_compile (AMinus (AId X) (AMult (ANum 2) (AId Y)))
  = [SLoad X; SPush 2; SLoad Y; SMult; SMinus].

Check s_compile_correct : forall (st : state) (e : aexp),
  s_execute st [] (s_compile e) = [ aeval st e ].


(*Require Export Assignment08_05.*)

(* problem #06: 10 points *)

(** **** Exercise: 2 stars (skip_right)  *)
(** Prove that adding a SKIP after a command results in an equivalent
    program *)

Theorem skip_right: forall c,
  cequiv 
    (c;; SKIP) 
    c.
Proof. 
  intros c st st'.
  split; intros.
  - inversion H. subst. inversion H5. subst. assumption.
  - apply E_Seq with st'. assumption. apply E_Skip.
Qed.

(*-- Check --*)
Check skip_right: forall c,
  cequiv 
    (c;; SKIP) 
    c.


(*Require Export Assignment08_06.*)

(* problem #07: 10 points *)

(** **** Exercise: 2 stars (IFB_false)  *)
Theorem IFB_false: forall b c1 c2,
  bequiv b BFalse  ->
  cequiv 
    (IFB b THEN c1 ELSE c2 FI) 
    c2.
Proof.
  intros b c1 c2. split; intros.
  - inversion H0; subst. 
    unfold bequiv in H. simpl in H. rewrite H in H6. inversion H6.
    apply H7.
  - apply E_IfFalse. 
    unfold bequiv in H. apply H.
    apply H0.
Qed.

(*-- Check --*)
Check IFB_false: forall b c1 c2,
  bequiv b BFalse  ->
  cequiv 
    (IFB b THEN c1 ELSE c2 FI) 
    c2.


(*Require Export Assignment08_07.*)

(* problem #08: 10 points *)

(** **** Exercise: 3 stars (swap_if_branches)  *)
(** Show that we can swap the branches of an IF by negating its
    condition *)

Theorem swap_if_branches: forall b e1 e2,
  cequiv
    (IFB b THEN e1 ELSE e2 FI)
    (IFB BNot b THEN e2 ELSE e1 FI).
Proof.
  intros. split; intros.
  - inversion H; subst. 
    apply E_IfFalse. simpl. rewrite H5. reflexivity. apply H6.
    apply E_IfTrue. simpl. rewrite H5. reflexivity. apply H6.
  - inversion H; subst.
    apply E_IfFalse. simpl in H5. symmetry. rewrite negb_involutive_reverse. rewrite H5. reflexivity. apply H6.
    apply E_IfTrue. simpl in H5. symmetry. rewrite negb_involutive_reverse. rewrite H5. reflexivity. apply H6.
Qed.

(*-- Check --*)
Check swap_if_branches: forall b e1 e2,
  cequiv
    (IFB b THEN e1 ELSE e2 FI)
    (IFB BNot b THEN e2 ELSE e1 FI).


(*Require Export Assignment08_08.*)

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


(*Require Export Assignment08_09.*)

(* problem #10: 10 points *)

(** **** Exercise: 2 stars, optional (seq_assoc)  *)
Theorem seq_assoc : forall c1 c2 c3,
  cequiv ((c1;;c2);;c3) (c1;;(c2;;c3)).
Proof.
  intros. split; intros.
  - inversion H; subst. inversion H5; subst. 
    inversion H2; subst. apply E_Seq with st'0. apply H3. apply E_Seq with st'. apply H7. apply E_Skip.
    inversion H2; subst. apply E_Seq with st'. apply H3. apply E_Seq with st'0. apply H7. apply E_Ass. reflexivity.
    inversion H2; subst. apply E_Seq with st'2. apply H6. apply E_Seq with st'0. apply H9. apply E_Seq with st'1. apply H0. apply H1.
    inversion H2; subst. apply E_Seq with st'1. apply H6. apply E_Seq with st'0. apply H9. apply E_IfTrue. apply H0. apply H1.
    inversion H2; subst. apply E_Seq with st'1. apply H6. apply E_Seq with st'0. apply H9. apply E_IfFalse. apply H0. apply H1.
    inversion H2; subst. apply E_Seq with st'0. apply H4. apply E_Seq with st'. apply H8. apply E_WhileEnd. apply H0. 
    inversion H2; subst. apply E_Seq with st'2. apply H7. apply E_Seq with st'0. apply H10. assumption.
  - inversion H; subst. inversion H5; subst.
    apply E_Seq with st'1. apply E_Seq with st'0. assumption. assumption. assumption.
Qed.

(*-- Check --*)
Check seq_assoc : forall c1 c2 c3,
  cequiv ((c1;;c2);;c3) (c1;;(c2;;c3)).


(*Require Export Assignment08_10.*)

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


(*Require Export Assignment08_11.*)

(* problem #12: 10 points *)

(** **** Exercise: 3 stars, optional (CSeq_congruence)  *)
Theorem CSeq_congruence : forall c1 c1' c2 c2',
  cequiv c1 c1' -> cequiv c2 c2' ->
  cequiv (c1;;c2) (c1';;c2').
Proof. 
  intros. split; intros.
  - inversion H1; subst. apply E_Seq with st'0. apply H. apply H4. apply H0. apply H7.
  - inversion H1; subst. apply E_Seq with st'0. apply H. apply H4. apply H0. apply H7.
Qed.

(*-- Check --*)
Check CSeq_congruence : forall c1 c1' c2 c2',
  cequiv c1 c1' -> cequiv c2 c2' ->
  cequiv (c1;;c2) (c1';;c2').


(*Require Export Assignment08_12.*)

(* problem #13: 10 points *)

(** **** Exercise: 3 stars (CIf_congruence)  *)
Theorem CIf_congruence : forall b b' c1 c1' c2 c2',
  bequiv b b' -> cequiv c1 c1' -> cequiv c2 c2' ->
  cequiv (IFB b THEN c1 ELSE c2 FI) (IFB b' THEN c1' ELSE c2' FI).
Proof.
  intros. split; intros.
  - inversion H2; subst. 
    apply E_IfTrue. rewrite <- H. assumption. apply H0. assumption.
    apply E_IfFalse. rewrite <- H. assumption. apply H1. assumption.
  - inversion H2; subst.
    apply E_IfTrue. rewrite H. assumption. apply H0. assumption.
    apply E_IfFalse. rewrite H. assumption. apply H1. assumption.
Qed.

(*-- Check --*)
Check CIf_congruence : forall b b' c1 c1' c2 c2',
  bequiv b b' -> cequiv c1 c1' -> cequiv c2 c2' ->
  cequiv (IFB b THEN c1 ELSE c2 FI) (IFB b' THEN c1' ELSE c2' FI).


(*Require Export Assignment08_13.*)

(* problem #14: 10 points *)

(** **** Exercise: 3 stars, optional (fold_bexp_Eq_informal)  *)
(** Here is an informal proof of the [BEq] case of the soundness
    argument for boolean expression constant folding.  Read it
    carefully and compare it to the formal proof that follows.  Then
    fill in the [BLe] case of the formal proof (without looking at the
    [BEq] case, if possible).

   _Theorem_: The constant folding function for booleans,
   [fold_constants_bexp], is sound.

   _Proof_: We must show that [b] is equivalent to [fold_constants_bexp],
   for all boolean expressions [b].  Proceed by induction on [b].  We
   show just the case where [b] has the form [BEq a1 a2].

   In this case, we must show 
       beval st (BEq a1 a2) 
     = beval st (fold_constants_bexp (BEq a1 a2)).
   There are two cases to consider:

     - First, suppose [fold_constants_aexp a1 = ANum n1] and
       [fold_constants_aexp a2 = ANum n2] for some [n1] and [n2].

       In this case, we have
           fold_constants_bexp (BEq a1 a2) 
         = if beq_nat n1 n2 then BTrue else BFalse
       and
           beval st (BEq a1 a2) 
         = beq_nat (aeval st a1) (aeval st a2).
       By the soundness of constant folding for arithmetic
       expressions (Lemma [fold_constants_aexp_sound]), we know
           aeval st a1 
         = aeval st (fold_constants_aexp a1) 
         = aeval st (ANum n1) 
         = n1
       and
           aeval st a2 
         = aeval st (fold_constants_aexp a2) 
         = aeval st (ANum n2) 
         = n2,
       so
           beval st (BEq a1 a2) 
         = beq_nat (aeval a1) (aeval a2)
         = beq_nat n1 n2.
       Also, it is easy to see (by considering the cases [n1 = n2] and
       [n1 <> n2] separately) that
           beval st (if beq_nat n1 n2 then BTrue else BFalse)
         = if beq_nat n1 n2 then beval st BTrue else beval st BFalse
         = if beq_nat n1 n2 then true else false
         = beq_nat n1 n2.
       So
           beval st (BEq a1 a2) 
         = beq_nat n1 n2.
         = beval st (if beq_nat n1 n2 then BTrue else BFalse),
]]         
       as required.

     - Otherwise, one of [fold_constants_aexp a1] and
       [fold_constants_aexp a2] is not a constant.  In this case, we
       must show
           beval st (BEq a1 a2) 
         = beval st (BEq (fold_constants_aexp a1)
                         (fold_constants_aexp a2)),
       which, by the definition of [beval], is the same as showing
           beq_nat (aeval st a1) (aeval st a2) 
         = beq_nat (aeval st (fold_constants_aexp a1))
                   (aeval st (fold_constants_aexp a2)).
       But the soundness of constant folding for arithmetic
       expressions ([fold_constants_aexp_sound]) gives us
         aeval st a1 = aeval st (fold_constants_aexp a1)
         aeval st a2 = aeval st (fold_constants_aexp a2),
       completing the case.  []
*)

Theorem fold_constants_bexp_sound: 
  btrans_sound fold_constants_bexp.
Proof.
  unfold btrans_sound. intros b. unfold bequiv. intros st.
  bexp_cases (induction b) Case; 
    (* BTrue and BFalse are immediate *)
    try reflexivity. 
  Case "BEq". 
    (* Doing induction when there are a lot of constructors makes
       specifying variable names a chore, but Coq doesn't always
       choose nice variable names.  We can rename entries in the
       context with the [rename] tactic: [rename a into a1] will
       change [a] to [a1] in the current goal and context. *)
    rename a into a1. rename a0 into a2. simpl.
    remember (fold_constants_aexp a1) as a1' eqn:Heqa1'.
    remember (fold_constants_aexp a2) as a2' eqn:Heqa2'.
    replace (aeval st a1) with (aeval st a1') by
       (subst a1'; rewrite <- fold_constants_aexp_sound; reflexivity).
    replace (aeval st a2) with (aeval st a2') by
       (subst a2'; rewrite <- fold_constants_aexp_sound; reflexivity).
    destruct a1'; destruct a2'; try reflexivity.
      (* The only interesting case is when both a1 and a2 
         become constants after folding *)
      simpl. destruct (beq_nat n n0); reflexivity.
  Case "BLe". 
    simpl.
    remember (fold_constants_aexp a) as a' eqn:Heqa'.
    remember (fold_constants_aexp a0) as a0' eqn:Heqa0'.
    replace (aeval st a) with (aeval st a'). replace (aeval st a0) with (aeval st a0').
    destruct a'; destruct a0'; try reflexivity.
      simpl. destruct (ble_nat n n0); reflexivity.
        subst a0'. rewrite <- fold_constants_aexp_sound. reflexivity.
        subst a'. rewrite <- fold_constants_aexp_sound. reflexivity.
  Case "BNot". 
    simpl. remember (fold_constants_bexp b) as b' eqn:Heqb'. 
    rewrite IHb.
    destruct b'; reflexivity. 
  Case "BAnd". 
    simpl. 
    remember (fold_constants_bexp b1) as b1' eqn:Heqb1'. 
    remember (fold_constants_bexp b2) as b2' eqn:Heqb2'.
    rewrite IHb1. rewrite IHb2.
    (***
     Note how we use the tactic [eauto].
     ***)
    destruct b1'; destruct b2'; simpl; try reflexivity
    ; eauto using andb_true_l, andb_true_r, andb_false_l, andb_false_r.
Qed.

(*-- Check --*)
Check fold_constants_bexp_sound: 
  btrans_sound fold_constants_bexp.


(*Require Export Assignment08_14.*)

(* problem #15: 10 points *)

(** **** Exercise: 3 stars (fold_constants_com_sound)  *)
(** Complete the [WHILE] case of the following proof. *)

Theorem WHILE_false : forall b c,
    bequiv b BFalse ->
    cequiv
    (WHILE b DO c END)
    SKIP.
Proof. 
    intros b c Hb. split; intros H.
    Case "->".
    inversion H; subst.
    SCase "E_WhileEnd".
    apply E_Skip.
    SCase "E_WhileLoop".
    rewrite Hb in H2. inversion H2.
    Case "<-".
    inversion H; subst.
    apply E_WhileEnd.
    rewrite Hb.
reflexivity.  Qed.

Theorem fold_constants_com_sound : 
  ctrans_sound fold_constants_com.
Proof. 
  unfold ctrans_sound. intros c. 
  com_cases (induction c) Case; simpl.
  Case "SKIP". apply refl_cequiv.
  Case "::=". apply CAss_congruence. apply fold_constants_aexp_sound.
  Case ";;". 
    (***
     Note how we use the tactic [eauto].
     ***)
   destruct c1; destruct c2; try (apply CSeq_congruence; assumption)
   ; eauto using skip_left, skip_right.
  Case "IFB". 
    assert (bequiv b (fold_constants_bexp b)).
      SCase "Pf of assertion". apply fold_constants_bexp_sound.
    destruct (fold_constants_bexp b) eqn:Heqb;
      (* If the optimization doesn't eliminate the if, then the result
         is easy to prove from the IH and fold_constants_bexp_sound *)
      try (apply CIf_congruence; assumption).
    SCase "b always true".
      apply trans_cequiv with c1; try assumption.
      apply IFB_true; assumption.
    SCase "b always false".
      apply trans_cequiv with c2; try assumption.
      apply IFB_false; assumption.
  Case "WHILE".
    assert (bequiv b (fold_constants_bexp b)).
      apply fold_constants_bexp_sound.
    destruct (fold_constants_bexp b) eqn:Heqb; try (apply CWhile_congruence; assumption).
      apply WHILE_true. apply H.
      apply WHILE_false. apply H.
Qed.

(*-- Check --*)
Check fold_constants_com_sound : 
  ctrans_sound fold_constants_com.


(*Require Export Assignment08_15.*)

(* problem #16: 10 points *)

Lemma optimize_0plus_aexp_sound:
  atrans_sound optimize_0plus_aexp.
Proof.
  unfold atrans_sound. intros. unfold aequiv. intros. induction a; try reflexivity.
  - simpl. try (destruct a1; try destruct a2; try destruct n; try rewrite IHa1; try rewrite IHa2; try rewrite plus_0_r; try reflexivity).
    destruct n0. rewrite <- IHa2. simpl. rewrite plus_0_r. reflexivity. reflexivity.
  - simpl. try (destruct a1; try destruct a2; try rewrite IHa1; try rewrite IHa2; try reflexivity).
  - simpl. try (destruct a1; try destruct a2; try rewrite IHa1; try rewrite IHa2; try reflexivity).
Qed.

(*-- Check --*)
Check optimize_0plus_aexp_sound:
  atrans_sound optimize_0plus_aexp.


(*Require Export Assignment08_16.*)

(* problem #17: 10 points *)

Lemma optimize_0plus_bexp_sound:
  btrans_sound optimize_0plus_bexp.
Proof.
  unfold btrans_sound. intros. unfold bequiv. intros. induction b; simpl; try reflexivity.
  - rewrite <- optimize_0plus_aexp_sound. rewrite <- optimize_0plus_aexp_sound. reflexivity.
  - rewrite <- optimize_0plus_aexp_sound. rewrite <- optimize_0plus_aexp_sound. reflexivity.
  - rewrite <- IHb. reflexivity.
  - rewrite <- IHb1. rewrite IHb2. reflexivity.
Qed.

(*-- Check --*)
Check optimize_0plus_bexp_sound:
  btrans_sound optimize_0plus_bexp.


(*Require Export Assignment08_17.*)

(* problem #18: 10 points *)

Lemma optimize_0plus_com_sound:
  ctrans_sound optimize_0plus_com.
Proof.
  unfold ctrans_sound. intros. induction c; simpl.
  - apply refl_cequiv.
  - apply CAss_congruence. apply optimize_0plus_aexp_sound.
  - apply CSeq_congruence. assumption. assumption.
  - assert (bequiv b (optimize_0plus_bexp b)). apply optimize_0plus_bexp_sound. destruct b;
    simpl; apply CIf_congruence; assumption; assumption; assumption.
  - assert (bequiv b (optimize_0plus_bexp b)). apply optimize_0plus_bexp_sound. destruct b;
    simpl; apply CWhile_congruence; assumption; assumption. 
Qed.

(*-- Check --*)
Check optimize_0plus_com_sound:
  ctrans_sound optimize_0plus_com.


(*Require Export Assignment08_18.*)

(* problem #19: 10 points *)

Lemma constfold_0plus_sound:
  ctrans_sound constfold_0plus.
Proof.
  unfold ctrans_sound. intros. unfold constfold_0plus. assert (cequiv c (fold_constants_com c)). apply fold_constants_com_sound. assert (cequiv c (optimize_0plus_com c)). apply optimize_0plus_com_sound. apply trans_cequiv with (fold_constants_com c).
  - assumption.
  - remember (fold_constants_com c) as c'. apply optimize_0plus_com_sound. 
Qed.

(*-- Check --*)
Check constfold_0plus_sound:
  ctrans_sound constfold_0plus.
