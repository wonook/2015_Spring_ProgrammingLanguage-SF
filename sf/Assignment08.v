Require Export Assignment08_00.

(* problem #01: 10 points *)

(** **** Exercise: 2 stars (ceval_example2)  *)
Example ceval_example2:
    (X ::= ANum 0;; Y ::= ANum 1;; Z ::= ANum 2) / empty_state ||
    (update (update (update empty_state X 0) Y 1) Z 2).
Proof.
  exact FILL_IN_HERE.
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
  FILL_IN_HERE.

Example pup_to_2_ceval :
  pup_to_n / (update empty_state X 2) ||
    update (update (update (update (update (update empty_state
      X 2) Y 0) Y 2) X 1) Y 3) X 0.
Proof.
  exact FILL_IN_HERE.
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
  exact FILL_IN_HERE.
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
  exact FILL_IN_HERE.
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
  FILL_IN_HERE.

(** After you've defined [s_compile], prove the following to test
    that it works. *)

Example s_compile1 :
    s_compile (AMinus (AId X) (AMult (ANum 2) (AId Y)))
  = [SLoad X; SPush 2; SLoad Y; SMult; SMinus].
Proof.
  exact FILL_IN_HERE.
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

Theorem s_compile_correct : forall (st : state) (e : aexp),
  s_execute st [] (s_compile e) = [ aeval st e ].
Proof.
  exact FILL_IN_HERE.
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
  exact FILL_IN_HERE.
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
  exact FILL_IN_HERE.
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
  exact FILL_IN_HERE.
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

Theorem WHILE_true: forall b c,
     bequiv b BTrue  ->
     cequiv 
       (WHILE b DO c END)
       (WHILE BTrue DO SKIP END).
Proof. 
  exact FILL_IN_HERE.
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
  exact FILL_IN_HERE.
Qed.

(*-- Check --*)
Check seq_assoc : forall c1 c2 c3,
  cequiv ((c1;;c2);;c3) (c1;;(c2;;c3)).


(*Require Export Assignment08_10.*)

(* problem #11: 10 points *)

(** **** Exercise: 2 stars (assign_aequiv)  *)
Theorem assign_aequiv : forall X e,
  aequiv (AId X) e -> 
  cequiv SKIP (X ::= e).
Proof.
  exact FILL_IN_HERE.
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
  exact FILL_IN_HERE.
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
  exact FILL_IN_HERE.
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
    exact FILL_IN_HERE.
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
    exact FILL_IN_HERE.
Qed.

(*-- Check --*)
Check fold_constants_com_sound : 
  ctrans_sound fold_constants_com.


(*Require Export Assignment08_15.*)

(* problem #16: 10 points *)

Lemma optimize_0plus_aexp_sound:
  atrans_sound optimize_0plus_aexp.
Proof.
  exact FILL_IN_HERE.
Qed.

(*-- Check --*)
Check optimize_0plus_aexp_sound:
  atrans_sound optimize_0plus_aexp.


(*Require Export Assignment08_16.*)

(* problem #17: 10 points *)

Lemma optimize_0plus_bexp_sound:
  btrans_sound optimize_0plus_bexp.
Proof.
  exact FILL_IN_HERE.
Qed.

(*-- Check --*)
Check optimize_0plus_bexp_sound:
  btrans_sound optimize_0plus_bexp.


(*Require Export Assignment08_17.*)

(* problem #18: 10 points *)

Lemma optimize_0plus_com_sound:
  ctrans_sound optimize_0plus_com.
Proof.
  exact FILL_IN_HERE.
Qed.

(*-- Check --*)
Check optimize_0plus_com_sound:
  ctrans_sound optimize_0plus_com.


(*Require Export Assignment08_18.*)

(* problem #19: 10 points *)

Lemma constfold_0plus_sound:
  ctrans_sound constfold_0plus.
Proof.
  exact FILL_IN_HERE.
Qed.

(*-- Check --*)
Check constfold_0plus_sound:
  ctrans_sound constfold_0plus.
