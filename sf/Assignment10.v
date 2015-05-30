Require Export Assignment10_00.

(* problem #01: 10 points *)

(** **** Exercise: 1 star (test_step_2)  *)
(** Right-hand sides of sums can take a step only when the
    left-hand side is finished: if [t2] can take a step to [t2'],
    then [P (C n) t2] steps to [P (C n)
    t2']: *)

Example test_step_2 : 
      P 
        (C 0)
        (P 
          (C 2) 
          (P (C 0) (C 3)))
      ==>
      P 
        (C 0)
        (P 
          (C 2) 
          (C (0 + 3))).
Proof. 
  exact FILL_IN_HERE.
Qed.

(*-- Check --*)
Check test_step_2 : 
      P 
        (C 0)
        (P 
          (C 2) 
          (P (C 0) (C 3)))
      ==>
      P 
        (C 0)
        (P 
          (C 2) 
          (C (0 + 3))).


(*Require Export Assignment10_01.*)

(* problem #02: 10 points *)

(** As a sanity check on this change, let's re-verify determinism 

    Proof sketch: We must show that if [x] steps to both [y1] and [y2]
    then [y1] and [y2] are equal.  Consider the final rules used in
    the derivations of [step x y1] and [step x y2].

    - If both are [ST_PlusConstConst], the result is immediate.

    - It cannot happen that one is [ST_PlusConstConst] and the other
      is [ST_Plus1] or [ST_Plus2], since this would imply that [x] has
      the form [P t1 t2] where both [t1] and [t2] are
      constants (by [ST_PlusConstConst]) AND one of [t1] or [t2] has
      the form [P ...].

    - Similarly, it cannot happen that one is [ST_Plus1] and the other
      is [ST_Plus2], since this would imply that [x] has the form
      [P t1 t2] where [t1] both has the form [P t1 t2] and
      is a value (hence has the form [C n]).

    - The cases when both derivations end with [ST_Plus1] or
      [ST_Plus2] follow by the induction hypothesis. [] *)

(** Most of this proof is the same as the one above.  But to get
    maximum benefit from the exercise you should try to write it from
    scratch and just use the earlier one if you get stuck. *)

Theorem step_deterministic_alt: deterministic step.
Proof.
  exact FILL_IN_HERE.
Qed.

(*-- Check --*)
Check step_deterministic_alt: deterministic step.


(*Require Export Assignment10_02.*)

(* problem #03: 10 points *)

(** **** Exercise: 1 star, optional (test_multistep_2)  *)
Lemma test_multistep_2:
  C 3 ==>* C 3.
Proof.
  exact FILL_IN_HERE.
Qed.

(*-- Check --*)
Check test_multistep_2:
  C 3 ==>* C 3.


(*Require Export Assignment10_03.*)

(* problem #04: 10 points *)

(** **** Exercise: 1 star, optional (test_multistep_3)  *)
Lemma test_multistep_3:
      P (C 0) (C 3)
   ==>*
      P (C 0) (C 3).
Proof.
  exact FILL_IN_HERE.
Qed.

(*-- Check --*)
Check test_multistep_3:
      P (C 0) (C 3)
   ==>*
      P (C 0) (C 3).


(*Require Export Assignment10_04.*)

(* problem #05: 10 points *)

(** **** Exercise: 2 stars (test_multistep_4)  *)
Lemma test_multistep_4:
      P
        (C 0)
        (P
          (C 2)
          (P (C 0) (C 3)))
  ==>*
      P
        (C 0)
        (C (2 + (0 + 3))).
Proof.
  exact FILL_IN_HERE.
Qed.

(*-- Check --*)
Check test_multistep_4:
      P
        (C 0)
        (P
          (C 2)
          (P (C 0) (C 3)))
  ==>*
      P
        (C 0)
        (C (2 + (0 + 3))).


(*Require Export Assignment10_05.*)

(* problem #06: 10 points *)

Theorem normal_forms_unique:
  deterministic normal_form_of.
Proof.
  unfold deterministic. unfold normal_form_of.  intros x y1 y2 P1 P2.
  inversion P1 as [P11 P12]; clear P1. inversion P2 as [P21 P22]; clear P2. 
  generalize dependent y2. 
  (* We recommend using this initial setup as-is! *)
  exact FILL_IN_HERE.
Qed.

(*-- Check --*)
Check normal_forms_unique:
  deterministic normal_form_of.


(*Require Export Assignment10_06.*)

(* problem #07: 10 points *)

(** **** Exercise: 2 stars (multistep_congr_2)  *)
Lemma multistep_congr_2 : forall t1 t2 t2',
     value t1 ->
     t2 ==>* t2' ->
     P t1 t2 ==>* P t1 t2'.
Proof.
  exact FILL_IN_HERE.
Qed.

(*-- Check --*)
Check multistep_congr_2 : forall t1 t2 t2',
     value t1 ->
     t2 ==>* t2' ->
     P t1 t2 ==>* P t1 t2'.


(*Require Export Assignment10_07.*)

(* problem #08: 10 points *)

(** **** Exercise: 3 stars (eval__multistep)  *)
(** The key idea behind the proof comes from the following picture:
       P t1 t2 ==>            (by ST_Plus1) 
       P t1' t2 ==>           (by ST_Plus1)  
       P t1'' t2 ==>          (by ST_Plus1) 
       ...                
       P (C n1) t2 ==>        (by ST_Plus2)
       P (C n1) t2' ==>       (by ST_Plus2)
       P (C n1) t2'' ==>      (by ST_Plus2)
       ...                
       P (C n1) (C n2) ==>    (by ST_PlusConstConst)
       C (n1 + n2)              
    That is, the multistep reduction of a term of the form [P t1 t2]
    proceeds in three phases:
       - First, we use [ST_Plus1] some number of times to reduce [t1]
         to a normal form, which must (by [nf_same_as_value]) be a
         term of the form [C n1] for some [n1].
       - Next, we use [ST_Plus2] some number of times to reduce [t2]
         to a normal form, which must again be a term of the form [C
         n2] for some [n2].
       - Finally, we use [ST_PlusConstConst] one time to reduce [P (C
         n1) (C n2)] to [C (n1 + n2)]. *)

(** To formalize this intuition, you'll need to use the congruence
    lemmas from above (you might want to review them now, so that
    you'll be able to recognize when they are useful), plus some basic
    properties of [==>*]: that it is reflexive, transitive, and
    includes [==>]. *)

Theorem eval__multistep : forall t n,
  t || n -> t ==>* C n.
Proof.
  exact FILL_IN_HERE.
Qed.

(*-- Check --*)
Check eval__multistep : forall t n,
  t || n -> t ==>* C n.


(*Require Export Assignment10_08.*)

(* problem #09: 10 points *)

(** **** Exercise: 3 stars (step__eval)  *)
Lemma step__eval : forall t t' n,
     t ==> t' ->
     t' || n ->
     t || n.
Proof.
  intros t t' n Hs. generalize dependent n.
  exact FILL_IN_HERE.
Qed.

(*-- Check --*)
Check step__eval : forall t t' n,
     t ==> t' ->
     t' || n ->
     t || n.


(*Require Export Assignment10_09.*)

(* problem #10: 10 points *)

(** The fact that small-step reduction implies big-step is now
    straightforward to prove, once it is stated correctly. 

    The proof proceeds by induction on the multi-step reduction
    sequence that is buried in the hypothesis [normal_form_of t t']. *)
(** Make sure you understand the statement before you start to
    work on the proof.  *)

(** **** Exercise: 3 stars (multistep__eval)  *)
Theorem multistep__eval : forall t t',
  normal_form_of t t' -> exists n, t' = C n /\ t || n.
Proof.
  exact FILL_IN_HERE.
Qed.

(*-- Check --*)
Check multistep__eval : forall t t',
  normal_form_of t t' -> exists n, t' = C n /\ t || n.


(*Require Export Assignment10_10.*)

(* problem #11: 10 points *)

(** **** Exercise: 3 stars, optional (interp_tm)  *)
(** Remember that we also defined big-step evaluation of [tm]s as a
    function [evalF].  Prove that it is equivalent to the existing
    semantics.
 
    Hint: we just proved that [eval] and [multistep] are
    equivalent, so logically it doesn't matter which you choose.
    One will be easier than the other, though!  *)

Theorem evalF_eval : forall t n,
  evalF t = n <-> t || n.
Proof.
  exact FILL_IN_HERE.
Qed.

(*-- Check --*)
Check evalF_eval : forall t n,
  evalF t = n <-> t || n.


(*Require Export Assignment10_11.*)

(* problem #12: 10 points *)

(** **** Exercise: 3 stars, optional  *)
Lemma par_body_n__Sn : forall n st,
  st X = n /\ st Y = 0 ->
  par_loop / st ==>c* par_loop / (update st X (S n)).
Proof.
  exact FILL_IN_HERE.
Qed.

(*-- Check --*)
Check par_body_n__Sn : forall n st,
  st X = n /\ st Y = 0 ->
  par_loop / st ==>c* par_loop / (update st X (S n)).


(*Require Export Assignment10_12.*)

(* problem #13: 10 points *)

(** **** Exercise: 3 stars, optional  *)
Lemma par_body_n : forall n st,
  st X = 0 /\ st Y = 0 ->
  exists st',
    par_loop / st ==>c*  par_loop / st' /\ st' X = n /\ st' Y = 0.
Proof.
  exact FILL_IN_HERE.
Qed.

(*-- Check --*)
Check par_body_n : forall n st,
  st X = 0 /\ st Y = 0 ->
  exists st',
    par_loop / st ==>c*  par_loop / st' /\ st' X = n /\ st' Y = 0.


(*Require Export Assignment10_13.*)

(* problem #14: 10 points *)

(* Hint: 

   First study the chapter "Auto.v".

   Using [;], [try] and [eauto], you can prove it in 4 lines thanks to: 
     Hint Constructors aval
     Hint Constructors astep.
  
   You can use the following intro pattern:
     destruct ... as [[? ?] | [? ?]].
*)

Theorem aexp_strong_progress: forall st a,
  (exists n, a = ANum n) \/
  exists a', a / st ==>a a'.
Proof.
  exact FILL_IN_HERE.
Qed.

(*-- Check --*)
Check aexp_strong_progress: forall st a,
  (exists n, a = ANum n) \/
  exists a', a / st ==>a a'.


(*Require Export Assignment10_14.*)

(* problem #15: 10 points *)

(* Hint: 

   First study the chapter "Auto.v".

   Using [;], [try] and [eauto], you can prove it in 7 lines thanks to:. 
     Hint Constructors bstep.

   You can use the following intro pattern:
     destruct ... as [[? | ?] | [? ?]].
*)

Theorem bexp_strong_progress: forall st b,
  (b = BTrue \/ b = BFalse) \/
  exists b', b / st ==>b b'.
Proof.
  exact FILL_IN_HERE.
Qed.

(*-- Check --*)
Check bexp_strong_progress: forall st b,
  (b = BTrue \/ b = BFalse) \/
  exists b', b / st ==>b b'.


(*Require Export Assignment10_15.*)

(* problem #16: 10 points *)

(* Hint: 

   First study the chapter "Auto.v".

   Using [;], [try] and [eauto], you can prove it in 6 lines thanks to:
     Hint Constructors cstep.
 
   You can use the following intro pattern:
     destruct ... as [ | [? [? ?]]].
*)

Theorem cimp_strong_progress : forall c st,
  c = SKIP \/ 
  exists c' st', c / st ==>c c' / st'.
Proof.
  exact FILL_IN_HERE.
Qed.

(*-- Check --*)
Check cimp_strong_progress : forall c st,
  c = SKIP \/ 
  exists c' st', c / st ==>c c' / st'.

