Require Export Assignment11_00.

(* problem #01: 10 points *)

(** **** Exercise: 2 stars (some_term_is_stuck)  *)
Example some_term_is_stuck :
  exists t, stuck t.
Proof.
  exists (tsucc ttrue). unfold stuck, value, normal_form, not. split; intros.
  - inversion H. inversion H0. inversion H2. 
  - inversion H. inversion H0. inversion H0. inversion H2. 
Qed.

(*-- Check --*)
Check some_term_is_stuck :
  exists t, stuck t.


(*Require Export Assignment11_01.*)

(* problem #02: 10 points *)

(** **** Exercise: 3 stars, advanced (value_is_nf)  *)
(** Hint: You will reach a point in this proof where you need to
    use an induction to reason about a term that is known to be a
    numeric value.  This induction can be performed either over the
    term itself or over the evidence that it is a numeric value.  The
    proof goes through in either case, but you will find that one way
    is quite a bit shorter than the other.  For the sake of the
    exercise, try to complete the proof both ways. *)

Lemma value_is_nf : forall t,
  value t -> step_normal_form t.
Proof.
  intros. induction H; intros.
  unfold normal_form, not; intros. inversion H0. inversion H; subst. inversion H1. inversion H1.
  induction H; unfold normal_form, not; intros. inversion H. inversion H0.
    unfold normal_form, not in IHnvalue. apply IHnvalue. inversion H0. inversion H1; subst. exists t1'. assumption.
Qed.

(*-- Check --*)
Check value_is_nf : forall t,
  value t -> step_normal_form t.


(*Require Export Assignment11_02.*)

(* problem #03: 10 points *)

(** **** Exercise: 3 stars, optional (step_deterministic)  *)
(** Using [value_is_nf], we can show that the [step] relation is
    also deterministic... *)

Theorem step_deterministic:
  deterministic step.
Proof with eauto.
  unfold deterministic. intros. generalize dependent y2. induction H; intros.
  - inversion H0; subst. reflexivity. inversion H4.
  - inversion H0; subst. reflexivity. inversion H4.
  - inversion H0; subst. inversion H; subst. inversion H; subst. apply IHstep in H5; subst. reflexivity.
  - inversion H0; subst. apply IHstep in H2; subst. reflexivity.
  - inversion H0; subst. reflexivity. inversion H1.
  - inversion H0; subst. reflexivity. inversion H2; subst. assert (value t1); eauto. 
    apply value_is_nf in H1. unfold normal_form, not in H1. exfalso. apply H1. exists t1'0. assumption.
  - inversion H0; subst.
    inversion H.
    inversion H; subst. assert (value y2); eauto. 
    apply value_is_nf in H1. unfold normal_form, not in H1. exfalso. apply H1. exists t1'0. assumption.
    apply IHstep in H2. subst; reflexivity.
  - inversion H0; subst. reflexivity. inversion H1.
  - inversion H0; subst. reflexivity. inversion H2; subst. assert (value t1); eauto.
    apply value_is_nf in H1. unfold normal_form, not in H1. exfalso. apply H1. exists t1'0. assumption.
  - inversion H0; subst.
    inversion H.
    inversion H; subst. assert (value t0); eauto.
    apply value_is_nf in H1. unfold normal_form, not in H1. exfalso. apply H1. exists t1'0. assumption.
    apply IHstep in H2. subst; reflexivity.
Qed.

(*-- Check --*)
Check step_deterministic:
  deterministic step.


(*Require Export Assignment11_03.*)

(* problem #04: 10 points *)

(** **** Exercise: 1 star, optional (succ_hastype_nat__hastype_nat)  *)
Example succ_hastype_nat__hastype_nat : forall t,
  |- tsucc t \in TNat ->
  |- t \in TNat.  
Proof.
  intros. inversion H; subst. assumption.
Qed.

(*-- Check --*)
Check succ_hastype_nat__hastype_nat : forall t,
  |- tsucc t \in TNat ->
  |- t \in TNat.  


(*Require Export Assignment11_04.*)

(* problem #05: 10 points *)

(** The typing relation enjoys two critical properties.  The first is
    that well-typed normal forms are values (i.e., not stuck). *)

(** **** Exercise: 3 stars (finish_progress)  *)
(** Complete the formal proof of the [progress] property.  (Make sure
    you understand the informal proof fragment in the following
    exercise before starting -- this will save you a lot of time.) *)

Theorem progress : forall t T,
  |- t \in T ->
  value t \/ exists t', t ==> t'.
Proof with auto.
  intros t T HT.
  has_type_cases (induction HT) Case...
  (* The cases that were obviously values, like T_True and
     T_False, were eliminated immediately by auto *)
  - Case "T_If".
    right. inversion IHHT1; clear IHHT1.
    SCase "t1 is a value".
    apply (bool_canonical t1 HT1) in H.
    inversion H; subst; clear H.
      exists t2...
      exists t3...
    SCase "t1 can take a step".
      inversion H as [t1' H1].
        exists (tif t1' t2 t3)...
  - Case "T_Succ".
    inversion IHHT; subst...
      inversion H... right. inversion H0; subst. inversion HT. inversion HT.
      inversion H. right. exists (tsucc x)...
  - Case "T_Pred".
    inversion IHHT; subst...
      inversion H... 
        right. inversion H0; subst. inversion HT. inversion HT.
        right. induction H0; subst. exists tzero... exists t...
      inversion H; subst. right. exists (tpred x)...
  - Case "T_Iszero".
    inversion IHHT; subst...
      inversion H...
        right. inversion H0; subst. inversion HT. inversion HT.
        right. inversion H0; subst. exists ttrue... exists tfalse...
      inversion H; subst. right. exists (tiszero x)...
Qed.

(*-- Check --*)
Check progress : forall t T,
  |- t \in T ->
  value t \/ exists t', t ==> t'.


(*Require Export Assignment11_05.*)

(* problem #06: 10 points *)

(** **** Exercise: 2 stars (finish_preservation)  *)
(** Complete the formal proof of the [preservation] property.  (Again,
    make sure you understand the informal proof fragment in the
    following exercise first.) *)

Theorem preservation : forall t t' T,
  |- t \in T ->
  t ==> t' ->
  |- t' \in T.
Proof with auto.
  intros t t' T HT HE.
  generalize dependent t'.
  has_type_cases (induction HT) Case; 
         (* every case needs to introduce a couple of things *)
         intros t' HE; 
         (* and we can deal with several impossible
            cases all at once *)
         try (solve by inversion).
  - Case "T_If". inversion HE; subst; clear HE.
    SCase "ST_IFTrue". assumption.
    SCase "ST_IfFalse". assumption.
    SCase "ST_If". apply T_If; try assumption.
      apply IHHT1; assumption.
  - Case "T_Succ".
    inversion HE; subst...
  - Case "T_Pred".  
    inversion HE; subst...
      inversion HT; subst. assumption.
  - Case "T_Iszero".
    inversion HE; subst...
Qed.

(*-- Check --*)
Check preservation : forall t t' T,
  |- t \in T ->
  t ==> t' ->
  |- t' \in T.


(*Require Export Assignment11_06.*)

(* problem #07: 10 points *)

(** **** Exercise: 1 star (normalize_ex)  *)
Theorem normalize_ex : exists e',
  (AMult (ANum 3) (AMult (ANum 2) (ANum 1))) / empty_state 
  ==>a* e'.
Proof.
  eapply ex_intro. normalize.
Qed.

(*-- Check --*)
Check normalize_ex : exists e',
  (AMult (ANum 3) (AMult (ANum 2) (ANum 1))) / empty_state 
  ==>a* e'.


(*Require Export Assignment11_07.*)

(* problem #08: 10 points *)

(** **** Exercise: 1 star, optional (normalize_ex')  *)
(** For comparison, prove it using [apply] instead of [eapply]. *)

Theorem normalize_ex' : exists e',
  (AMult (ANum 3) (AMult (ANum 2) (ANum 1))) / empty_state 
  ==>a* e'.
Proof.
  apply ex_intro with (ANum 6). normalize.
Qed.

(*-- Check --*)
Check normalize_ex' : exists e',
  (AMult (ANum 3) (AMult (ANum 2) (ANum 1))) / empty_state 
  ==>a* e'.


(*Require Export Assignment11_08.*)

(* problem #09: 10 points *)

(** **** Exercise: 2 stars (subject_expansion)  *)
(** Having seen the subject reduction property, it is reasonable to
    wonder whether the opposity property -- subject _expansion_ --
    also holds.  That is, is it always the case that, if [t ==> t']
    and [|- t' \in T], then [|- t \in T]?  If so, prove it.  If
    not, give a counter-example.  (You do not need to prove your
    counter-example in Coq, but feel free to do so if you like.)
*)

Theorem subject_expansion_false: 
  exists t t' T,
    t ==> t' /\
    |- t' \in T /\
    ~ |- t \in T.
Proof.
  exists (tif ttrue tfalse tzero). exists tfalse. eexists. split; eauto. split; eauto. unfold not. intros.
  inversion H; subst; eauto. inversion H6.
Qed.

(*-- Check --*)
Check subject_expansion_false: 
  exists t t' T,
    t ==> t' /\
    |- t' \in T /\
    ~ |- t \in T.


(*Require Export Assignment11_09.*)

(* problem #10: 30 points *)

(** Write a type checking function [tyeq: tm -> ty -> bool].
**)

Fixpoint tycheck (t: tm) (T: ty) : bool :=
  match t with
  | .

Example tycheck_ex1:
  tycheck
    (tif (tiszero (tpred (tsucc (tsucc tzero)))) ttrue (tiszero (tsucc tzero))) 
    TBool 
  = true.
Proof. reflexivity. Qed.

Example tycheck_ex2:
  tycheck
    (tif (tiszero (tpred (tsucc (tsucc tzero)))) tzero (tiszero (tsucc tzero))) 
    TBool 
  = false.
Proof. reflexivity. Qed.

(** Prove that the type checking function [tyeq: tm -> ty -> bool] is correct.

    Hint: use the lemma [andb_prop].
**)

Check andb_prop.

Theorem tycheck_correct1: forall t T
    (TYCHK: tycheck t T = true),
  |- t \in T.
Proof.
  exact FILL_IN_HERE.
Qed.

Theorem tycheck_correct2: forall t T
    (HASTY: |- t \in T),
  tycheck t T = true.
Proof.
  exact FILL_IN_HERE.
Qed.

(*-- Check --*)

Check (conj tycheck_ex1 tycheck_ex2 :
 (tycheck
    (tif (tiszero (tpred (tsucc (tsucc tzero)))) ttrue (tiszero (tsucc tzero))) 
    TBool 
  = true)
 /\
 (tycheck
    (tif (tiszero (tpred (tsucc (tsucc tzero)))) tzero (tiszero (tsucc tzero))) 
    TBool 
  = false)).

Check tycheck_correct1: forall t T
    (TYCHK: tycheck t T = true),
  |- t \in T.

Check tycheck_correct2: forall t T
    (HASTY: |- t \in T),
  tycheck t T = true.
