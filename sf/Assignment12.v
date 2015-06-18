Require Export Assignment12_00.

(* problem #01: 10 points *)

(** **** Exercise: 3 stars, optional (typing_nonexample_3)  *)
(** Another nonexample:
    ~ (exists S, exists T,
          empty |- \x:S. x x : T).
*)

Example typing_nonexample_3 :
  ~ (exists S, exists T,
        empty |- 
          (tabs X S
             (tapp (tvar X) (tvar X))) \in
          T).
Proof.
  unfold not. intros. inversion H. inversion H0. 
  inversion H1; subst; clear H1.
  inversion H7; subst; clear H7.
  inversion H4; subst; clear H4.
  inversion H6; subst; clear H6.
  rewrite H3 in H4. inversion H4. 
  assert (forall T T', ~ (TArrow T T' = T)).
  - induction T; unfold not; intros; try solve by inversion.
    + inversion H1. eapply IHT1. apply H6.
  - eapply H1. apply H2.
Qed.

(*-- Check --*)
Check typing_nonexample_3 :
  ~ (exists S, exists T,
        empty |- 
          (tabs X S
             (tapp (tvar X) (tvar X))) \in
          T).


(*Require Export Assignment12_01.*)

(* problem #02: 10 points *)

(** **** Exercise: 2 stars, optional (typable_empty__closed)  *)
Corollary typable_empty__closed : forall t T, 
    empty |- t \in T  ->
    closed t.
Proof.
  intros. remember (@empty ty) as Gamma. unfold closed. unfold not. intros. 
  assert (exists T', Gamma x = Some T').
    - apply free_in_context with t T. assumption. assumption.
    - inversion H1. rewrite HeqGamma in H2. inversion H2.
Qed.

(*-- Check --*)
Check typable_empty__closed : forall t T, 
    empty |- t \in T  ->
    closed t.


(*Require Export Assignment12_02.*)

(* problem #03: 10 points *)

(** **** Exercise: 3 stars (types_unique)  *)
(** Another pleasant property of the STLC is that types are
    unique: a given term (in a given context) has at most one
    type. *)

Lemma type_is_unique: forall t G T T'
    (TYPED: G |- t \in T)
    (TYPED': G |- t \in T'),
  T = T'.
Proof.
  intros. generalize dependent T'. induction TYPED; intros; inversion TYPED'; subst; eauto.
  - rewrite H2 in H. inversion H. auto.
  - assert (T12 = T1). apply IHTYPED. assumption. 
    rewrite H. auto.
  - assert (TArrow T1 T2 = TArrow T0 T'). apply IHTYPED1. assumption.
    inversion H. auto.
  - assert (T1 = T0). apply IHTYPED1. assumption.
    assert (T2 = T3). apply IHTYPED2. assumption.
    subst. auto.
  - assert (TProd T1 T2 = TProd T' T3). apply IHTYPED. assumption.
    inversion H. auto.
  - assert (TProd T1 T2 = TProd T0 T'). apply IHTYPED. assumption.
    inversion H. auto.
  - apply IHTYPED2. assert (T1 = T0). apply IHTYPED1. assumption.
    rewrite H. auto.
  - assert (T1 = T0). apply IHTYPED. assumption.
    subst. auto.
  - assert (T2 = T3). apply IHTYPED. assumption.
    subst. auto.
  - assert (TSum T1 T2 = TSum T0 T3). apply IHTYPED1. assumption.
    inversion H.
    apply IHTYPED2. rewrite H1. assumption.
  - assert (TArrow (TArrow T1 T2) (TArrow T1 T2) = TArrow (TArrow T0 T3) (TArrow T0 T3)). apply IHTYPED. assumption. 
    inversion H. auto.
Qed.

(*-- Check --*)
Check type_is_unique: forall t G T T'
    (HTyped: G |- t \in T)
    (HTyped': G |- t \in T'),
  T = T'.


(*Require Export Assignment12_03.*)

(* problem #04: 10 points *)

Corollary soundness : forall t t' T,
  empty |- t \in T -> 
  t ==>* t' ->
  ~(stuck t').
Proof.
    intros t t' T Hhas_type Hmulti. unfold stuck.
    intros [Hnf Hnot_val]. unfold normal_form in Hnf.
    induction Hmulti.
    - apply Hnot_val. destruct (progress x T). assumption. assumption. exfalso. apply Hnf. assumption.
    - apply IHHmulti. apply (preservation x y). assumption. assumption. assumption. assumption.
Qed.

(*-- Check --*)
Check soundness : forall t t' T,
  empty |- t \in T -> 
  t ==>* t' ->
  ~(stuck t').


(*Require Export Assignment12_04.*)

(* problem #05: 20 points *)

(** Translate this informal recursive definition into one using [fix]:
<<
   halve = 
     \x:Nat. 
        if x=0 then 0 
        else if (pred x)=0 then 0
        else 1 + (halve (pred (pred x))))
>>
<<
  halve =
    fix
      (\f:nat->nat
        \x:nat.
          if0 x then 0
          else if0 (pred x) then 0
          else (succ (f (pred (pred x))))).
>>
*)

Definition halve : tm :=
    tfix
      (tabs Halve (TArrow TNat TNat)
        (tabs X TNat
          (tif0 (tvar X) (tnat 0)
            (tif0 (tpred (tvar X)) (tnat 0)
              (tsucc 
                (tapp (tvar Halve) (tpred (tpred (tvar X))))))))).

Example halve_type: empty |- halve \in TArrow TNat TNat.
Proof.
  (* unfold halve; eauto 10. *)
  unfold halve; eauto 10.
Qed.

Example halve_10: tapp halve (tnat 10) ==>* tnat 5.
Proof.
  (* unfold halve; normalize. *)
  unfold halve; normalize.
Qed.

Example halve_11: tapp halve (tnat 11) ==>* tnat 5.
Proof.
  (* unfold halve; normalize. *)
  unfold halve. normalize.
Qed.


Theorem halve_correct: forall n,
   tapp halve (tnat (n+n)) ==>* tnat n.
Proof.
  unfold halve. intros. induction n.
  - normalize.
  - eapply multi_step. 
      eapply ST_AppFix. apply v_abs. apply v_nat.
    eapply multi_step.
      eapply ST_App1. eapply ST_AppAbs. apply v_fix. apply v_abs.
    eapply multi_step. simpl.
      eapply ST_AppAbs. apply v_nat.
    eapply multi_step. simpl.
      eapply ST_If0Nonzero.
    eapply multi_step.
      eapply ST_If01. rewrite plus_comm. apply ST_PredNat.
    eapply multi_step. simpl.
      eapply ST_If0Nonzero. rewrite plus_comm. 
    eapply multi_step. simpl.
      eapply ST_Succ1. eapply ST_App2. apply v_fix. apply v_abs.
      eapply ST_Pred. eapply ST_PredNat.
    eapply multi_step. simpl.
      eapply ST_Succ1. eapply ST_App2. apply v_fix. apply v_abs.
      eapply ST_PredNat. simpl.
    assert (forall A, A ==>* tnat n -> tsucc A ==>* tnat (S n)).
      intros. eapply multi_trans.
      assert (forall t t', t ==>* t' -> tsucc t ==>* tsucc t').
        intros; induction H0; eauto.
      apply H0. apply H. eauto.
    apply H. apply IHn.
Qed.

(*-- Check --*)

Check conj halve_type (conj halve_10 halve_11) :
  empty |- halve \in TArrow TNat TNat /\
  tapp halve (tnat 10) ==>* tnat 5 /\ 
  tapp halve (tnat 11) ==>* tnat 5.

Check halve_correct: forall n,
   tapp halve (tnat (n + n)) ==>* tnat n.


(*Require Export Assignment12_05.*)

(* problem #06: 10 points *)

(*Reserved Notation "t1 '==>n' n t2" (at level 40).

Inductive multi_n : tm -> nat -> tm -> Prop :=
| multi_0 : forall t, multi_n t 0 t
| multi_nxt : forall m t t1 t2, t ==> t1 -> multi_n t1 m t2 -> multi_n t (S m) t2

where "t1 '==>n' n t2" := (multi_n t1 n t2).

Notation "t1 '==>n' n t2" := (multi_n t1 n t2) (at level 40).

Hint Constructors multi_n.*)

Lemma deter:
  forall t t1 t2, t ==> t1 -> t ==> t2 -> t1 = t2.
Proof.
    intros. generalize dependent t2. admit.
Qed.

Lemma lalala:
    forall t q1 q2 q3, q1 ==>* t -> q1 ==> q2 -> q2 ==> q3 -> q3 ==> q1 -> 
                    (t = q1 \/ t = q2 \/ t = q3).
Proof.
    intros. inversion H. auto. inversion H4. right. left. eapply deter. rewrite <- H8. apply H3. apply H0. admit.
Qed.

Theorem tloop_diverges:
  ~ exists t, tapp tloop (tnat 0) ==>* t /\ normal_form step t.
Proof.
  unfold tloop, not, normal_form. intros.
    inversion H; subst; clear H.
    inversion H0; subst; clear H0.
    apply H1.
    remember (tapp (tfix (tabs Loop (TArrow TNat TNat) (tabs X TNat (tapp (tvar Loop) (tvar X))))) (tnat 0)).
    remember (tapp (tapp (tabs Loop (TArrow TNat TNat) (tabs X TNat (tapp (tvar Loop) (tvar X)))) (tfix (tabs Loop (TArrow TNat TNat) (tabs X TNat (tapp (tvar Loop) (tvar X)))))) (tnat 0)).
    remember (tapp (tabs X TNat (tapp (tfix (tabs Loop (TArrow TNat TNat) (tabs X TNat (tapp (tvar Loop) (tvar X))))) (tvar X))) (tnat 0)).
    assert (t0 ==> t1).
      subst. apply ST_App1. apply ST_AppAbs. apply v_fix. apply v_abs.
    assert (t ==> t0).
      subst. apply ST_AppFix. apply v_abs. apply v_nat.
    assert (t1 ==> t).
      subst. apply ST_AppAbs. apply v_nat.
    assert (x = t \/ x = t0 \/ x = t1).
      inversion H; eauto.
      apply lalala; eauto.
    inversion H4. rewrite H5. eauto. inversion H5. rewrite H6. eauto. rewrite H6. eauto.
Qed.

(*-- Check --*)
Check tloop_diverges:
  ~ exists t, tapp tloop (tnat 0) ==>* t /\ normal_form step t.

