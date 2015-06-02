Require Export Assignment10_09.

(* problem #10: 10 points *)

(** The fact that small-step reduction implies big-step is now
    straightforward to prove, once it is stated correctly. 

    The proof proceeds by induction on the multi-step reduction
    sequence that is buried in the hypothesis [normal_form_of t t']. *)
(** Make sure you understand the statement before you start to
    work on the proof.  *)

(** **** Exercise: 3 stars (multistep__eval)  *)
Theorem strong_progress : forall t,
  value t \/ (exists t', t ==> t').
Proof.  
  tm_cases (induction t) Case.
    Case "C". left. apply v_const.
    Case "P". right. inversion IHt1.
      SCase "l". inversion IHt2.
        SSCase "l". inversion H. inversion H0.
          exists (C (n + n0)).
          apply ST_PlusConstConst.
        SSCase "r". inversion H0 as [t' H1].
          exists (P t1 t').
          apply ST_Plus2. apply H. apply H1.
      SCase "r". inversion H as [t' H0]. 
          exists (P t' t2).
          apply ST_Plus1. apply H0.  Qed.

Lemma nf_is_value : forall t,
  normal_form step t -> value t.
Proof. (* a corollary of [strong_progress]... *)
  unfold normal_form. intros t H.
  assert (G : value t \/ exists t', t ==> t').
    SCase "Proof of assertion". apply strong_progress.
  inversion G.
    SCase "l". apply H0.
    SCase "r". apply ex_falso_quodlibet. apply H. assumption.  Qed.

Theorem multistep__eval : forall t t',
  normal_form_of t t' -> exists n, t' = C n /\ t || n.
Proof.
  intros. unfold normal_form_of in H. inversion H. induction H0.
  - unfold step_normal_form in H1. apply nf_is_value in H1. inversion H1. exists n. split.
      reflexivity. constructor.
  - apply IHmulti in H1. destruct H1. destruct H1. exists x0. split. 
    assumption. apply step__eval with (t':=y). assumption. assumption. split. assumption. assumption.
Qed.

(*-- Check --*)
Check multistep__eval : forall t t',
  normal_form_of t t' -> exists n, t' = C n /\ t || n.

