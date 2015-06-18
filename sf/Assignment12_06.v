Require Export Assignment12_05.

(* problem #06: 10 points *)

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

