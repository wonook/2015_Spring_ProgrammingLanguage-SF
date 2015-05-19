git diffvfRequire Export Assignment08_03.

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

