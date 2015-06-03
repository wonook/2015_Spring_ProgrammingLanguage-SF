Require Export Assignment10_12.

(* problem #13: 10 points *)

(** **** Exercise: 3 stars, optional  *)
Lemma par_body_n : forall n st,
  st X = 0 /\ st Y = 0 ->
  exists st',
    par_loop / st ==>c*  par_loop / st' /\ st' X = n /\ st' Y = 0.
Proof.
    (* DIFFICULT!! *)
  intros. generalize dependent st. induction n; intros; unfold par_loop.
  - exists st. split.
    apply multi_refl. assumption.
  - apply IHn in H. inversion H.
    exists (update x X (S n)).
    inversion H0; subst. split.
    eapply multi_trans. apply H1.
    eapply par_body_n__Sn. assumption.
    split. 
      rewrite update_eq. reflexivity.
      rewrite update_neq. inversion H2. assumption.
      destruct (eq_id_dec X Y) eqn:eqn. inversion eqn. assumption.
Qed.

(*-- Check --*)
Check par_body_n : forall n st,
  st X = 0 /\ st Y = 0 ->
  exists st',
    par_loop / st ==>c*  par_loop / st' /\ st' X = n /\ st' Y = 0.

