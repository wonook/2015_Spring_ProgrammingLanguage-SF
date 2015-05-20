Require Export Assignment08_09.

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

