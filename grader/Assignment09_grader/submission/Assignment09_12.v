Require Export Assignment09_11.

(* problem #12: 10 points *)

(** **** Exercise: 2 stars, advanced (hoare_asgn_weakest)  *)
(** Show that the precondition in the rule [hoare_asgn] is in fact the
    weakest precondition. *)

Theorem hoare_asgn_weakest : forall Q X a,
  is_wp (Q [X |-> a]) (X ::= a) Q.
Proof.
  intros. unfold is_wp. split.
  - eapply hoare_consequence_pre. apply hoare_asgn. intros st H. assumption.
  - intros. intros st H'. unfold hoare_triple in H. unfold assn_sub, update.
    apply H with (st' := update st X (aeval st a)) in H'.
      assumption.
      constructor. reflexivity.
Qed.

(*-- Check --*)
Check hoare_asgn_weakest : forall Q X a,
  is_wp (Q [X |-> a]) (X ::= a) Q.
