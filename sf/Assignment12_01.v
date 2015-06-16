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

