Require Export Assignment09_10.

(* problem #11: 10 points *)

(** **** Exercise: 3 stars, advanced, optional (is_wp_formal)  *)
(** Prove formally using the definition of [hoare_triple] that [Y <= 4]
   is indeed the weakest precondition of [X ::= Y + 1] with respect to
   postcondition [X <= 5]. *)

Theorem is_wp_example :
  is_wp (fun st => st Y <= 4)
    (X ::= APlus (AId Y) (ANum 1)) (fun st => st X <= 5).
Proof.
  intros. unfold is_wp. split.
  - eapply hoare_consequence_pre. apply hoare_asgn.
    intros st H. unfold assn_sub, update; simpl. omega.
  - intros. intros st H'. unfold hoare_triple in H. 
      remember (update st X (st Y + 1)) as st'.
      assert ((X ::= APlus (AId Y) (ANum 1)) / st || st') as E. subst. apply E_Ass. reflexivity.
    apply H in E; try assumption. rewrite Heqst' in E. unfold update in E. 
    apply le_pred in E. simpl in E. rewrite plus_comm in E. simpl in E. assumption.
Qed.

(*-- Check --*)
Check is_wp_example :
  is_wp (fun st => st Y <= 4)
    (X ::= APlus (AId Y) (ANum 1)) (fun st => st X <= 5).

