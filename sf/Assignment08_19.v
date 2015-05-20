Require Export Assignment08_18.

(* problem #19: 10 points *)

Lemma constfold_0plus_sound:
  ctrans_sound constfold_0plus.
Proof.
  unfold ctrans_sound. intros. unfold constfold_0plus. assert (cequiv c (fold_constants_com c)). apply fold_constants_com_sound. assert (cequiv c (optimize_0plus_com c)). apply optimize_0plus_com_sound. apply trans_cequiv with (fold_constants_com c).
  - assumption.
  - remember (fold_constants_com c) as c'. apply optimize_0plus_com_sound. 
Qed.

(*-- Check --*)
Check constfold_0plus_sound:
  ctrans_sound constfold_0plus.
