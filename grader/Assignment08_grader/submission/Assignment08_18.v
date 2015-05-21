Require Export Assignment08_17.

(* problem #18: 10 points *)

Lemma optimize_0plus_com_sound:
  ctrans_sound optimize_0plus_com.
Proof.
  unfold ctrans_sound. intros. induction c; simpl.
  - apply refl_cequiv.
  - apply CAss_congruence. apply optimize_0plus_aexp_sound.
  - apply CSeq_congruence. assumption. assumption.
  - assert (bequiv b (optimize_0plus_bexp b)). apply optimize_0plus_bexp_sound. destruct b;
    simpl; apply CIf_congruence; assumption; assumption; assumption.
  - assert (bequiv b (optimize_0plus_bexp b)). apply optimize_0plus_bexp_sound. destruct b;
    simpl; apply CWhile_congruence; assumption; assumption. 
Qed.

(*-- Check --*)
Check optimize_0plus_com_sound:
  ctrans_sound optimize_0plus_com.

