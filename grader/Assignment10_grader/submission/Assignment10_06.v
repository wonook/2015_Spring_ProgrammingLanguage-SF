Require Export Assignment10_05.

(* problem #06: 10 points *)

Theorem normal_forms_unique:
  deterministic normal_form_of.
Proof.
  unfold deterministic. unfold normal_form_of.  intros x y1 y2 P1 P2.
  inversion P1 as [P11 P12]; clear P1. inversion P2 as [P21 P22]; clear P2. 
  generalize dependent y2. 
  (* We recommend using this initial setup as-is! *)
  induction P11.
  - intros. inversion P21; subst. 
    reflexivity.
    exfalso. apply P12. exists y. assumption.
  - intros. inversion P21; subst.
    exfalso. apply P22. exists y. assumption.
    apply IHP11. 
      assumption.
      assert (y = y0). eapply step_deterministic_alt. apply H. assumption. rewrite H2. assumption.
      assumption.
Qed.

(*-- Check --*)
Check normal_forms_unique:
  deterministic normal_form_of.

