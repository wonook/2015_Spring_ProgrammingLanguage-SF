Require Export Assignment11_02.

(* problem #03: 10 points *)

(** **** Exercise: 3 stars, optional (step_deterministic)  *)
(** Using [value_is_nf], we can show that the [step] relation is
    also deterministic... *)

Theorem step_deterministic:
  deterministic step.
Proof with eauto.
  unfold deterministic. intros. generalize dependent y2. induction H; intros.
  - inversion H0; subst. reflexivity. inversion H4.
  - inversion H0; subst. reflexivity. inversion H4.
  - inversion H0; subst. inversion H; subst. inversion H; subst. apply IHstep in H5; subst. reflexivity.
  - inversion H0; subst. apply IHstep in H2; subst. reflexivity.
  - inversion H0; subst. reflexivity. inversion H1.
  - inversion H0; subst. reflexivity. inversion H2; subst. assert (value t1); eauto. 
    apply value_is_nf in H1. unfold normal_form, not in H1. exfalso. apply H1. exists t1'0. assumption.
  - inversion H0; subst.
    inversion H.
    inversion H; subst. assert (value y2); eauto. 
    apply value_is_nf in H1. unfold normal_form, not in H1. exfalso. apply H1. exists t1'0. assumption.
    apply IHstep in H2. subst; reflexivity.
  - inversion H0; subst. reflexivity. inversion H1.
  - inversion H0; subst. reflexivity. inversion H2; subst. assert (value t1); eauto.
    apply value_is_nf in H1. unfold normal_form, not in H1. exfalso. apply H1. exists t1'0. assumption.
  - inversion H0; subst.
    inversion H.
    inversion H; subst. assert (value t0); eauto.
    apply value_is_nf in H1. unfold normal_form, not in H1. exfalso. apply H1. exists t1'0. assumption.
    apply IHstep in H2. subst; reflexivity.
Qed.

(*-- Check --*)
Check step_deterministic:
  deterministic step.

