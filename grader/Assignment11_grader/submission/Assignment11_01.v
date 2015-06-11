Require Export Assignment11_00.

(* problem #01: 10 points *)

(** **** Exercise: 2 stars (some_term_is_stuck)  *)
Example some_term_is_stuck :
  exists t, stuck t.
Proof.
  exists (tsucc ttrue). unfold stuck, value, normal_form, not. split; intros.
  - inversion H. inversion H0. inversion H2. 
  - inversion H. inversion H0. inversion H0. inversion H2. 
Qed.

(*-- Check --*)
Check some_term_is_stuck :
  exists t, stuck t.

