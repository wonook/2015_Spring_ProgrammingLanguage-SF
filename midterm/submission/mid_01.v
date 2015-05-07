Require Export mid_00.

(* problem #01: 10 points *)

(** Easy:
    Prove the following theorem.
 **)

Lemma forall_not_ex_not: forall (X: Type) (P: X -> Prop)
    (ALL: forall x, P x),
  ~ exists x, ~ P x.
Proof.
  admit.
Qed.

