Require Export mid_04.

(* problem #05: 10 points *)

(** Medium:
    Prove the following theorem.
 **)

Lemma app_tail_cancel: forall X (l1 l2: list X) a
    (EQ: l1 ++ [a] = l2 ++ [a]),
  l1 = l2.
Proof.
  (* FILL IN HERE *) admit.
Qed.

