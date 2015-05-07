Require Export mid_05.

(* problem #06: 10 points *)

(** Medium:
    Prove the following theorem.
 **)

Lemma odd_or_even: forall n,
  exists k, n = 2*k \/ n = 1 + 2*k.
Proof.
  induction n.
  - exists 0. auto.
  - destruct IHn as [k [IHn | IHn]]; subst.
  	+ exists k; auto.
  	+ exists (1+k).
  	  left; simpl.
  	  rewrite plus_0_r, (plus_comm k (S k)).
Qed.

