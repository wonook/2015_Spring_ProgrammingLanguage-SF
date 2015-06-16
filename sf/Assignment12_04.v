Require Export Assignment12_03.

(* problem #04: 10 points *)

Corollary soundness : forall t t' T,
  empty |- t \in T -> 
  t ==>* t' ->
  ~(stuck t').
Proof.
    intros t t' T Hhas_type Hmulti. unfold stuck.
    intros [Hnf Hnot_val]. unfold normal_form in Hnf.
    induction Hmulti.
    - apply Hnot_val. destruct (progress x T). assumption. assumption. exfalso. apply Hnf. assumption.
    - apply IHHmulti. apply (preservation x y). assumption. assumption. assumption. assumption.
Qed.

(*-- Check --*)
Check soundness : forall t t' T,
  empty |- t \in T -> 
  t ==>* t' ->
  ~(stuck t').

