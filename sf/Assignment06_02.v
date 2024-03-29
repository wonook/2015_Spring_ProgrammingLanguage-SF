Require Export Assignment06_01.

(* problem #02: 10 points *)

(** **** Exercise: 3 stars, optional (not_exists_dist)  *)
(** (The other direction of this theorem requires the classical "law
    of the excluded middle".) *)

Theorem not_exists_dist :
  excluded_middle ->
  forall (X:Type) (P : X -> Prop),
    ~ (exists x, ~ P x) -> (forall x, P x).
Proof.
    intros. unfold not in H0. unfold excluded_middle in H. unfold not in H.
    destruct H with (P:=(P x)). 
    - apply H1. 
    (* Careful! *)
    - apply ex_falso_quodlibet. apply H0. apply ex_intro with (witness:=x). apply H1.
Qed.
(** [] *)

