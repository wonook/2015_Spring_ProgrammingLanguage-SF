Require Export Assignment10_10.

(* problem #11: 10 points *)

(** **** Exercise: 3 stars, optional (interp_tm)  *)
(** Remember that we also defined big-step evaluation of [tm]s as a
    function [evalF].  Prove that it is equivalent to the existing
    semantics.
 
    Hint: we just proved that [eval] and [multistep] are
    equivalent, so logically it doesn't matter which you choose.
    One will be easier than the other, though!  *)

Theorem evalF_eval : forall t n,
  evalF t = n <-> t || n.
Proof.
  intros. split. 
  - generalize dependent n. induction t; intros.
    + simpl in H. rewrite H. constructor.
    + simpl in H. inversion H; subst. constructor. apply IHt1. reflexivity. apply IHt2. reflexivity.
  - generalize dependent n. induction t; intros.
    + inversion H; subst. simpl. reflexivity.
    + inversion H; subst. simpl. rewrite (IHt1 n1). rewrite (IHt2 n2). reflexivity. assumption. assumption.
Qed.

(*-- Check --*)
Check evalF_eval : forall t n,
  evalF t = n <-> t || n.

