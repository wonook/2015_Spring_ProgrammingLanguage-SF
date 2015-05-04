Require Export Assignment07_00.

(* problem #01: 20 points *)


(** **** Exercise: 3 stars (optimize_0plus_b)  *)
(** Since the [optimize_0plus] tranformation doesn't change the value
    of [aexp]s, we should be able to apply it to all the [aexp]s that
    appear in a [bexp] without changing the [bexp]'s value.  Write a
    function which performs that transformation on [bexp]s, and prove
    it is sound.  Use the tacticals we've just seen to make the proof
    as elegant as possible. *)

Fixpoint optimize_0plus_b (b : bexp) : bexp :=
  match b with
  | BTrue => BTrue
  | BFalse => BFalse
  | BEq a1 a2 => BEq (optimize_0plus a1) (optimize_0plus a2)
  | BLe a1 a2 => BLe (optimize_0plus a1) (optimize_0plus a2)
  | BNot b1 => BNot (optimize_0plus_b b1)
  | BAnd b1 b2 => BAnd (optimize_0plus_b b1) (optimize_0plus_b b2)
  end.

Lemma optimize_0_plus_sound : forall a,
  aeval (optimize_0plus a) = aeval a.
Proof.
  intros.
  induction a;
    try (simpl; reflexivity);
    try (simpl; simpl in IHa1; simpl in IHa2; rewrite IHa1; rewrite IHa2; reflexivity).
    destruct a1; try (simpl; simpl in IHa1; simpl in IHa2; rewrite IHa1; rewrite IHa2; reflexivity).
      destruct n; try (simpl; simpl in IHa2; rewrite IHa2; reflexivity).
Qed.
Theorem optimize_0plus_b_sound : forall b,
  beval (optimize_0plus_b b) = beval b.
Proof.
  intros.
  induction b;
    try (simpl; reflexivity);
    try (simpl; repeat (rewrite optimize_0_plus_sound); reflexivity);
    try (simpl; simpl in IHb; rewrite IHb; reflexivity).
    simpl; try(rewrite IHb1); try (rewrite IHb2); try(reflexivity).
Qed.
(** [] *)

