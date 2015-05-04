Require Export Assignment07_02.

(* problem #03: 20 points *)

(** **** Exercise: 3 stars  (bevalR)  *)
(** Write a relation [bevalR] in the same style as
    [aevalR], and prove that it is equivalent to [beval].*)


Inductive bevalR: bexp -> bool -> Prop :=
  | E_BTrue : BTrue || true
  | E_BFalse : BFalse || false
  | E_BEq : forall (e1 e2: aexp) (n1 n2 : nat),
      aevalR e1 n1 -> aevalR e2 n2 -> (BEq e1 e2) || (beq_nat n1 n2)
  | E_BLe : forall (e1 e2: aexp) (n1 n2 : nat),
      aevalR e1 n1 -> aevalR e2 n2 -> (BLe e1 e2) || (ble_nat n1 n2)
  | E_BNot : forall (e1: bexp) (b1 : bool),
      (e1 || b1) -> (BNot e1) || (negb b1)
  | E_BAnd : forall (e1 e2: bexp) (b1 b2 : bool),
      (e1 || b1) -> (e2 || b2) -> (BAnd e1 e2) || (andb b1 b2)
  where "e '||' b" := (bevalR e b) : type_scope.

Theorem beval_iff_bevalR : forall b bv,
  bevalR b bv <-> beval b = bv.
Proof.
  split.
    intros.
    induction H;
      try(simpl; reflexivity);
      try(simpl; apply aeval_iff_aevalR in H; apply aeval_iff_aevalR in H0; rewrite H; rewrite H0; try(reflexivity));
      try(simpl; subst; reflexivity).
    generalize dependent bv.
    induction b; simpl; intros; 
      try(rewrite <- H; subst; constructor);
      try(apply aeval_iff_aevalR; reflexivity);
      try(apply IHb; reflexivity);
      try(apply IHb1; reflexivity);
      try(apply IHb2; reflexivity).
Qed.

(** [] *)

