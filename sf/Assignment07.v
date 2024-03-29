
Require Export SfLib.

(* Important: 
   - You are NOT allowed to use the [admit] tactic
     because [admit] simply admits any goal 
     regardless of whether it is provable or not.

     But, you can leave [admit] for problems that you cannot prove.
     Then you will get zero points for those problems.

   - You are ALLOWED to use any tactics including.

     [tauto], [intuition], [firstorder], [omega].

   - Do NOT add any additional `Require Import/Export`.
*)

Inductive aexp : Type :=
  | ANum : nat -> aexp
  | APlus : aexp -> aexp -> aexp
  | AMinus : aexp -> aexp -> aexp
  | AMult : aexp -> aexp -> aexp.

Inductive bexp : Type :=
  | BTrue : bexp
  | BFalse : bexp
  | BEq : aexp -> aexp -> bexp
  | BLe : aexp -> aexp -> bexp
  | BNot : bexp -> bexp
  | BAnd : bexp -> bexp -> bexp.

Fixpoint aeval (a : aexp) : nat :=
  match a with
  | ANum n => n
  | APlus a1 a2 => (aeval a1) + (aeval a2)
  | AMinus a1 a2  => (aeval a1) - (aeval a2)
  | AMult a1 a2 => (aeval a1) * (aeval a2)
  end.

Fixpoint beval (b : bexp) : bool :=
  match b with
  | BTrue       => true
  | BFalse      => false
  | BEq a1 a2   => beq_nat (aeval a1) (aeval a2)
  | BLe a1 a2   => ble_nat (aeval a1) (aeval a2)
  | BNot b1     => negb (beval b1)
  | BAnd b1 b2  => andb (beval b1) (beval b2)
  end.

Fixpoint optimize_0plus (a:aexp) : aexp :=
  match a with
  | ANum n =>
      ANum n
  | APlus (ANum 0) e2 =>
      optimize_0plus e2
  | APlus e1 e2 =>
      APlus (optimize_0plus e1) (optimize_0plus e2)
  | AMinus e1 e2 =>
      AMinus (optimize_0plus e1) (optimize_0plus e2)
  | AMult e1 e2 =>
      AMult (optimize_0plus e1) (optimize_0plus e2)
  end.

Reserved Notation "e '||' n" (at level 50, left associativity).

Inductive aevalR : aexp -> nat -> Prop :=
  | E_ANum : forall (n:nat),
      (ANum n) || n
  | E_APlus : forall (e1 e2: aexp) (n1 n2 : nat),
      (e1 || n1) -> (e2 || n2) -> (APlus e1 e2) || (n1 + n2)
  | E_AMinus : forall (e1 e2: aexp) (n1 n2 : nat),
      (e1 || n1) -> (e2 || n2) -> (AMinus e1 e2) || (n1 - n2)
  | E_AMult :  forall (e1 e2: aexp) (n1 n2 : nat),
      (e1 || n1) -> (e2 || n2) -> (AMult e1 e2) || (n1 * n2)

  where "e '||' n" := (aevalR e n) : type_scope.

Tactic Notation "aevalR_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "E_ANum" | Case_aux c "E_APlus"
  | Case_aux c "E_AMinus" | Case_aux c "E_AMult" ].

Theorem aeval_iff_aevalR : forall a n,
  (a || n) <-> aeval a = n.
Proof.
  (* WORKED IN CLASS *)
  split.
  Case "->".
    intros H; induction H; subst; reflexivity.
  Case "<-".
    generalize dependent n.
    induction a; simpl; intros; subst; constructor;
       try apply IHa1; try apply IHa2; reflexivity.
Qed.

Definition state := id -> nat.

Definition empty_state : state :=
  fun _ => 0.

Definition update (st : state) (x : id) (n : nat) : state :=
  fun x' => if eq_id_dec x x' then n else st x'.



(*Require Export Assignment07_00.*)

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


(*Require Export Assignment07_01.*)

(* problem #02: 10 points *)

Fixpoint optimize_1mult (a:aexp) : aexp :=
  match a with
  | ANum n =>
      ANum n
  | APlus e1 e2 =>
      APlus (optimize_1mult e1) (optimize_1mult e2)
  | AMinus e1 e2 =>
      AMinus (optimize_1mult e1) (optimize_1mult e2)
  | AMult (ANum 1) e2 =>
      optimize_1mult e2
  | AMult e1 (ANum 1) =>
      optimize_1mult e1
  | AMult e1 e2 =>
      AMult (optimize_1mult e1) (optimize_1mult e2)
  end.

(** Hint:
    If you use the tacticals [;], [try] and [omega] well,
    you can prove the following theorem in 5 lines.
 **)

Theorem optimize_1mult_sound: forall a,
  aeval (optimize_1mult a) = aeval a.
Proof.
  intros.
  induction a;
    try(simpl; reflexivity);
    try(simpl; rewrite IHa1; rewrite IHa2; reflexivity).
    simpl.
    destruct a1. (*4*)
      - try (destruct n). (*2*)
        * try (destruct a2). (*4*)
          + destruct n. 
            simpl. reflexivity.
            destruct n. 
              simpl. reflexivity.
              simpl. reflexivity.
          + simpl. reflexivity.
          + simpl. reflexivity.
          + simpl. reflexivity.
        * destruct n. (*2*)
          + simpl. rewrite IHa2. omega.
          + destruct a2. (*4*)
            destruct n0. (*2*)
              simpl. reflexivity.
              destruct n0. (*2*)
                simpl. omega.
                simpl. reflexivity.
            simpl. simpl in IHa2. rewrite IHa2. reflexivity.
            simpl. simpl in IHa2. rewrite IHa2. reflexivity.
            simpl. simpl in IHa2. rewrite IHa2. reflexivity.
    - destruct a2. (*4*)
      * destruct n.
        + simpl. simpl in IHa1. rewrite IHa1. reflexivity.
        + simpl. simpl in IHa1. destruct n.
          simpl. omega.
          simpl. rewrite IHa1. reflexivity.
      * simpl. simpl in IHa1. simpl in IHa2. rewrite IHa1. rewrite IHa2. reflexivity.
      * simpl. simpl in IHa1. simpl in IHa2. rewrite IHa1. rewrite IHa2. reflexivity.
      * simpl. simpl in IHa1. simpl in IHa2. rewrite IHa1. rewrite IHa2. reflexivity.
    - destruct a2. (*4*)
      * destruct n.
        + simpl. simpl in IHa1. rewrite IHa1. reflexivity.
        + simpl. simpl in IHa1. destruct n.
          simpl. omega.
          simpl. rewrite IHa1. reflexivity.
      * simpl. simpl in IHa1. simpl in IHa2. rewrite IHa1. rewrite IHa2. reflexivity.
      * simpl. simpl in IHa1. simpl in IHa2. rewrite IHa1. rewrite IHa2. reflexivity.
      * simpl. simpl in IHa1. simpl in IHa2. rewrite IHa1. rewrite IHa2. reflexivity.
    - destruct a2. (*4*)
      * destruct n.
        + simpl. simpl in IHa1. rewrite IHa1. reflexivity.
        + simpl. simpl in IHa1. destruct n.
          simpl. omega.
          simpl. rewrite IHa1. reflexivity.
      * simpl. simpl in IHa1. simpl in IHa2. rewrite IHa1. rewrite IHa2. reflexivity.
      * simpl. simpl in IHa1. simpl in IHa2. rewrite IHa1. rewrite IHa2. reflexivity.
      * simpl. simpl in IHa1. simpl in IHa2. rewrite IHa1. rewrite IHa2. reflexivity.
Qed.

Theorem optimize_1mult_sound': forall a,
  aeval (optimize_1mult a) = aeval a.
Proof.
  intros.
  induction a;
    try(simpl; reflexivity);
    try(simpl; rewrite IHa1; rewrite IHa2; reflexivity).
    simpl.
    destruct a1;
      try(destruct a2; 
        try(simpl; simpl in IHa1; simpl in IHa2; rewrite IHa1; rewrite IHa2; reflexivity);
        destruct n; 
          simpl; simpl in IHa1; 
            try(rewrite IHa1; reflexivity);
            destruct n; simpl;
              try(omega);
              rewrite IHa1; reflexivity).
      destruct n.
        - destruct a2;
          try(simpl; reflexivity).
          destruct n.
            simpl; reflexivity.
            destruct n;
              simpl; reflexivity.
        - destruct n.
          simpl. rewrite IHa2. omega.
          destruct a2;
            try(simpl; simpl in IHa2; rewrite IHa2; reflexivity).
            destruct n0.
              simpl; reflexivity.
              destruct n0;
                simpl; omega.
Qed.



(*Require Export Assignment07_02.*)

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



(*Require Export Assignment07_03.*)

(* problem #04: 10 points *)

(** **** Exercise: 1 star, optional (neq_id)  *)
Lemma neq_id : forall (T:Type) x y (p q:T), x <> y -> 
               (if eq_id_dec x y then p else q) = q. 
Proof.
  intros. destruct (eq_id_dec x y); 
    try(reflexivity).
    try(apply ex_falso_quodlibet). unfold not in H. apply H. apply e.
Qed.
(** [] *)



(*Require Export Assignment07_04.*)

(* problem #05: 10 points *)

(** **** Exercise: 1 star (update_eq)  *)
Theorem update_eq : forall n x st,
  (update st x n) x = n.
Proof.
  intros. unfold update. 
  destruct (eq_id_dec x x); try(reflexivity).
  unfold not in n0. apply ex_falso_quodlibet. apply n0. reflexivity.
Qed.
(** [] *)



(*Require Export Assignment07_05.*)

(* problem #06: 10 points *)

(** **** Exercise: 1 star (update_neq)  *)
Theorem update_neq : forall x2 x1 n st,
  x2 <> x1 ->                        
  (update st x2 n) x1 = (st x1).
Proof.
  intros. unfold not in H. unfold update. 
  destruct (eq_id_dec x2 x1); try(reflexivity).
  apply ex_falso_quodlibet. apply H. apply e.
Qed.
(** [] *)



(*Require Export Assignment07_06.*)

(* problem #07: 10 points *)

(** **** Exercise: 1 star (update_example)  *)
(** Before starting to play with tactics, make sure you understand
    exactly what the theorem is saying! *)

Theorem update_example : forall (n:nat),
  (update empty_state (Id 2) n) (Id 3) = 0.
Proof.
  intros. unfold update. 
  destruct (eq_id_dec (Id 2) (Id 3)); 
    try(inversion e);
    try(unfold not in n0; unfold empty_state; reflexivity).
Qed.
(** [] *)



(*Require Export Assignment07_07.*)

(* problem #08: 10 points *)

(** **** Exercise: 1 star (update_shadow)  *)
Theorem update_shadow : forall n1 n2 x1 x2 (st : state),
   (update  (update st x2 n1) x2 n2) x1 = (update st x2 n2) x1.
Proof.
  intros. unfold update. destruct (eq_id_dec x2 x1); reflexivity.
Qed.
(** [] *)



(*Require Export Assignment07_08.*)

(* problem #09: 10 points *)

(** **** Exercise: 2 stars (update_same)  *)
Theorem update_same : forall n1 x1 x2 (st : state),
  st x1 = n1 ->
  (update st x1 n1) x2 = st x2.
Proof.
  intros. unfold update. 
  destruct (eq_id_dec x1 x2); 
    try(reflexivity);
    try(subst; reflexivity).
Qed.
(** [] *)



(*Require Export Assignment07_09.*)

(* problem #10: 10 points *)

(** **** Exercise: 3 stars (update_permute)  *)
Theorem update_permute : forall n1 n2 x1 x2 x3 st,
  x2 <> x1 -> 
  (update (update st x2 n1) x1 n2) x3 = (update (update st x1 n2) x2 n1) x3.
Proof.
  intros. unfold update.
  destruct (eq_id_dec x1 x3); destruct (eq_id_dec x2 x3);
    try (reflexivity);
    try(subst; unfold not in H; apply ex_falso_quodlibet; apply H; reflexivity).
Qed.
(** [] *)
