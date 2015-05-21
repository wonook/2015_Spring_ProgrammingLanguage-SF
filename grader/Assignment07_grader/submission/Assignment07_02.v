Require Export Assignment07_01.

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

