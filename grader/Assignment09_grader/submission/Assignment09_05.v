Require Export Assignment09_04.

(* problem #05: 10 points *)

(** **** Exercise: 2 stars (if_minus_plus)  *)
(** Prove the following hoare triple using [hoare_if]: *)

Theorem if_minus_plus :
  {{fun st => True}}
  IFB (BLe (AId X) (AId Y))
    THEN (Z ::= AMinus (AId Y) (AId X))
    ELSE (Y ::= APlus (AId X) (AId Z))
  FI
  {{fun st => st Y = st X + st Z}}. 
Proof.
  eapply hoare_consequence_pre.
    apply hoare_if. 
      apply hoare_asgn. apply hoare_asgn.
      unfold assn_sub, update, assert_implies. simpl.
        intros. split. 
          destruct (ble_nat (st X) (st Y)) eqn:eqn. 
            intros. apply le_plus_minus. apply ble_nat_true in eqn. apply eqn.
            intros. inversion H0.
          destruct (ble_nat (st X) (st Y)) eqn:eqn.
            intros. inversion H0.
            intros. reflexivity.
Qed.

(*-- Check --*)
Check if_minus_plus :
  {{fun st => True}}
  IFB (BLe (AId X) (AId Y))
    THEN (Z ::= AMinus (AId Y) (AId X))
    ELSE (Y ::= APlus (AId X) (AId Z))
  FI
  {{fun st => st Y = st X + st Z}}. 

