Require Export Assignment11_09.

(* problem #10: 30 points *)

(** Write a type checking function [tyeq: tm -> ty -> bool].
**)

Fixpoint tycheck (t: tm) (T: ty) : bool :=
  match t with
  | ttrue => match T with
              | TBool => true
              | _ => false
              end
  | tfalse => match T with
              | TBool => true
              | _ => false
              end
  | tif h tr fl => andb (tycheck h TBool) (andb (tycheck tr T) (tycheck fl T))
  | tzero => match T with
              | TNat => true
              | _ => false
              end
  | tsucc n => match T with
                | TNat => (tycheck n TNat)
                | _ => false
                end
  | tpred n => match T with
                | TNat => (tycheck n TNat)
                | _ => false
                end
  | tiszero n => match T with
                  | TBool => (tycheck n TNat)
                  | _ => false
                  end
  end.

Example tycheck_ex1:
  tycheck
    (tif (tiszero (tpred (tsucc (tsucc tzero)))) ttrue (tiszero (tsucc tzero))) 
    TBool 
  = true.
Proof. reflexivity. Qed.

Example tycheck_ex2:
  tycheck
    (tif (tiszero (tpred (tsucc (tsucc tzero)))) tzero (tiszero (tsucc tzero))) 
    TBool 
  = false.
Proof. reflexivity. Qed.

(** Prove that the type checking function [tyeq: tm -> ty -> bool] is correct.

    Hint: use the lemma [andb_prop].
**)

Check andb_prop.

Theorem tycheck_correct1: forall t T
    (TYCHK: tycheck t T = true),
  |- t \in T.
Proof.
  intros. generalize dependent T. induction t; intros.
  - destruct T. eauto. inversion TYCHK.
  - destruct T. eauto. inversion TYCHK.
  - inversion TYCHK. apply andb_prop in H0. inversion H0. apply andb_prop in H1. inversion H1. eauto.
  - destruct T. inversion TYCHK. eauto.
  - destruct T. inversion TYCHK. info_auto.
  - destruct T. inversion TYCHK. info_auto.
  - destruct T. eauto. inversion TYCHK.
Qed.

Theorem tycheck_correct2: forall t T
    (HASTY: |- t \in T),
  tycheck t T = true.
Proof.
  intros. generalize dependent T. induction t; intros.
  - destruct T. eauto. inversion HASTY.
  - destruct T. eauto. inversion HASTY.
  - simpl. inversion HASTY; subst. rewrite andb_true_iff. rewrite andb_true_iff. split. auto. auto.
  - destruct T. inversion HASTY. eauto.
  - destruct T. inversion HASTY. apply IHt. inversion HASTY. assumption.
  - destruct T. inversion HASTY. apply IHt. inversion HASTY. assumption.
  - destruct T. apply IHt. inversion HASTY. assumption. inversion HASTY.
Qed.

(*-- Check --*)

Check (conj tycheck_ex1 tycheck_ex2 :
 (tycheck
    (tif (tiszero (tpred (tsucc (tsucc tzero)))) ttrue (tiszero (tsucc tzero))) 
    TBool 
  = true)
 /\
 (tycheck
    (tif (tiszero (tpred (tsucc (tsucc tzero)))) tzero (tiszero (tsucc tzero))) 
    TBool 
  = false)).

Check tycheck_correct1: forall t T
    (TYCHK: tycheck t T = true),
  |- t \in T.

Check tycheck_correct2: forall t T
    (HASTY: |- t \in T),
  tycheck t T = true.
