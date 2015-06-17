Require Export Assignment12_04.

(* problem #05: 20 points *)

(** Translate this informal recursive definition into one using [fix]:
<<
   halve = 
     \x:Nat. 
        if x=0 then 0 
        else if (pred x)=0 then 0
        else 1 + (halve (pred (pred x))))
>>
<<
  halve =
    fix
      (\f:nat->nat
        \x:nat.
          if0 x then 0
          else if0 (pred x) then 0
          else (succ (f (pred (pred x))))).
>>
*)

Definition halve : tm :=
    tfix
      (tabs Halve (TArrow TNat TNat)
        (tabs X TNat
          (tif0 (tvar X) (tnat 0)
            (tif0 (tpred (tvar X)) (tnat 0)
              (tsucc 
                (tapp (tvar Halve) (tpred (tpred (tvar X))))))))).

Example halve_type: empty |- halve \in TArrow TNat TNat.
Proof.
  (* unfold halve; eauto 10. *)
  unfold halve; eauto 10.
Qed.

Example halve_10: tapp halve (tnat 10) ==>* tnat 5.
Proof.
  (* unfold halve; normalize. *)
  unfold halve; normalize.
Qed.

Example halve_11: tapp halve (tnat 11) ==>* tnat 5.
Proof.
  (* unfold halve; normalize. *)
  unfold halve. normalize.
Qed.


Theorem halve_correct: forall n,
   tapp halve (tnat (n+n)) ==>* tnat n.
Proof.
  unfold halve. intros. induction n.
  - normalize.
  - eapply multi_step. 
      eapply ST_AppFix. apply v_abs. apply v_nat.
    eapply multi_step.
      eapply ST_App1. eapply ST_AppAbs. apply v_fix. apply v_abs.
    eapply multi_step. simpl.
      eapply ST_AppAbs. apply v_nat.
    eapply multi_step. simpl.
      eapply ST_If0Nonzero.
    eapply multi_step.
      eapply ST_If01. rewrite plus_comm. apply ST_PredNat.
    eapply multi_step. simpl.
      eapply ST_If0Nonzero. rewrite plus_comm. 
    eapply multi_step. simpl.
      eapply ST_Succ1. eapply ST_App2. apply v_fix. apply v_abs.
      eapply ST_Pred. eapply ST_PredNat.
    eapply multi_step. simpl.
      eapply ST_Succ1. eapply ST_App2. apply v_fix. apply v_abs.
      eapply ST_PredNat. simpl.
    assert (forall A, A ==>* tnat n -> tsucc A ==>* tnat (S n)).
      intros. eapply multi_trans.
      assert (forall t t', t ==>* t' -> tsucc t ==>* tsucc t').
        intros; induction H0; eauto.
      apply H0. apply H. eauto.
    apply H. apply IHn.
Qed.

(*-- Check --*)

Check conj halve_type (conj halve_10 halve_11) :
  empty |- halve \in TArrow TNat TNat /\
  tapp halve (tnat 10) ==>* tnat 5 /\ 
  tapp halve (tnat 11) ==>* tnat 5.

Check halve_correct: forall n,
   tapp halve (tnat (n + n)) ==>* tnat n.

