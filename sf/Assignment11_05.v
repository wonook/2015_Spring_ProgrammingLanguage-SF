Require Export Assignment11_04.

(* problem #05: 10 points *)

(** The typing relation enjoys two critical properties.  The first is
    that well-typed normal forms are values (i.e., not stuck). *)

(** **** Exercise: 3 stars (finish_progress)  *)
(** Complete the formal proof of the [progress] property.  (Make sure
    you understand the informal proof fragment in the following
    exercise before starting -- this will save you a lot of time.) *)

Theorem progress : forall t T,
  |- t \in T ->
  value t \/ exists t', t ==> t'.
Proof with auto.
  intros t T HT.
  has_type_cases (induction HT) Case...
  (* The cases that were obviously values, like T_True and
     T_False, were eliminated immediately by auto *)
  - Case "T_If".
    right. inversion IHHT1; clear IHHT1.
    SCase "t1 is a value".
    apply (bool_canonical t1 HT1) in H.
    inversion H; subst; clear H.
      exists t2...
      exists t3...
    SCase "t1 can take a step".
      inversion H as [t1' H1].
        exists (tif t1' t2 t3)...
  - Case "T_Succ".
    inversion IHHT; subst...
      inversion H... right. inversion H0; subst. inversion HT. inversion HT.
      inversion H. right. exists (tsucc x)...
  - Case "T_Pred".
    inversion IHHT; subst...
      inversion H... 
        right. inversion H0; subst. inversion HT. inversion HT.
        right. induction H0; subst. exists tzero... exists t...
      inversion H; subst. right. exists (tpred x)...
  - Case "T_Iszero".
    inversion IHHT; subst...
      inversion H...
        right. inversion H0; subst. inversion HT. inversion HT.
        right. inversion H0; subst. exists ttrue... exists tfalse...
      inversion H; subst. right. exists (tiszero x)...
Qed.

(*-- Check --*)
Check progress : forall t T,
  |- t \in T ->
  value t \/ exists t', t ==> t'.

