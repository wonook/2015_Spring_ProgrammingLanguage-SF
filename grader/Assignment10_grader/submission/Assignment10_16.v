Require Export Assignment10_15.

(* problem #16: 10 points *)

(* Hint: 

   First study the chapter "Auto.v".

   Using [;], [try] and [eauto], you can prove it in 6 lines thanks to:
     Hint Constructors cstep.
 
   You can use the following intro pattern:
     destruct ... as [ | [? [? ?]]].
*)

Hint Constructors cstep.

Theorem cimp_strong_progress : forall c st,
  c = SKIP \/ 
  exists c' st', c / st ==>c c' / st'.
Proof.
  intros. induction c; eauto.
  - assert ((exists n, a = ANum n) \/ exists a', a / st ==>a a'). apply aexp_strong_progress. 
    inversion H. inversion H0. rewrite H1; eauto. inversion H0; eauto.
  - inversion IHc1; subst. inversion IHc2; subst. eauto. inversion H; eauto. inversion H; inversion H0; eauto.
  - assert ((b = BTrue \/ b = BFalse) \/ exists b', b / st ==>b b'). apply bexp_strong_progress.
    inversion H. inversion H0. rewrite H1; eauto. rewrite H1; eauto. inversion H0; eauto.
  - inversion IHc1; subst. inversion IHc2; subst. eauto. inversion H; inversion H0; eauto. inversion H; inversion H0; eauto.
Qed.

(*-- Check --*)
Check cimp_strong_progress : forall c st,
  c = SKIP \/ 
  exists c' st', c / st ==>c c' / st'.

