Require Export Assignment10_14.

(* problem #15: 10 points *)

(* Hint: 

   First study the chapter "Auto.v".

   Using [;], [try] and [eauto], you can prove it in 7 lines thanks to:. 
     Hint Constructors bstep.

   You can use the following intro pattern:
     destruct ... as [[? | ?] | [? ?]].
*)

Hint Constructors bstep.

Theorem bexp_strong_progress: forall st b,
  (b = BTrue \/ b = BFalse) \/
  exists b', b / st ==>b b'.
Proof.
  intros. induction b; eauto. 
  - assert ((exists n, a = ANum n) \/ exists a', a / st ==>a a'). apply aexp_strong_progress. 
    assert ((exists n, a0 = ANum n) \/ exists a', a0 / st ==>a a'). apply aexp_strong_progress.
    inversion H. inversion H1. rewrite H2. inversion H0. inversion H3. 
      rewrite H4; eauto.
      inversion H3; eauto.
      inversion H1; eauto.
  - assert ((exists n, a = ANum n) \/ exists a', a / st ==>a a'). apply aexp_strong_progress. 
    assert ((exists n, a0 = ANum n) \/ exists a', a0 / st ==>a a'). apply aexp_strong_progress.
    inversion H. inversion H1. rewrite H2. inversion H0. inversion H3. 
      rewrite H4; eauto.
      inversion H3; eauto.
      inversion H1; eauto.
  - inversion IHb. inversion H. rewrite H0; eauto. rewrite H0; eauto. inversion H; eauto.
  - inversion IHb1. inversion H. rewrite H0. inversion IHb2. inversion H1. 
    rewrite H2; eauto.
    rewrite H2; eauto.
    inversion H1; eauto.
    rewrite H0; eauto.
    inversion H; eauto.
Qed.

(*-- Check --*)
Check bexp_strong_progress: forall st b,
  (b = BTrue \/ b = BFalse) \/
  exists b', b / st ==>b b'.

