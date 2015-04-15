Require Export Assignment05_24.

(* problem #25: 10 points *)









(** 3 stars, optional (ev_plus_plus)  *)
(** Here's an exercise that just requires applying existing lemmas.  No
    induction or even case analysis is needed, but some of the rewriting
    may be tedious. 
    Hint: You can use [plus_comm], [plus_assoc], [double_plus], [double_even], [ev_sum], [ev_ev__ev].
*)
Check plus_comm.
Check plus_assoc.
Check double_plus.
Check double_even.
Check ev_sum.
Check ev_ev__ev.

Theorem ev_plus_plus : forall n m p,
  ev (n+m) -> ev (n+p) -> ev (m+p).
Proof.
    intros. apply ev_sum with (n:=n+p) in H. 
    rewrite plus_assoc in H. replace (n+p+n+m) with ((n+n)+(p+m)) in H. 
    apply ev_ev__ev with (n:= n+n) in H.
    - replace (m+p) with (p+m). apply H. apply plus_comm.
    - replace (n+n) with (double n). apply double_even. apply double_plus.
    - rewrite -> plus_assoc.  rewrite -> plus_comm with (n:=n+n). rewrite-> plus_assoc. rewrite -> plus_comm with (n:=p). reflexivity.
    - apply H0.
Qed.
(** [] *)


