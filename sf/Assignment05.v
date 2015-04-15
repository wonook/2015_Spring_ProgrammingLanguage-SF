
Require Export MoreCoq.

(* Important: 
   - You are NOT allowed to use the [admit] tactic
     because [admit] simply admits any goal 
     regardless of whether it is provable or not.

     But, you can leave [admit] for problems that you cannot prove.
     Then you will get zero points for those problems.

   - You are NOT allowed to use the following tactics.

     [tauto], [intuition], [firstorder], [omega].

   - Do NOT add any additional `Require Import/Export`.
*)

Inductive and (P Q : Prop) : Prop :=
  conj : P -> Q -> (and P Q). 

Notation "P /\ Q" := (and P Q) : type_scope.

Inductive or (P Q : Prop) : Prop :=
  | or_introl : P -> or P Q
  | or_intror : Q -> or P Q. 

Notation "P \/ Q" := (or P Q) : type_scope.

Definition iff (P Q : Prop) := (P -> Q) /\ (Q -> P).

Notation "P <-> Q" := (iff P Q) 
                      (at level 95, no associativity) 
                      : type_scope.

Inductive False : Prop := . 

Definition not (P:Prop) := P -> False.

Notation "~ x" := (not x) : type_scope.

Notation "x <> y" := (~ (x = y)) : type_scope.

Inductive le : nat -> nat -> Prop :=
  | le_n : forall n, le n n
  | le_S : forall n m, (le n m) -> (le n (S m)).

Notation "m <= n" := (le m n).

Definition lt (n m:nat) := le (S n) m.

Notation "m < n" := (lt m n).

Definition even (n:nat) : Prop := 
  evenb n = true.

Inductive ev : forall (n: nat), Prop :=
  | ev_0 : ev O
  | ev_SS : forall (n:nat) (pf_evn :ev n), ev (S (S n))
.

Inductive beautiful : nat -> Prop :=
| b_0   : beautiful 0
| b_3   : beautiful 3
| b_5   : beautiful 5
| b_sum : forall n m (beuty_n:beautiful n) (beauty_m: beautiful m),
            beautiful (n+m)
.

Inductive gorgeous : nat -> Prop :=
  g_0 : gorgeous 0
| g_plus3 : forall n, gorgeous n -> gorgeous (3+n)
| g_plus5 : forall n, gorgeous n -> gorgeous (5+n)
.



(* problem #01: 10 points *)
(** 1 star, optional (proj2)  *)
Theorem proj2 : forall P Q : Prop, 
  P /\ Q -> Q.
Proof.
    intros. apply H.
Qed.
(** [] *)



(* problem #02: 10 points *)
(** 2 stars (and_assoc)  *)
(** In the following proof, notice how the _nested pattern_ in the
    [destruct] breaks the hypothesis [H : P /\ (Q /\ R)] down into
    [HP: P], [HQ : Q], and [HR : R].  Finish the proof from there: *)

Theorem and_assoc : forall P Q R : Prop, 
  P /\ (Q /\ R) -> (P /\ Q) /\ R.
Proof.
  intros P Q R H.
  destruct H as [HP [HQ HR]].
  split. split.
  apply HP. apply HQ. apply HR.
Qed.
(** [] *)



(* problem #03: 10 points *)
(** 1 star, optional (iff_properties)  *)
(** Using the above proof that [<->] is symmetric ([iff_sym]) as
    a guide, prove that it is also reflexive and transitive. *)
(** Hint: If you have an iff hypothesis in the context, you can use
    [inversion] to break it into two separate implications.  (Think
    about why this works.) *)


Theorem iff_refl : forall P : Prop, 
  P <-> P.
Proof. 
    intros. split. 
    intros. apply H.
    intros. apply H.
Qed.



(* problem #04: 10 points *)
Lemma injinj : forall P Q R : Prop,
    (P -> Q) /\ (Q -> R) -> (P -> R).
Proof.
    intros. inversion H. apply H2 in H1.
    - apply H1.
    - apply H0.
Qed.
Theorem iff_trans : forall P Q R : Prop, 
  (P <-> Q) -> (Q <-> R) -> (P <-> R).
Proof.
    intros. split.
    - intros. apply H in H1. apply H0 in H1. apply H1.
    - intros. apply H0 in H1. apply H in H1. apply H1.
Qed.



(* problem #05: 10 points *)
(** 1 star, optional (or_distributes_over_and)  *)
Theorem or_distributes_over_and : forall P Q R : Prop,
  P \/ (Q /\ R) <-> (P \/ Q) /\ (P \/ R).
Proof.
    intros. split.
    - intros. destruct H.
      split.
        left. apply H.
        left. apply H.
      split.
        right. apply H.
        right. apply H.
    - intros. inversion H. inversion H0.
      left. apply H2.
      inversion H1.
      left. apply H3.
      right. split.
      apply H2.
      apply H3.
Qed.
(** [] *)



(* problem #06: 10 points *)
(** 2 stars, optional (orb_false)  *)
Theorem orb_prop : forall b c,
  orb b c = true -> b = true \/ c = true.
Proof.
    intros. destruct b.
    - left. reflexivity.
    - right. apply H.
Qed.



(* problem #07: 10 points *)
(** 2 stars, optional (orb_false_elim)  *)
Theorem orb_false_elim : forall b c,
  orb b c = false -> b = false /\ c = false.
Proof.
    intros. destruct b.
    - inversion H.
    - destruct c.
      inversion H.
      split.
      reflexivity. reflexivity.
Qed.
(** [] *)



(* problem #08: 10 points *)
(** 2 stars, advanced (double_neg_inf)  *)
Theorem double_neg_inf: forall (P: Prop),
  P -> ~~P.
Proof.
    intros. unfold not. intros. apply H0. apply H.
Qed.
(** [] *)



(* problem #09: 10 points *)
(** 2 stars (contrapositive)  *)
Theorem contrapositive : forall P Q : Prop,
  (P -> Q) -> (~Q -> ~P).
Proof.
    intros. unfold not. unfold not in H0. intros. apply H in H1. apply H0 in H1. apply H1.
Qed.
(** [] *)



(* problem #10: 10 points *)
(** 1 star (not_both_true_and_false)  *)
Theorem not_both_true_and_false : forall P : Prop,
  ~ (P /\ ~P).
Proof. 
    intros. unfold not. intros. inversion H. apply H1 in H0. apply H0.
Qed.
(** [] *)



(* problem #11: 10 points *)
(** 3 stars (excluded_middle_irrefutable)  *)
(** This theorem implies that it is always safe to add a decidability
axiom (i.e. an instance of excluded middle) for any _particular_ Prop [P].
Why? Because we cannot prove the negation of such an axiom; if we could,
we would have both [~ (P \/ ~P)] and [~ ~ (P \/ ~P)], a contradiction. *)

Theorem excluded_middle_irrefutable:  forall (P:Prop), ~ ~ (P \/ ~ P).  
Proof.
    intros. unfold not. intros. apply H. right. intros. apply H. left. apply H0.
Qed.



(* problem #12: 10 points *)
(** 2 stars (false_beq_nat)  *)
Lemma false_induction : forall P : Prop,
    False -> P.
Proof.
    intros. inversion H.
Qed.

Theorem false_beq_nat : forall n m : nat,
     n <> m ->
     beq_nat n m = false.
Proof.
    (* DIFFICULT *)
    intros n m. unfold not. intros. generalize dependent m. induction n.
    - intros. induction m.
      apply false_induction. apply H. reflexivity.
      simpl. reflexivity.
    - intros. induction m.
      simpl.  reflexivity.
      simpl. apply IHn. intros. apply H. apply f_equal. apply H0.
Qed.
(** [] *)



(* problem #13: 10 points *)
(** 2 stars, optional (beq_nat_false)  *)
Theorem beq_nat_false : forall n m,
  beq_nat n m = false -> n <> m.
Proof.
    intros n m. unfold not. intros. generalize dependent m. induction n.
    - intros. induction m.
      inversion H.
      inversion H0.
    - intros. induction m.
      inversion H0.
      apply IHn with m. apply H. inversion H0. reflexivity.
Qed.
(** [] *)



(* problem #14: 10 points *)
(** 2 star (ev__even)  *)
Theorem ev__even: forall n : nat,
  ev n -> even n.
Proof.
    (* GET THE HANG OF IT *)
    intros. unfold even. induction H.
    - reflexivity.    
    - simpl. apply IHev.
Qed.
(** [] *)



(* problem #15: 10 points *)
(** 1 star (double_even)  *)
Theorem double_even : forall n,
  ev (double n).
Proof.
    intros. induction n.
    - simpl. apply ev_0.
    - simpl. apply ev_SS. apply IHn.
Qed.
(** [] *)



(* problem #16: 10 points *)
(** 2 stars (b_times2)  *)
Theorem b_times2: forall n, beautiful n -> beautiful (2*n).
Proof.
    intros. simpl. apply b_sum.
    - apply H.
    - apply b_sum. apply H. apply b_0.
Qed.
(** [] *)



(* problem #17: 10 points *)
(** 3 stars (b_timesm)  *)
Theorem b_timesm: forall n m, beautiful n -> beautiful (m*n).
Proof.
    intros. induction m. 
    - simpl. apply b_0.
    - simpl. apply b_sum. apply H. apply IHm.
Qed.
(** [] *)



(* problem #18: 10 points *)
(** 1 star (gorgeous_plus13)  *)
Theorem gorgeous_plus13: forall n, 
  gorgeous n -> gorgeous (13+n).
Proof.
    intros. apply g_plus3. apply g_plus5. apply g_plus5. apply H.
Qed.
(** [] *)



(* problem #19: 10 points *)
(** 2 stars (gorgeous_sum)  *)
Theorem gorgeous_sum : forall n m,
  gorgeous n -> gorgeous m -> gorgeous (n + m).
Proof.
    intros. induction H.
    - simpl. apply H0.
    - apply g_plus3 with (n:=n+m). apply IHgorgeous.
    - apply g_plus5 with (n:=n+m). apply IHgorgeous.
Qed.
(** [] *)



(* problem #20: 10 points *)
(** 3 stars, advanced (beautiful__gorgeous)  *)
Theorem beautiful__gorgeous : forall n, beautiful n -> gorgeous n.
Proof.
    intros. induction H.
    - apply g_0.
    - apply g_plus3. apply g_0.
    - apply g_plus5. apply g_0.
    - apply gorgeous_sum. apply IHbeautiful1. apply IHbeautiful2.
Qed.
(** [] *)



(* problem #21: 10 points *)
(** 2 stars (ev_sum)  *)

Theorem ev_sum : forall n m,
   ev n -> ev m -> ev (n+m).
Proof. 
    intros. induction H. 
    - simpl. apply H0.
    - simpl. apply ev_SS. apply IHev.
Qed.
(** [] *)



(* problem #22: 10 points *)
(** 1 star (inversion_practice)  *)
Theorem SSSSev__even : forall n,
  ev (S (S (S (S n)))) -> ev n.
Proof.
    intros. inversion H. inversion pf_evn. apply pf_evn0. 
Qed.

(** The [inversion] tactic can also be used to derive goals by showing
    the absurdity of a hypothesis. *)



(* problem #23: 10 points *)
(** 1 star (inversion_practice)  *)
Theorem even5_nonsense : 
  ev 5 -> 2 + 2 = 9.
Proof.
    (* weird coincidence *)
    intros. inversion H. inversion pf_evn. inversion pf_evn0.
Qed.
(** [] *)



(* problem #24: 10 points *)
(** 3 stars, advanced (ev_ev__ev)  *)
(** Finding the appropriate thing to do induction on is a
    bit tricky here: *)

Theorem ev_ev__ev : forall n m,
  ev (n+m) -> ev n -> ev m.
Proof.
    (* induction H0.!! *)
    intros. induction H0.
    - simpl in H. apply H.
    - inversion H. apply IHev. apply pf_evn.
Qed.
(** [] *)



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



(* problem #26: 10 points *)
(** 3 star (even__ev)  
    Note that proving [even__ev] directly is hard.
    You might find it easier to prove [even__ev_strong] first
    and then prove [even__ev] using it.
*)

Lemma evenb_SS: forall n: nat,
    evenb n = evenb (S (S n)).
Proof.
  intros. induction n.
  - reflexivity.
  - simpl. reflexivity.
Qed.
Lemma S_pred_n: forall n: nat,
    (pred (S n)) = n.
Proof.
    intros. induction n.
    simpl. reflexivity.
    simpl. reflexivity.
Qed.
Lemma even__ev_strong: forall n : nat, 
  (even (pred n) -> ev (pred n)) /\ (even n -> ev n).
Proof.
    intros. induction n.
    - split. 
      intros. simpl. apply ev_0.
      intros. apply ev_0.
    - split. 
      intros. simpl. apply IHn. simpl in H. apply H.
      intros. inversion IHn. destruct n.
        inversion H.
        inversion H. apply ev_SS. simpl in H0. apply H0. unfold even. apply H3.
Qed.
(** [] *)



(* problem #27: 10 points *)
Theorem even__ev: forall n : nat,
  even n -> ev n.
Proof.
    intros. induction n.
    - apply ev_0.
    - SearchAbout ev. apply even__ev_strong with (n:=(S n)). apply H.
Qed.
(** [] *)



(* problem #28: 30 points *)
(** 4 stars (palindromes)  *)
(** A palindrome is a sequence that reads the same backwards as
    forwards.

    - Define an inductive proposition [pal] on [list X] that
      captures what it means to be a palindrome. (Hint: You'll need
      three cases.  Your definition should be based on the structure
      of the list; just having a single constructor
        c : forall l, l = rev l -> pal l
      may seem obvious, but will not work very well.)
 
    - Prove [pal_app_rev] that 
       forall l, pal (l ++ rev l).
    - Prove [pal_rev] that 
       forall l, pal l -> l = rev l.
*)
Inductive pal {X: Type} : list X -> Prop :=
  | pal_nil : pal nil
  | pal_one : forall n:X, pal [n]
  | pal_add : forall (n:X) (l:list X), pal l -> pal(n::l++[n])
.

Lemma snoc_to_plus: forall (X: Type) (l: list X) (n: X),
    snoc l n = l ++ [n].
Proof.
    intros. induction l.
    - simpl. reflexivity.
    - simpl. rewrite IHl. reflexivity.
Qed.
Theorem app_assoc : forall (X: Type) (l1 l2 l3 : list X), 
      (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).   
      Proof.
            intros x l1 l2 l3. induction l1 as [| n l1'].
              - reflexivity.
                - simpl. rewrite -> IHl1'. reflexivity.  
      Qed.
Theorem pal_app_rev: forall (X: Type) (l: list X),
  pal (l ++ rev l).
Proof.
    intros. replace (l++ rev l) with (l ++ nil ++ rev l). induction l.
    simpl. apply pal_nil.
    simpl. rewrite snoc_to_plus. replace (x::l++rev l++[x]) with (x::(l++rev l)++[x]). apply pal_add with (n:=x). apply IHl. rewrite app_assoc. reflexivity.
    simpl. reflexivity.
Qed.

Lemma rev_app: forall (X: Type) (a: X) (b:list X),
    rev(b++[a]) = [a]++(rev b).
Proof.
    intros. induction b.
    reflexivity.
    simpl. rewrite IHb. reflexivity.
Qed.
Theorem pal_rev: forall (X: Type) (l: list X),
  pal l -> l = rev l.
Proof.
    intros. induction H.
    - reflexivity.
    - reflexivity.
    - simpl. rewrite snoc_to_plus. rewrite rev_app. simpl. rewrite <- IHpal. reflexivity.
Qed.

(** [] *)



(* problem #29: 10 points *)
(** 2 stars, optional (le_exercises)  *)
(** Here are a number of facts about the [<=] and [<] relations that
    we are going to need later in the course.  The proofs make good
    practice exercises. *)

Lemma le_trans : forall m n o, m <= n -> n <= o -> m <= o.
Proof.
    intros. induction H0.
    apply H.
    apply le_S. apply IHle. apply H.
Qed.



(* problem #30: 10 points *)
Theorem O_le_n : forall n,
  0 <= n.
Proof.
    intros. induction n.
    apply le_n.
    apply le_S. apply IHn.
Qed.



(* problem #31: 10 points *)
Theorem n_le_m__Sn_le_Sm : forall n m,
  n <= m -> S n <= S m.
Proof. 
    (* Get used to it!! *)
    intros. induction H.
    apply le_n.
    apply le_S. apply IHle.
Qed.



(* problem #32: 10 points *)
Theorem Sn_le_Sm__n_le_m : forall n m,
  S n <= S m -> n <= m.
Proof. 
    intros. inversion H.
    - apply le_n.
    - apply le_trans with (m:=n) (n:=(S n)) (o:=m). 
    (* careful! *)
      apply le_S. apply le_n.
      apply H2.
Qed.



(* problem #33: 10 points *)
Theorem le_plus_l : forall a b,
  a <= a + b.
Proof. 
    intros. induction a.
    - simpl. apply O_le_n.
    - simpl. apply n_le_m__Sn_le_Sm. apply IHa.
Qed.



(* problem #34: 10 points *)
Theorem plus_lt : forall n1 n2 m,
  n1 + n2 < m ->
  n1 < m /\ n2 < m.
Proof. 
 unfold lt. 
 intros. inversion H. 
 - split.
    apply n_le_m__Sn_le_Sm. apply le_plus_l.
    apply n_le_m__Sn_le_Sm. rewrite plus_comm with (n:=n1) (m:=n2). apply le_plus_l.
 - split.
    apply n_le_m__Sn_le_Sm. assert (n1 <= S (n1 + n2)).
      apply le_S. apply le_plus_l.
      SearchAbout le.
      apply le_trans with (n:=S (n1 + n2)). apply H3. apply H0.
    apply n_le_m__Sn_le_Sm. assert (n2 <= S (n1 + n2)).
      apply le_S. rewrite plus_comm. apply le_plus_l.
      apply le_trans with (n:= S (n1 + n2)). apply H3. apply H0.
Qed.



(* problem #35: 10 points *)
Theorem lt_S : forall n m,
  n < m ->
  n < S m.
Proof.
    unfold lt. intros. 
    apply n_le_m__Sn_le_Sm. assert (n <= S n).
      apply le_S. apply le_n.
      apply le_trans with (n:= S n). apply H0. apply H.
Qed.



(* problem #36: 10 points *)
Theorem ble_nat_true : forall n m,
  ble_nat n m = true -> n <= m.
Proof. 
    (* hard time.. *)
    intros. generalize dependent n. induction m.
    - intros. destruct n.
      apply le_n.
      inversion H. 
    - intros. destruct n.
      apply O_le_n.
      apply n_le_m__Sn_le_Sm. apply IHm. simpl in H. apply H.
Qed.



(* problem #37: 10 points *)
Theorem le_ble_nat : forall n m,
  n <= m ->
  ble_nat n m = true.
Proof.
  (* Hint: This may be easiest to prove by induction on [m]. *)
    intros. generalize dependent n. induction m.
    - intros. inversion H. reflexivity.
    (* hard time here //*)
    - intros. destruct n.
      simpl. reflexivity.
      simpl. apply IHm. apply Sn_le_Sm__n_le_m. apply H.
Qed.



(* problem #38: 10 points *)
Theorem ble_nat_true_trans : forall n m o,
  ble_nat n m = true -> ble_nat m o = true -> ble_nat n o = true.                               
Proof.
  (* Hint: This theorem can be easily proved without using [induction]. *)
    (*Transition between ble_nat and le!! *)
    intros. apply le_ble_nat. apply ble_nat_true in H. apply ble_nat_true in H0.
    apply le_trans with (n:=m).
      apply H. apply H0.
Qed.



(* problem #39: 10 points *)
Theorem ble_nat_false : forall n m,
  ble_nat n m = false -> ~(n <= m).
Proof.
    unfold not.
    intros. generalize dependent m. induction n.
    - intros. inversion H.
    - intros. destruct m.
      inversion H0.
      apply (IHn m). simpl in H. apply H.
      apply Sn_le_Sm__n_le_m. apply H0.
Qed.
(** [] *)




