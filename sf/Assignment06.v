
Require Export "Prop".

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


Inductive ex (X:Type) (P : X->Prop) : Prop :=
  ex_intro : forall (witness:X) (proof: P witness), ex X P.

Notation "'exists' x , p" := (ex _ (fun x => p))
  (at level 200, x ident, right associativity) : type_scope.
Notation "'exists' x : X , p" := (ex _ (fun x:X => p))
  (at level 200, x ident, right associativity) : type_scope.

Theorem eq_nat_dec : forall n m : nat, {n = m} + {n <> m}.
Proof.
  (* WORKED IN CLASS *)
  intros n.
  induction n as [|n'].
  Case "n = 0".
    intros m.
    destruct m as [|m'].
    SCase "m = 0".
      left. reflexivity.
    SCase "m = S m'".
      right. intros contra. inversion contra.
  Case "n = S n'".
    intros m.
    destruct m as [|m'].
    SCase "m = 0".
      right. intros contra. inversion contra.
    SCase "m = S m'". 
      destruct IHn' with (m := m') as [eq | neq].
      left. apply f_equal.  apply eq.
      right. intros Heq. inversion Heq as [Heq']. apply neq. apply Heq'.
Defined. 

Definition override' {X: Type} (f: nat->X) (k:nat) (x:X) : nat->X:=
  fun (k':nat) => if eq_nat_dec k k' then x else f k'.



(* problem #01: 10 points *)


(** **** Exercise: 1 star (dist_not_exists)  *)
(** Prove that "[P] holds for all [x]" implies "there is no [x] for
    which [P] does not hold." *)

Theorem dist_not_exists : forall (X:Type) (P : X -> Prop),
  (forall x, P x) -> ~ (exists x, ~ P x).
Proof. 
    intros. unfold not. intros. inversion H0. apply proof. apply H.
Qed.
(** [] *)



(* problem #02: 10 points *)

(** **** Exercise: 3 stars, optional (not_exists_dist)  *)
(** (The other direction of this theorem requires the classical "law
    of the excluded middle".) *)

Theorem not_exists_dist :
  excluded_middle ->
  forall (X:Type) (P : X -> Prop),
    ~ (exists x, ~ P x) -> (forall x, P x).
Proof.
    intros. unfold not in H0. unfold excluded_middle in H. unfold not in H.
    destruct H with (P:=(P x)). 
    - apply H1. 
    (* Careful! *)
    - apply ex_falso_quodlibet. apply H0. apply ex_intro with (witness:=x). apply H1.
Qed.
(** [] *)



(* problem #03: 10 points *)

(** **** Exercise: 2 stars (dist_exists_or)  *)
(** Prove that existential quantification distributes over
    disjunction. *)

Theorem dist_exists_or : forall (X:Type) (P Q : X -> Prop),
  (exists x, P x \/ Q x) <-> (exists x, P x) \/ (exists x, Q x).
Proof.
    intros. split.
    (* !! *)
    - intros. destruct H. inversion proof. 
      left. exists witness. apply H.
      right. exists witness. apply H.
    - intros. inversion H. inversion H0.
      exists witness. left. apply proof.
      inversion H0. exists witness. right. apply proof.
Qed.
(** [] *)



(* problem #04: 10 points *)

(** **** Exercise: 1 star (override_shadow')  *)
Theorem override_shadow' : forall (X:Type) x1 x2 k1 k2 (f : nat->X),
  (override' (override' f k1 x2) k1 x1) k2 = (override' f k1 x1) k2.
Proof.
    intros. unfold override'. destruct (eq_nat_dec k1 k2).
    - reflexivity.
    - reflexivity.
Qed.
(** [] *)



(* problem #05: 20 points *)

(** **** Exercise: 3 stars (all_forallb)  *)
(** Inductively define a property [all] of lists, parameterized by a
    type [X] and a property [P : X -> Prop], such that [all X P l]
    asserts that [P] is true for every element of the list [l]. *)

Inductive all {X : Type} (P : X -> Prop) : list X -> Prop :=
| all_empty: all P []
| all_list: forall (x:X) (l:list X), P x /\ all P l -> all P (x::l)
.

(** Recall the function [forallb], from the exercise
    [forall_exists_challenge] in chapter [Poly]: *)

Fixpoint forallb {X : Type} (test : X -> bool) (l : list X) : bool :=
  match l with
    | [] => true
    | x :: l' => andb (test x) (forallb test l')
  end.

(** Using the property [all], write down a specification for [forallb],
    and prove that it satisfies the specification. Try to make your 
    specification as precise as possible.

    Are there any important properties of the function [forallb] which
    are not captured by your specification? *)

Theorem forallb_correct: forall X (P: X -> bool) l,
  forallb P l = true <-> all (fun x => P x = true) l.
Proof.
    intros. split.
    - induction l.
      intros. apply all_empty.
      simpl. intros. destruct (P x) eqn:Px.
        apply all_list. split. apply Px. apply IHl. simpl in H. apply H. destruct (forallb P l).
            apply all_list. split. rewrite Px. simpl in H. apply H.
            apply IHl. reflexivity.
        simpl in H. inversion H.
    - induction l.
        intros. simpl. reflexivity.
        intros. simpl. destruct (P x) eqn:Px.
            simpl. apply IHl. inversion H. apply H1.
            inversion H. rewrite Px in H1. simpl. apply H1.
Qed.

(** [] *)



(* problem #06: 20 points *)

(** **** Exercise: 4 stars, advanced (no_repeats)  *)
(** The following inductively defined proposition... *)

Inductive appears_in {X:Type} (a:X) : list X -> Prop :=
  | ai_here : forall l, appears_in a (a::l)
  | ai_later : forall b l, appears_in a l -> appears_in a (b::l).

(** ...gives us a precise way of saying that a value [a] appears at
    least once as a member of a list [l]. 

    Here's a pair of warm-ups about [appears_in].
*)

Lemma list_app_nil : forall {X:Type} (l:list X),
    l = l ++ [].
Proof.
    intros. induction l.
    reflexivity.
    symmetry. simpl. rewrite <- IHl. reflexivity.
Qed.

Lemma appears_in_app : forall (X:Type) (xs ys : list X) (x:X), 
     appears_in x (xs ++ ys) -> appears_in x xs \/ appears_in x ys.
Proof.
  intros. induction xs.
    simpl in H. right. apply H.
      destruct ys eqn:Ys.
        left. simpl in H. replace (xs ++ []) with (xs) in H. apply H. 
          apply list_app_nil.
        inversion H.
          left. apply ai_here.
          apply IHxs in H1. inversion H1. 
            left. apply ai_later. apply H3.
            right. apply H3.
Qed.

Lemma app_appears_in : forall (X:Type) (xs ys : list X) (x:X), 
     appears_in x xs \/ appears_in x ys -> appears_in x (xs ++ ys).
Proof.
    intros. induction xs.
      simpl. inversion H. inversion H0. apply H0.
      simpl. inversion H. inversion H0.
        apply ai_here.
        apply ai_later. apply IHxs. left. apply H2.
        apply ai_later. apply IHxs. right. apply H0.
Qed.



(* problem #07: 10 points *)

(** **** Exercise: 3 stars (nostutter)  *)
(** Formulating inductive definitions of predicates is an important
    skill you'll need in this course.  Try to solve this exercise
    without any help at all.

    We say that a list of numbers "stutters" if it repeats the same
    number consecutively.  The predicate "[nostutter mylist]" means
    that [mylist] does not stutter.  Formulate an inductive definition
    for [nostutter].  (This is different from the [no_repeats]
    predicate in the exercise above; the sequence [1;4;1] repeats but
    does not stutter.) *)

Inductive nostutter:  list nat -> Prop :=
| nostutter_nil: nostutter []
| nostutter_one: forall (n:nat), nostutter [n]
| nostutter_next: forall (l:list nat) (a b:nat), nostutter (a::l) /\ not(eq a b) -> nostutter (b:: (a::l))
.

(** Make sure each of these tests succeeds, but you are free
    to change the proof if the given one doesn't work for you.
    Your definition might be different from mine and still correct,
    in which case the examples might need a different proof.
   
    The suggested proofs for the examples (in comments) use a number
    of tactics we haven't talked about, to try to make them robust
    with respect to different possible ways of defining [nostutter].
    You should be able to just uncomment and use them as-is, but if
    you prefer you can also prove each example with more basic
    tactics.  *)

Example test_nostutter_1:      nostutter [3;1;4;1;5;6].
Proof. repeat constructor; apply beq_nat_false; auto. Qed.
(* 
  Proof. repeat constructor; apply beq_nat_false; auto. Qed.
*)

Example test_nostutter_2:  nostutter [].
Proof. repeat constructor; apply beq_nat_false; auto. Qed.
(* 
  Proof. repeat constructor; apply beq_nat_false; auto. Qed.
*)

Example test_nostutter_3:  nostutter [5].
Proof. repeat constructor; apply beq_nat_false; auto. Qed.
(* 
  Proof. repeat constructor; apply beq_nat_false; auto. Qed.
*)

Example test_nostutter_4:      not (nostutter [3;1;1;4]).
  Proof. intro.
  repeat match goal with 
    h: nostutter _ |- _ => inversion h; clear h; subst 
  end.
  inversion H1.
   repeat match goal with 
    h: nostutter _ |- _ => inversion h; clear h; subst 
  end.
  inversion H3.
  contradiction H2; auto. Qed.
(* 
  Proof. intro.
  repeat match goal with 
    h: nostutter _ |- _ => inversion h; clear h; subst 
  end.
  contradiction H1; auto. Qed.
*)
(** [] *)



(* problem #08: 40 points *)

(** **** Exercise: 4 stars, advanced (pigeonhole principle)  *)
(** The "pigeonhole principle" states a basic fact about counting:
   if you distribute more than [n] items into [n] pigeonholes, some 
   pigeonhole must contain at least two items.  As is often the case,
   this apparently trivial fact about numbers requires non-trivial
   machinery to prove, but we now have enough... *)

(** First a pair of useful lemmas (we already proved these for lists
    of naturals, but not for arbitrary lists). *)

Lemma app_length : forall (X:Type) (l1 l2 : list X),
  length (l1 ++ l2) = length l1 + length l2. 
Proof. 
    intros. induction l1.
      simpl. reflexivity.
      simpl. rewrite IHl1. reflexivity.
Qed.

Lemma appears_in_app_split : forall (X:Type) (x:X) (l:list X),
  appears_in x l -> 
  exists l1, exists l2, l = l1 ++ (x::l2).
Proof.
    intros. induction H.
      exists []. exists l. simpl. reflexivity.
      inversion IHappears_in. inversion proof. exists (b::witness). exists witness0. simpl. rewrite proof0. reflexivity.
Qed.

(** Now define a predicate [repeats] (analogous to [no_repeats] in the
   exercise above), such that [repeats X l] asserts that [l] contains
   at least one repeated element (of type [X]).  *)

Inductive repeats {X:Type} : list X -> Prop :=
  | repeats_here: forall (a:X) (l:list X), appears_in a l -> repeats (a::l)
  | repeats_later: forall a (l: list X), repeats l -> repeats (a::l)
.

(** Now here's a way to formalize the pigeonhole principle. List [l2]
    represents a list of pigeonhole labels, and list [l1] represents
    the labels assigned to a list of items: if there are more items
    than labels, at least two items must have the same label.  This
    proof is much easier if you use the [excluded_middle] hypothesis
    to show that [appears_in] is decidable, i.e. [forall x
    l, (appears_in x l) \/ ~ (appears_in x l)].  However, it is also
    possible to make the proof go through _without_ assuming that
    [appears_in] is decidable; if you can manage to do this, you will
    not need the [excluded_middle] hypothesis. *)

Lemma ai_comm : forall {X:Type} (x y:X) (l1 l2: list X),
    appears_in x (l1++l2) -> appears_in x (l2++l1).
Proof.
    intros. SearchAbout appears_in. apply app_appears_in. apply appears_in_app in H. SearchAbout or. apply or_commut. apply H.
Qed.

Lemma ai_latter : forall {X:Type} (x y:X) (l: list X),
    x <> y -> appears_in x (y::l) -> appears_in x l.
Proof.
    intros. inversion H0.
      rewrite H2 in H. destruct H. reflexivity.
      apply H2.
Qed.

Theorem pigeonhole_principle: forall {X:Type} (l1 l2:list X),
    excluded_middle ->
    (forall x, appears_in x l1 -> appears_in x l2) ->
    length l2 < length l1 ->
    repeats l1.
Proof.
   intros X l1. induction l1.
   - intros. inversion H1.
   - intros.
      assert (repeats l1 \/ ~ repeats l1). unfold excluded_middle in H. apply H. inversion H2.
        apply repeats_later. apply H3.
      assert (appears_in x l1 \/ ~ appears_in x l1). unfold excluded_middle in H. apply H. inversion H4.
        apply repeats_here. apply H5.
      assert (appears_in x l2). apply H0. apply ai_here.
      apply repeats_later. destruct (appears_in_app_split X x l2). apply H6. destruct proof.
      apply IHl1 with (witness++witness0).
        apply H.
        intros.
          assert (appears_in x0 l2). apply H0. apply ai_later. apply H7.
          rewrite proof in H8. apply ai_comm in H8. simpl in H8. apply ai_latter with (y:=x) in H8.
            apply ai_comm. apply x0. apply H8.
            assert (x0=x \/ x0<>x). apply H. inversion H9. rewrite <- H10 in H5. apply ex_falso_quodlibet. apply H5. apply H7.
            apply H10. apply x0.
        rewrite proof in H1. rewrite app_length. rewrite app_length in H1. simpl in H1. rewrite <- plus_n_Sm in H1.
        unfold lt in H1. unfold lt. apply Sn_le_Sm__n_le_m. apply H1.
Qed.

