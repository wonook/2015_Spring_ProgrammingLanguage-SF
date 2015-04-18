Require Export Assignment06_05.

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

