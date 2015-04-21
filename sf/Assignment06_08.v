Require Export Assignment06_07.

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
