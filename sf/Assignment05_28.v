Require Export Assignment05_27.

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




