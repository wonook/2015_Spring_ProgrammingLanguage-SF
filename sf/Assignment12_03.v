Require Export Assignment12_02.

(* problem #03: 10 points *)

(** **** Exercise: 3 stars (types_unique)  *)
(** Another pleasant property of the STLC is that types are
    unique: a given term (in a given context) has at most one
    type. *)

Lemma type_is_unique: forall t G T T'
    (TYPED: G |- t \in T)
    (TYPED': G |- t \in T'),
  T = T'.
Proof.
  intros. generalize dependent T'. induction TYPED; intros; inversion TYPED'; subst; eauto.
  - rewrite H2 in H. inversion H. auto.
  - assert (T12 = T1). apply IHTYPED. assumption. 
    rewrite H. auto.
  - assert (TArrow T1 T2 = TArrow T0 T'). apply IHTYPED1. assumption.
    inversion H. auto.
  - assert (T1 = T0). apply IHTYPED1. assumption.
    assert (T2 = T3). apply IHTYPED2. assumption.
    subst. auto.
  - assert (TProd T1 T2 = TProd T' T3). apply IHTYPED. assumption.
    inversion H. auto.
  - assert (TProd T1 T2 = TProd T0 T'). apply IHTYPED. assumption.
    inversion H. auto.
  - apply IHTYPED2. assert (T1 = T0). apply IHTYPED1. assumption.
    rewrite H. auto.
  - assert (T1 = T0). apply IHTYPED. assumption.
    subst. auto.
  - assert (T2 = T3). apply IHTYPED. assumption.
    subst. auto.
  - assert (TSum T1 T2 = TSum T0 T3). apply IHTYPED1. assumption.
    inversion H.
    apply IHTYPED2. rewrite H1. assumption.
  - assert (TArrow (TArrow T1 T2) (TArrow T1 T2) = TArrow (TArrow T0 T3) (TArrow T0 T3)). apply IHTYPED. assumption. 
    inversion H. auto.
Qed.

(*-- Check --*)
Check type_is_unique: forall t G T T'
    (HTyped: G |- t \in T)
    (HTyped': G |- t \in T'),
  T = T'.

