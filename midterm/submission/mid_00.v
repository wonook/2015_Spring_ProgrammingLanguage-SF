
Require Export Arith NPeano.

(** Important: 
    - You are NOT allowed to use the [admit] tactic
      because [admit] simply admits any goal 
      regardless of whether it is provable or not.

      But, you can leave [admit] for problems that you cannot prove.
      Then you will get zero points for those problems.

    - You are NOT allowed to use the following tactics.

      [tauto], [intuition], [firstorder], [omega].

    - Here is the list of tactics and tacticals you have learned.

      [intros]
      [revert]
      [reflexivity]
      [simpl]
      [rewrite]
      [induction]
      [assert]
      [unfold]
      [apply] ... [with] ... [in] ...
      [destruct] ... [as] ... [eqn:] ...
      [inversion]
      [symmetry]
      [generalize dependent]
      [split]
      [exists]
      [clear]
      [subst]
      [rename] ... [into] ...
      [contradiction]
      [constructor]
      [auto]
      [repeat]
      [try]
      [;]
**)

Definition admit {T: Type} : T.  Admitted.

(**
  Definition of [list] 
 **)

Inductive list (X:Type) : Type :=
  | nil : list X
  | cons : X -> list X -> list X.

Fixpoint app (X : Type) (l1 l2 : list X)
                : (list X) :=
  match l1 with
  | nil      => l2
  | cons h t => cons X h (app X t l2)
  end.

Arguments nil {X}.
Arguments cons {X} _ _.
Arguments app {X} l1 l2.

Notation "x :: y" := (cons x y)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y []) ..).
Notation "x ++ y" := (app x y)
                     (at level 60, right associativity).

Check (3 :: ([0; 1] ++ [])).

(**
  You may want to use the following lemmas.
 **)

Check mult_comm.
Check mult_1_r.
Check mult_assoc.
Check plus_comm.
Check plus_0_r.
Check plus_assoc.
Check plus_minus.
Check mult_plus_distr_l.
Check mult_plus_distr_r.
Check mult_minus_distr_l.
Check mult_minus_distr_r.

Check le_not_lt.
Check lt_le_trans.
Check lt_irrefl.

