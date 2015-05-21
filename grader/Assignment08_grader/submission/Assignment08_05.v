Require Export Assignment08_04.

(* problem #05: 20 points *)

(** Write a function which compiles an [aexp] into a stack
    machine program. The effect of running the program should be the
    same as pushing the value of the expression on the stack. *)

Fixpoint s_compile (e : aexp) : list sinstr :=
  match e with
  | ANum n => [SPush n]
  | AId i => [SLoad i]
  | APlus a1 a2 => (s_compile a1)++(s_compile a2)++[SPlus]
  | AMinus a1 a2 => (s_compile a1)++(s_compile a2)++[SMinus]
  | AMult a1 a2 => (s_compile a1)++(s_compile a2)++[SMult]
  end.

(** After you've defined [s_compile], prove the following to test
    that it works. *)

Example s_compile1 :
    s_compile (AMinus (AId X) (AMult (ANum 2) (AId Y)))
  = [SLoad X; SPush 2; SLoad Y; SMult; SMinus].
Proof.
  reflexivity.
Qed.

(** **** Exercise: 3 stars, advanced (stack_compiler_correct)  *)
(** The task of this exercise is to prove the correctness of the
    compiler implemented in the previous exercise.  Remember that
    the specification left unspecified what to do when encountering an
    [SPlus], [SMinus], or [SMult] instruction if the stack contains
    less than two elements.  (In order to make your correctness proof
    easier you may find it useful to go back and change your
    implementation!)

    Prove the following theorem, stating that the [compile] function
    behaves correctly.  You will need to start by stating a more
    general lemma to get a usable induction hypothesis; the main
    theorem will then be a simple corollary of this lemma. *)

Lemma s_compile_app : forall (st : state) (nl: list nat) (l1 l2 : list sinstr),
  s_execute st nl (l1 ++ l2) = s_execute st (s_execute st nl l1) l2.
Proof.
  intros. generalize dependent nl. induction l1.
  - reflexivity.
  - simpl. intros. destruct a.
    + apply IHl1.
    + apply IHl1.
    + destruct nl.
      * apply IHl1.
      * destruct nl. apply IHl1. apply IHl1.
    + destruct nl.
      * apply IHl1.
      * destruct nl. apply IHl1. apply IHl1.
    + destruct nl.
      * apply IHl1.
      * destruct nl. apply IHl1. apply IHl1.
Qed.

Lemma s_compile_correct0 : forall (st: state) (e:aexp) (nl:list nat),
  s_execute st nl (s_compile e) = aeval st e :: nl.
Proof.
  intros. generalize dependent nl. induction e; try (reflexivity); simpl.
  - intros. repeat (rewrite s_compile_app). rewrite IHe1. rewrite IHe2. reflexivity.
  - intros. repeat (rewrite s_compile_app). rewrite IHe1. rewrite IHe2. reflexivity.
  - intros. repeat (rewrite s_compile_app). rewrite IHe1. rewrite IHe2. reflexivity.
Qed.

Theorem s_compile_correct : forall (st : state) (e : aexp),
  s_execute st [] (s_compile e) = [ aeval st e ].
Proof.
  intros. apply s_compile_correct0.
Qed.

(*-- Check --*)
Check s_compile1 :
    s_compile (AMinus (AId X) (AMult (ANum 2) (AId Y)))
  = [SLoad X; SPush 2; SLoad Y; SMult; SMinus].

Check s_compile_correct : forall (st : state) (e : aexp),
  s_execute st [] (s_compile e) = [ aeval st e ].

