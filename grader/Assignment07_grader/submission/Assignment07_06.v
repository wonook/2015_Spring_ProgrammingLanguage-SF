Require Export Assignment07_05.

(* problem #06: 10 points *)

(** **** Exercise: 1 star (update_neq)  *)
Theorem update_neq : forall x2 x1 n st,
  x2 <> x1 ->                        
  (update st x2 n) x1 = (st x1).
Proof.
  intros. unfold not in H. unfold update. 
  destruct (eq_id_dec x2 x1); try(reflexivity).
  apply ex_falso_quodlibet. apply H. apply e.
Qed.
(** [] *)

