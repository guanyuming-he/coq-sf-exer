From LF.induction Require Import basic_induction.

(*
  Suppose we want to show that 
   [ forall x  P(x, y) ] -> Q(y).
  With specialize, we prove that
   exists x [ P(x, y) -> Q(y) ].
  Thus, if forall x P(x, y) is true,
  Q(y) must also be true, otherwise we would have
   forall x [ P(x, y) -> \neg Q(y) ], a contradiction.
 *)

Theorem specialize_example: forall n,
  (forall m, m*n = 0)
  -> n = 0.
Proof.
  intros n H.
  specialize H with (m := 1).
  simpl in H.
  rewrite add_comm in H.
  simpl in H.
  apply H. 
Qed.

