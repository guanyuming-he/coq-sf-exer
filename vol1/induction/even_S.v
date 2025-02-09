From LF Require Export numbers.

Theorem even_S: forall n : nat,
  even (S n) = negb (even n).
Proof.
  intros n.
  induction n as [| n' IHn'].
  - simpl. reflexivity.
  - rewrite -> IHn'. simpl. 
    (* negb negb x = x *) rewrite -> negb_involutive. reflexivity.
Qed.
