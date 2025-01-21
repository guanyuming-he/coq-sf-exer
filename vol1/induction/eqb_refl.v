Require Import LF.Basics.

Theorem eqb_refl : forall n : nat,
  (n =? n) = true.
Proof.
  intros n.
  induction n as [| n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite -> IHn'. reflexivity.
Qed.
