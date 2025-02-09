From LF Require Export basics.numbers.

(* Need this to prove commutativity of addition *)
Theorem add_0_r : forall n:nat, n + 0 = n.
Proof.
  intros n. induction n as [| n' IHn'].
  - (* n = 0 *) reflexivity.
  - (* n = S n' *) simpl. rewrite -> IHn'. reflexivity.
Qed.

Theorem mul_0_r : forall n:nat,
  n * 0 = 0.
Proof.
  intros n.
  induction n as [|n' IHn'].
  - reflexivity.
  - simpl. rewrite -> IHn'. reflexivity.
Qed.

Theorem plus_n_Sm : forall n m : nat,
  S (n + m) = n + (S m).
Proof.
  intros n.
  induction n as [|n' IHn'].
  - reflexivity.
  - simpl. intros m. rewrite -> IHn'. reflexivity.
Qed.

Theorem add_comm : forall n m : nat,
  n + m = m + n.
Proof.
  intros n.
  induction n as [| n' IHn'].
  - simpl. intros m. rewrite -> add_0_r. reflexivity.
  - intros m. simpl. rewrite -> IHn'. apply plus_n_Sm.
Qed.

Theorem add_assoc : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  intros n.
  induction n as [| n' IHn'].
  - simpl. reflexivity.
  - intros m p. simpl. rewrite -> IHn'.  reflexivity.
Qed.
