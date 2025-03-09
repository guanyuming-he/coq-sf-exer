From LF.basics Require Import numbers.
From LF.induction Require Import basic_induction.

Theorem eqb_true : forall n m,
  n =? m = true -> n = m.
Proof.
  intros n.
  induction n.
  - intros m. destruct m.
    + simpl. reflexivity.
    + simpl. discriminate.
  - intros m. destruct m.
    + discriminate.
    + simpl. intros H. apply IHn in H.
      rewrite -> H. reflexivity.
Qed.

Theorem plus_n_n_injective : forall n m,
  n + n = m + m ->
  n = m.
Proof.
  intros n.
  induction n.
  - simpl. intros m. destruct m.
    + reflexivity.
    + discriminate.
  - intros m. destruct m. 
    + discriminate.
    + simpl. intros H. injection H as H1.
      rewrite -> add_comm in H1.
      rewrite -> (add_comm m (S m)) in H1.
      simpl in H1.
      injection H1 as H2.
      apply IHn in H2.
      rewrite -> H2.
      reflexivity.
Qed.

From LF.poly Require Import defns.

Theorem nth_error_after_last: forall (n : nat) (X : Type) (l : list X),
  length l = n ->
  nth_error l n = None.
Proof.
  intros n X l.
  generalize dependent n.
  induction l.
  - simpl.  reflexivity.
  - intros n. destruct n.
    + discriminate.
    + simpl. intros H.
      injection H as H1.
      apply IHl in H1.
      apply H1.
Qed.
