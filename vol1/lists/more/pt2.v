From LF Require Import defns list_funs bag.

Theorem count_member_nonzero : forall (s : bag),
  1 <=? (count 1 (1 :: s)) = true.
Proof.
  intros s.
  simpl. reflexivity.
Qed.

Theorem leb_n_Sn : forall n,
  n <=? (S n) = true.
Proof.
  intros n. induction n as [| n' IHn'].
  - (* 0 *)
    simpl. reflexivity.
  - (* S n' *)
    simpl. rewrite IHn'. reflexivity. Qed.

Theorem remove_does_not_increase_count: forall (s : bag),
  (count 0 (remove_one 0 s)) <=? (count 0 s) = true.
Proof.
  intros s.
  induction s.
  - simpl. reflexivity.
  - destruct n.
    + simpl. rewrite -> leb_n_Sn. reflexivity.
    + simpl. exact IHs.
Qed.

Theorem bag_count_sum: forall b c : bag, forall n : nat,
  count n (sum b c) = (count n b) + (count n c).
Proof.
  intros b.
  induction b.
  - simpl. reflexivity.
  - simpl.
    intros c n0.
    destruct (n =? n0).
    + rewrite -> IHb. reflexivity.
    + rewrite -> IHb. reflexivity.
Qed.



