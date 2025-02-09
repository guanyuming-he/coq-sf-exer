From LF.lists Require Import defns list_funs bag more.pt1.

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


Theorem involution_injective : forall (f : nat -> nat),
    (forall n : nat, n = f (f n)) -> (forall n1 n2 : nat, f n1 = f n2 -> n1 = n2).
Proof.
  intros f H1.
  intros n1 n2.
  intros H2.
  assert (f(f n1) = f(f n2)) as lem.
  {
    rewrite -> H2. reflexivity.
  }
  rewrite <- H1 in lem.
  rewrite <- H1 in lem.
  exact lem.
Qed.

Theorem rev_injective : forall (l1 l2 : natlist),
  rev l1 = rev l2 -> l1 = l2.
Proof.
  (* assert the previous theorem, but for natlist *)
  assert (forall (f : natlist -> natlist),
    (forall n : natlist, n = f (f n)) -> (forall n1 n2 : natlist, f n1 = f n2 -> n1 = n2))
  as involution_injective_natlist.
  {
    (* copy and paste the previous proof here. *)
    intros f H1.
    intros n1 n2.
    intros H2.
    assert (f(f n1) = f(f n2)) as lem.
    {
      rewrite -> H2. reflexivity.
    }
    rewrite <- H1 in lem.
    rewrite <- H1 in lem.
    exact lem.
  }
  apply involution_injective_natlist.
  intros n. rewrite -> rev_involutive.
  reflexivity.
Qed.


