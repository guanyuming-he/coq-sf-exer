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
  intros b c.
  induction b, c.
  - simpl. reflexivity.
  - simpl. reflexivity.
  - simpl. intros n0. rewrite -> add_0_r. reflexivity.
  - simpl. 
    intros n1. 

    assert (forall p q: nat, (p =? q = true) -> p = q) as lem1.
    { 
      intros p.
      induction p.
      - intros q. destruct q.
        + reflexivity.
        + simpl. discriminate.
      - simpl. intros q. destruct q.
        + discriminate.
        + intros H. apply IHp in H. rewrite -> H. reflexivity.
    }
    destruct (n =? n0) eqn:H1.
    { destruct (n =? n1) eqn:H2.
      - apply lem1 in H1. apply lem1 in H2.
        rewrite <- H1. rewrite <- H2.
        rewrite -> eqb_refl.
        assert 
        ( count n0 (sum b (n0 :: c)) = count n0 b + S (count n0 c)) as temp.
        {
          rewrite -> IHb. simpl. rewrite -> eqb_refl. reflexivity.
        }
        rewrite -> H1.
        simpl. rewrite <- temp. simpl.

        
