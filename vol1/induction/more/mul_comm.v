Require Import LF.Basics.
Require Import LF.basic_induction.

Theorem add_shuffle3 : forall n m p : nat,
  n + (m + p) = m + (n + p).
Proof.
  intros n m p.
  rewrite -> add_assoc.
  rewrite -> add_assoc.
  assert (H: n+m = m+n).
    { rewrite -> add_comm. reflexivity. }
  rewrite -> H.
  reflexivity.
Qed.

Theorem mul_comm : forall m n : nat,
  m * n = n * m.
Proof.
  intros m.
  induction m as [| m' IHm' ].
  - intros n. rewrite -> mul_0_r. reflexivity.
  - simpl. 
    assert (forall n, n * S m' = n + (n * m')) as H.
    { induction n as [| n' IHn'].
      - simpl. reflexivity.
      - simpl. rewrite -> IHn'. 
        rewrite -> add_shuffle3. reflexivity. 
    }
    intros n.
    rewrite -> H.
    rewrite -> IHm'.
    reflexivity.
Qed.
