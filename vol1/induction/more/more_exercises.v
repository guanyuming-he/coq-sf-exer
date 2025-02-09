From LF Require Import induction.basic_induction.

Theorem leb_refl : forall n:nat,
  (n <=? n) = true.
Proof.
  intros n.
  induction n as [| n' IHn'].
  - reflexivity.
  - simpl. rewrite -> IHn'. reflexivity.
Qed.

Theorem zero_neqb_S : forall n:nat,
  0 =? (S n) = false.
Proof.
  simpl. reflexivity.
Qed.

Theorem andb_false_r : forall b : bool,
  andb b false = false.
Proof.
  intros b. destruct b.
  - reflexivity.
  - reflexivity.
Qed.

Theorem S_neqb_0 : forall n:nat,
  (S n) =? 0 = false.
Proof.
  simpl. reflexivity.
Qed.

Theorem mult_1_l : forall n:nat, 1 * n = n.
Proof.
  simpl. intros n. rewrite -> add_0_r. reflexivity.
Qed.

Theorem all3_spec : forall b c : bool,
  orb
    (andb b c)
    (orb (negb b)
         (negb c))
  = true.
Proof.
  intros b c.
  destruct (b && c) eqn:H.
  - simpl. reflexivity.
  - simpl. destruct b. 
    { simpl. destruct c. 
      { simpl in H. simpl. rewrite -> H. reflexivity. }
      { simpl. reflexivity. }
    }
    { simpl. reflexivity. }
Qed.

Theorem mult_plus_distr_r : forall n m p : nat,
  (n + m) * p = (n * p) + (m * p).
Proof.
  intros n.
  induction n as [| n' IHn'].
  - simpl. reflexivity.
  - simpl.  intros m p. rewrite -> IHn'. rewrite -> add_assoc. reflexivity.
Qed.

Theorem mult_assoc : forall n m p : nat,
  n * (m * p) = (n * m) * p.
Proof.
  intros n.
  induction n as [| n' IHn'].
  - simpl. reflexivity.
  - simpl. intros m p. rewrite -> IHn'. rewrite -> mult_plus_distr_r. reflexivity.
Qed.
