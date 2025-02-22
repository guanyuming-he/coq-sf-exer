From LF.poly Require Import defns.

Theorem app_nil_r : forall (X:Type), forall l:list X,
  l ++ [] = l.
Proof.
  intros X.
  intros l.
  induction l.
  - simpl. reflexivity.
  - simpl. rewrite -> IHl. reflexivity.
Qed.

Theorem app_assoc : forall A (l m n:list A),
  l ++ m ++ n = (l ++ m) ++ n.
Proof.
  intros A.
  intros l.
  induction l.
  - simpl. reflexivity.
  - simpl. intros m n. rewrite -> IHl. reflexivity.
Qed.

Lemma app_length : forall (X:Type) (l1 l2 : list X),
  length (l1 ++ l2) = length l1 + length l2.
Proof.
  intros X.
  intros l1.
  induction l1.
  - simpl. reflexivity.
  - simpl. intros l2. rewrite -> IHl1. reflexivity.
Qed.

Theorem rev_app_distr: forall X (l1 l2 : list X),
  rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
  intros X.
  intros l1.
  induction l1.
  - simpl. intros l2. rewrite -> app_nil_r. reflexivity.
  - simpl. intros l2. rewrite -> IHl1. 
    rewrite -> app_assoc. reflexivity.
Qed.

Theorem rev_involutive : forall X : Type, forall l : list X,
  rev (rev l) = l.
Proof.
  intros X.
  intros l.
  induction l.
  - simpl. reflexivity.
  - simpl. rewrite -> rev_app_distr. rewrite -> IHl.
    simpl. reflexivity.
Qed.
