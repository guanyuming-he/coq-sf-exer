From LF.basics Require Import numbers.

Module Playground.

Inductive le : nat -> nat -> Prop :=
  | le_n (n : nat) : le n n
  | le_S (n m : nat) (H : le n m) : le n (S m).
Notation "n <= m" := (le n m).

Theorem test_le1 :
  le 3 3.
Proof.
  (* WORKED IN CLASS *)
  apply le_n. Qed.
Theorem test_le2 :
  le 3 6.
Proof.
  (* WORKED IN CLASS *)
  apply le_S. apply le_S. apply le_S. apply le_n. Qed.
Theorem test_le3 :
  (le 2 1) -> 2 + 2 = 5.
Proof.
  (* WORKED IN CLASS *)
  intros H. inversion H. inversion H2. Qed.


End Playground.

(* Use our own le *)
From LF.indprop Require Import defns.

Definition lt (n m : nat) := le (S n) m.
Notation "n < m" := (lt n m).
Definition ge (m n : nat) : Prop := le n m.
Notation "m >= n" := (ge m n).

(* for add_0_r *)
From LF.induction Require Import basic_induction.

(* 
   I modified the order of the following theorems
   so that some are easier to prove with others
*)
Theorem O_le_n : forall n,
  0 <= n.
Proof.
  intros n. induction n.
  - apply le_n.
  - apply (le_S 0 n IHn).
Qed.

Theorem le_plus_l : forall a b,
  a <= a + b.
Proof.
  intros a b. induction b.
  - simpl. rewrite -> add_0_r. apply le_n.
  - rewrite -> add_comm. simpl.
    rewrite <- add_comm.
    apply le_S with (n := a) (m := a + b).
    apply IHb.
Qed.

(* My added corollary *)
Corollary n_le_Sn : forall n,
  n <= S n.
Proof.
  intros n.
  assert (S n = n + 1).
  { rewrite add_comm. simpl. reflexivity. }
  rewrite -> H. apply le_plus_l.
Qed.

(* My added lemma. *)
Lemma Sn_le_m__n_le_m : forall n m,
  S n <= m -> n <= m.
Proof.
  intros n m E.
  remember (S n) as n'.
  induction E.
  - rewrite -> Heqn'. apply le_S. apply le_n.
  - apply (le_S n m (IHE Heqn')).
Qed.

(* Just for my next lemma *)
Lemma ne_Sn_n : forall n : nat,
  S n <> n.
Proof.
  intros n. unfold not. intros H. induction n.
  - discriminate.
  - injection H.
    apply IHn.
Qed.

(* My added lemma *)
Lemma not_le_Sn_n : forall n : nat,
  ~(S n <= n).
Proof.
  intros n. induction n.
  - unfold not. intros H. inversion H.
  - unfold not. intros H. inversion H.
    + apply ne_Sn_n in H2. apply H2. 
    + apply Sn_le_m__n_le_m in H2.
      apply IHn in H2. apply H2.
Qed.


Theorem Sn_le_Sm__n_le_m : forall n m,
  S n <= S m -> n <= m.
Proof.
  intros n m E.
  inversion E.
  - apply le_n.
  - apply (Sn_le_m__n_le_m n m H1).
Qed.

Lemma le_trans : forall m n o, m <= n -> n <= o -> m <= o.
Proof.
  intros m n o E.
  induction E.
  - intros H. apply H.
  - intros H. apply Sn_le_m__n_le_m in H.
    apply IHE in H. apply H.
Qed.

Theorem n_le_m__Sn_le_Sm : forall n m,
  n <= m -> S n <= S m.
Proof.
  intros n m E.
  induction E.
  - apply le_n.
  - apply le_S. apply IHE.
Qed.

Theorem plus_le : forall n1 n2 m,
  n1 + n2 <= m ->
  n1 <= m /\ n2 <= m.
Proof.
  intros n1 n2 m H.
  split.
  - (* 
       le_plus_l n1 n2 gives n1 <= n1+n2
       use that together with n1+n2<=m with trans,
       to have n1 <= m.
    *)
  apply (
    le_trans n1 (n1+n2) m 
    (le_plus_l n1 n2)
    H
  ).  
  - (* similar process to the prev one. *)
    rewrite -> add_comm in H.
    apply (
      le_trans n2 (n2+n1) m
      (le_plus_l n2 n1)
      H
    ).
Qed.

Theorem plus_le_cases : forall n m p q,
  n + m <= p + q -> n <= p \/ m <= q.
Proof.
  intros n. induction n.
  - intros m p q _.
    left. apply O_le_n.
  - intros m p q H.
    simpl in H.
    assert (S(n+m) = (S n) + m) as H1.
    { reflexivity. }
    destruct p as [| p'] eqn:Ep'.
    + right. simpl in H. 
      rewrite -> H1 in H.
      rewrite -> add_comm in H.
      apply (
        le_trans m (m+S n) q 
        (le_plus_l m (S n)) (* m <= Sn *)
        H
     ).
    + simpl in H. 
      rewrite -> plus_n_Sm in H.
      rewrite -> plus_n_Sm in H.
      apply IHn in H.
      destruct H.
      {
        apply n_le_m__Sn_le_Sm in H.
        left. apply H.
      }
      {
        apply Sn_le_Sm__n_le_m in H.
        right. apply H.
      }
Qed.


Theorem plus_le_compat_l : forall n m p,
  n <= m ->
  p + n <= p + m.
Proof.
  intros n m p.
  generalize dependent n.
  generalize dependent m.
  induction p.
  - intros m n H.
    simpl. apply H.
  - intros m n H.
    apply IHp in H.
    simpl. apply (n_le_m__Sn_le_Sm (p+n) (p+m) H).
Qed.

Theorem plus_le_compat_r : forall n m p,
  n <= m ->
  n + p <= m + p.
Proof.
  intros n m p H.
  apply plus_le_compat_l with (p := p) in H.
  rewrite -> add_comm with (n := p) (m := n) in H.
  rewrite -> add_comm with (n := p) (m := m) in H.
  apply H.
Qed.

(* My own theorem, c.f. plus_le_cases *)
Theorem le_cases_plus : forall n m p q,
  n <= p -> m <= q -> n+m <= p+q.
Proof.
  intros n m p q H1 H2.
  apply (plus_le_compat_r n p m) in H1.
  apply (plus_le_compat_l m q p) in H2.
  apply (le_trans (n+m) (p+m) (p+q) H1 H2).
Qed.

Theorem le_plus_trans : forall n m p,
  n <= m ->
  n <= m + p.
Proof.
  intros n m p H.
  apply (
    le_trans n m (m+p)
    H
    (le_plus_l m p) (* m <= m+p *)
  ).
Qed.

Theorem lt_ge_cases : forall n m,
  n < m \/ n >= m.
Proof.
  intros n.
  induction n.
  - destruct m.
    + right. unfold ge. apply (le_n 0).
    + left.  unfold lt. 
      apply (
        n_le_m__Sn_le_Sm 0 m
        (O_le_n m) (* 0 <= m *)
      ).
  - intros m.
    destruct m as [| m'].
    + right. unfold ge. apply O_le_n.
    + destruct (IHn m').
      { left. apply n_le_m__Sn_le_Sm. apply H. }
      { right. unfold ge. unfold ge in H. 
        apply n_le_m__Sn_le_Sm. apply H.
      }
Qed.

Theorem n_lt_m__n_le_m : forall n m,
  n < m ->
  n <= m.
Proof.
  intros n m H.
  unfold lt in H.
  apply Sn_le_m__n_le_m. apply H.
Qed.
  

Theorem plus_lt : forall n1 n2 m,
  n1 + n2 < m ->
  n1 < m /\ n2 < m.
Proof.
  intros n1 n2 m.
  unfold lt.
  intros H.
  split.
  - rewrite -> plus_Sn_m in H.
    apply (
    le_trans _ _ _
    (le_plus_l (S n1) n2)
    H
    ).
  - rewrite -> plus_n_Sm in H.
    rewrite -> add_comm in H.
    apply (
      le_trans _ _ _
      (le_plus_l (S n2) n1)
      H
    ).
Qed.

Theorem leb_complete : forall n m,
  n <=? m = true -> n <= m.
Proof.
  intros n. induction n.
  - intros m _. apply O_le_n.
  - intros m H.
    simpl in H.
    destruct m
    + discriminate H.
    + discriminate H.
    + apply IHn in H. apply n_le_m__Sn_le_Sm in H.
      apply H.
Qed.

(* For leb_refl *)
From LF.induction Require Import more.more_exercises.

(* soundness *)
Theorem leb_correct : forall n m,
  n <= m ->
  n <=? m = true.
Proof.
  intros n. induction n.
  - intros m _. reflexivity.
  - intros m H.
    inversion H.
    + apply leb_refl.
    + apply le_S in H0. apply Sn_le_Sm__n_le_m in H0.
      apply IHn in H0.
      simpl.
      apply H0.
Qed.

Theorem leb_iff : forall n m,
  n <=? m = true <-> n <= m.
Proof.
  intros n m. split.
  - apply leb_complete.
  - apply leb_correct. 
Qed.

(* For rewriting <-> *)
From Coq Require Import Setoids.Setoid.

Theorem leb_true_trans : forall n m o,
  n <=? m = true -> m <=? o = true -> n <=? o = true.
Proof.
  intros n m o.
  rewrite -> leb_iff.
  rewrite -> leb_iff.
  rewrite -> leb_iff.
  apply le_trans.
Qed.

