From LF.basics Require Import numbers.
From LF.poly Require Import defns.

Module R.

Inductive R : nat -> nat -> nat -> Prop :=
  | c1 : R 0 0 0
  | c2 m n o (H : R m n o ) : R (S m) n (S o)
  | c3 m n o (H : R m n o ) : R m (S n) (S o)
  | c4 m n o (H : R (S m) (S n) (S (S o))) : R m n o
  | c5 m n o (H : R m n o ) : R n m o.

(**
  1. Which of the following propositions are provable?
    - R 1 1 2 : yes, through c2 and c3 (order does not matter).
    - R 2 2 6 : no. 2 + 2 <> 6.
  2. No. c2 and c3 are symmetric about m and n.
  3. No, by changing how we apply c2 and c3, we can get to any R m n o such that
   m+n = o
 *)

(* for theorems about addition *)
From LF.induction Require Import basic_induction.

Definition fR : nat -> nat -> nat
  := plus.

(* My own lemma *)
Lemma R_n_times_c3 : forall n,
  R 0 n n.
Proof.
  intros n. induction n.
  - apply c1.
  - apply (c3 0 n n IHn).
Qed. 

Theorem R_equiv_fR : forall m n o, R m n o <-> fR m n = o.
Proof.
  intros m n o.
  split.
  - intros E. induction E.
    + reflexivity.
    + unfold fR. unfold fR in IHE.
      simpl. rewrite -> IHE. reflexivity.
    + unfold fR in IHE. unfold fR.
      simpl. rewrite -> add_comm. simpl. rewrite <- add_comm.
      rewrite -> IHE. reflexivity.
    + unfold fR. unfold fR in IHE.
      simpl. simpl in IHE. rewrite -> add_comm in IHE. simpl in IHE.
      rewrite <- add_comm in IHE. injection IHE.
      intros H. apply H.
    + unfold fR. unfold fR in IHE.
      rewrite -> add_comm. apply IHE.
  - generalize dependent n. generalize dependent o.
    induction m.
    + unfold fR. intros o n H. simpl in H.
      rewrite -> H. apply R_n_times_c3.
    + unfold fR. intros o n H.
      destruct o as [| o'].
      { discriminate. }
      { simpl in H. injection H as H.
        apply IHm in H.
        apply c2. apply H.
      }
Qed.

End R.

(* For In *)
From LF.logic Require Import prog_props.

Inductive subseq : list nat -> list nat -> Prop :=
  | ss_empty (l2 : list nat) : 
      subseq [] l2
      (* here we must take it one step at a time *)
  | ss_cons_l1 (n : nat) (l1 l2 : list nat) : 
      subseq l1 l2 /\ In n l2 -> subseq (n::l1) l2 
  | ss_app_l2 (l1 l2 l3 : list nat) :
      subseq l1 l2 \/ subseq l1 l3 -> subseq l1 (l2++l3).

Theorem subseq_refl : forall (l : list nat), subseq l l.
Proof.
  intros l. induction l.
  - apply ss_empty.
  - apply ss_cons_l1.
    split.
    + apply (ss_app_l2 l [x] l).
      right. apply IHl.
    + unfold In.
      left. reflexivity.
Qed.

Theorem subseq_app : forall (l1 l2 l3 : list nat),
  subseq l1 l2 ->
  subseq l1 (l2 ++ l3).
Proof.
  intros l1 l2 l3 H.
  apply ss_app_l2. left. apply H.
Qed.
  

Theorem subseq_trans : forall (l1 l2 l3 : list nat),
  subseq l1 l2 ->
  subseq l2 l3 ->
  subseq l1 l3.
Proof.
  intros l1 l2.
  generalize dependent l1.
  induction l2.
  - intros l1 l3 H1 H2.
    inversion H1.
    + apply ss_empty.
    + destruct H as [_ contra].
      unfold In in contra.
      destruct contra.
    + (* subseq l1 [] \/ subseq _ _ ->
         subseq l1 ([]++l3)
       *)
      apply ss_app_l2 with (l1 := l1) (l2 := []) (l3 := l3).
      left. apply H1.
  - 

