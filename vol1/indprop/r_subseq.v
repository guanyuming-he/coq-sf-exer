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
      (* with this we are able to expand l1 with l2.
         Note that in general we can't expand l1 only.
         we could write something like
         subseq l1 l2 /\ In n l2 -> subseq (n::l1) l2,
         but that will confuse induction and it won't generate 
         an inductive hypothesis,
         unless I later figured out we could put In n l2
         as one of the parameters.
         But I haven't tried that way.
         *)
  | ss_cons_l1l2 (n : nat) (l1 l2 : list nat) : 
      subseq l1 l2 -> subseq (n::l1) (n::l2) 
      (* with this we are able to expand l2 only *)
  | ss_cons_l2 (n : nat) (l1 l2 : list nat) :
      subseq l1 l2 -> subseq l1 (n::l2).

(* My own lemma. c.f. subseq_app *)
Lemma subseq_app_l : forall (l1 l2 l3 : list nat),
  subseq l1 l2 -> subseq l1 (l3 ++ l2).
Proof.
  intros l1 l2 l3.
  generalize dependent l2.
  generalize dependent l1.
  induction l3.
  - intros l1 l2 H. simpl. apply H.
  - intros l1 l2 H.
    simpl.
    apply IHl3 in H.
    apply (ss_cons_l2 _ _ _ H).
Qed.


Theorem subseq_refl : forall (l : list nat), subseq l l.
Proof.
  intros l. induction l.
  - apply ss_empty.
  - apply ss_cons_l1l2.
    apply IHl.
Qed.


Theorem subseq_app : forall (l1 l2 l3 : list nat),
  subseq l1 l2 ->
  subseq l1 (l2 ++ l3).
Proof.
  intros l1 l2 l3 H.
  induction H.
  - apply ss_empty.
  - simpl. apply (ss_cons_l1l2 _ _ _ IHsubseq).
  - simpl. apply (ss_cons_l2 _ _ _ IHsubseq).
Qed.
  

Theorem subseq_trans : forall (l1 l2 l3 : list nat),
  subseq l1 l2 ->
  subseq l2 l3 ->
  subseq l1 l3.
Proof.
  (* How I come to this choice of inducting on H2 and generalize only on l1?
     I know it looked quite arbitrary at first glance.
    1. generally I can't just induct on a list, but that I have to induct on
    subseq. That is, I either induct on H1 or H2.
    2. I tried induction on H1. For that, I cannot generalize l1 or l2 since they are in it,
    so I can only generalize l3, but I was stuck that way.
    3. Hence I tried inducting on H2, for which I can only generalize l1.
    And boom it worked. Hence it's my choice *)
  intros l1 l2 l3 H1 H2.
  generalize dependent l1.
  induction H2.
  - intros l3 H.
    destruct l3.
    + apply ss_empty.
    + inversion H. (* non-sense *)
  - intros l3 H.
    inversion H.
    + apply ss_empty.
    + apply IHsubseq in H3.
      apply ss_cons_l1l2. apply H3.
    + apply IHsubseq in H3. apply ss_cons_l2.
      apply H3.
  - intros l3 H.
    apply IHsubseq in H. apply ss_cons_l2.
    apply H.
Qed.
    
