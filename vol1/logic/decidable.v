(* For even *)
From LF.basics Require Import numbers.
(* For double *)
From LF.induction Require Import double_plus.


Lemma even_double : forall k, even (double k) = true.
Proof.
  intros k. induction k as [|k' IHk'].
  - reflexivity.
  - simpl. apply IHk'.
Qed.

(* For even_S *)
From LF.induction Require Import even_S.

Lemma even_double_conv : forall n, exists k,
  n = if even n then double k else S (double k).
Proof.
  intros n. induction n.
  - exists 0. reflexivity.
  - destruct (even n) eqn:HEn.
    + rewrite -> even_S. rewrite -> HEn. simpl.
      destruct IHn as [k]. exists k.
      rewrite -> H. reflexivity.
    + rewrite -> even_S. rewrite -> HEn. simpl.
      destruct IHn as [k]. exists (S k).
      rewrite H. reflexivity.
Qed.

(* For Even *)
From LF.logic Require Import exist.
Theorem even_bool_prop : forall n,
  even n = true <-> Even n.
Proof.
  intros n. split.
  - intros H. destruct (even_double_conv n) as [k Hk].
    rewrite Hk. rewrite H. exists k. reflexivity.
  - intros [k Hk]. rewrite Hk. apply even_double.
Qed.

(* For eqb_refl *)
From LF.induction Require Import eqb_refl.
(* For eqb_true *)
From LF.more_tac Require Import induction.

Theorem eqb_eq : forall n1 n2 : nat,
  n1 =? n2 = true <-> n1 = n2.
Proof.
  intros n1 n2. split.
  - apply eqb_true.
  - intros H. rewrite H. rewrite eqb_refl. reflexivity.
Qed.

(* Make <-> setoids *)
From Coq Require Import Setoids.Setoid.

Lemma plus_eqb_example : forall n m p : nat,
  n =? m = true -> n + p =? m + p = true.
Proof.
  (* WORKED IN CLASS *)
  intros n m p H.
  rewrite eqb_eq in H.
  rewrite H.
  rewrite eqb_eq.
  reflexivity.
Qed.

Theorem andb_true_iff : forall b1 b2:bool,
  b1 && b2 = true <-> b1 = true /\ b2 = true.
Proof.
  intros b1 b2.
  split.
  - destruct b1, b2.
    + split. { reflexivity. } { reflexivity. }
    + discriminate.
    + discriminate.
    + discriminate.
  - destruct b1, b2.
    + reflexivity.
    + intros [H1 H2]. discriminate.
    + intros [H1 H2]. discriminate.
    + intros [H1 H2]. discriminate.
Qed.

Theorem orb_true_iff : forall b1 b2,
  b1 || b2 = true <-> b1 = true \/ b2 = true.
Proof.
  intros b1 b2.
  split.
  - destruct b1, b2.
    + left. reflexivity.
    + left. reflexivity.
    + right. reflexivity.
    + discriminate.
  - destruct b1, b2.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + intros [H1 | H2]. 
      { discriminate. } { discriminate. }
Qed.

Theorem eqb_neq : forall x y : nat,
  x =? y = false <-> x <> y.
Proof.
  intros x y.
  split.
  - unfold not. rewrite <- eqb_eq.
    intros H. rewrite -> H.
    discriminate.
  - unfold not. destruct (x =? y) eqn:He.
    + intros H. rewrite eqb_eq in He. apply H in He.
      contradiction.
    + reflexivity.
Qed.

(* For list X *)
From LF.poly Require Import defns.

Fixpoint eqb_list {A : Type} (eqb : A -> A -> bool)
  (l1 l2 : list A) : bool
  :=
  match l1 with
  | nil => 
      match l2 with
      | nil => true
      | _ :: _ => false
      end
  | h1 :: t1 => 
      match l2 with
      | nil => false 
      | h2 :: t2 => eqb h1 h2 && eqb_list eqb t1 t2
        end
  end.

Theorem eqb_list_true_iff :
  forall A (eqb : A -> A -> bool),
    (forall a1 a2, eqb a1 a2 = true <-> a1 = a2) ->
    forall l1 l2, eqb_list eqb l1 l2 = true <-> l1 = l2.
Proof.
  intros A eqb H.
  intros l1. induction l1 as [| x1 l1].
  - split.
    + destruct l2.
      { reflexivity. }
      { discriminate. }
    + intros H1. rewrite <- H1. reflexivity.
  - split.
    + destruct l2 as [|x2 l2].
      { discriminate. }
      { 
        intros H1. simpl in H1.
        rewrite -> andb_true_iff in H1.
        rewrite H in H1. rewrite IHl1 in H1.
        destruct H1 as [ H2 H3 ].
        rewrite H2. rewrite H3.
        reflexivity.
      }
    + destruct l2 as [|x2 l2].
      { discriminate. }
      { 
        intros H1. injection H1.
        intros H2 H3.
        simpl. rewrite -> andb_true_iff.
        rewrite -> H. rewrite -> IHl1.
        split.
        { apply H3. } { apply H2. }
      }
Qed.

(* For forallb *)
From LF.more_tac Require Import additional.
(* For All *)
From LF.logic Require Import prog_props.

Theorem forallb_true_iff : forall X test (l : list X),
  forallb test l = true <-> All (fun x => test x = true) l.
Proof.
  intros X test l.
  induction l.
  - split.
    + reflexivity.
    + reflexivity.
  - split.
    + destruct (test x) eqn:Ex.
      { 
        intros H. simpl in H. rewrite -> Ex in H. 
        simpl. 
        split.
        { apply Ex. }
        { apply IHl in H. apply H. }
      }
      { intros H. simpl in H. rewrite -> Ex in H. discriminate. }
    + intros H. simpl in H. destruct H as [H1 H2].
      simpl. rewrite -> H1.
      apply IHl in H2. apply H2.
Qed.
