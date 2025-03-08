From LF.basics Require Import numbers.

Theorem silly_ex : forall p,
  (forall n, even n = true -> even (S n) = false) ->
  (forall n, even n = false -> odd n = true) ->
  even p = true ->
  odd (S p) = true.
Proof.
  intros p term1 term2 term3.
  apply term2.
  apply term1.
  apply term3.
Qed.

From LF.poly Require Import defns.
From LF.poly Require Import poly_list_exer.

Theorem rev_exercise1 : forall (l l' : list nat),
  l = rev l' ->
  l' = rev l.
Proof.
  intros l l'.
  intros term1.
  rewrite -> term1.
  symmetry.
  apply rev_involutive.
Qed.

(** Difference between rewrite and apply:
  1. rewrite works with equalities, by substituting one with something equal to
   it.
  2. apply can work with any term whose conclusion has the same type as the
   current goal or a hypothesis.
  3. If we have a situation where term is a = b and goal is also a = b, then
   both can be applied.
 *)


Theorem trans_eq : forall (X:Type) (n m o : X),
  n = m -> m = o -> n = o.
Proof.
  intros X n m o eq1 eq2. rewrite -> eq1. rewrite -> eq2.
  reflexivity. Qed.

Example trans_eq_exercise : forall (n m o p : nat),
  m = (minustwo o) ->
  (n + p) = m ->
  (n + p) = (minustwo o).
Proof.
  intros n m o p eq1 eq2.
  apply trans_eq with (m:=m).
  { apply eq2. }
  { apply eq1. }
Qed.
