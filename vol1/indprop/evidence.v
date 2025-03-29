From LF.indprop Require Import defns.

Theorem ev_inversion : forall (n : nat),
  ev n ->
  (n = 0) \/ (exists n', n = S (S n') /\ ev n').
Proof.
  intros n E. destruct E as [ | n' E'] eqn:EE.
  - (* E = ev_0 : ev 0 *)
    left. reflexivity.
  - (* E = ev_SS n' E' : ev (S (S n')) *)
    right. exists n'. split. reflexivity. apply E'.
Qed.

Theorem le_inversion : forall (n m : nat),
  le n m ->
  (n = m) \/ (exists m', m = S m' /\ le n m').
Proof.
  intros n m.
  intros [ a | a b ].
  - left. reflexivity.
  - right. exists b. split.
    + reflexivity.
    + apply H.
Qed.

Theorem evSS_ev' : forall n,
  ev (S (S n)) -> ev n.
Proof.
  intros n E. inversion E as [| n' E' Hnn'].
  (* We are in the E = ev_SS n' E' case now. *)
  apply E'.
Qed.

Theorem SSSSev__even : forall n,
  ev (S (S (S (S n)))) -> ev n.
Proof.
  intros n E.
  inversion E.
  inversion H0.
  apply H2.
Qed.

Theorem ev5_nonsense :
  ev 5 -> 2 + 2 = 9.
Proof.
  intros E.
  inversion E.
  inversion H0.
  inversion H2.
Qed.

(* For Even *)
From LF.logic Require Import exist.

Lemma ev_Even : forall n,
  ev n -> Even n.
Proof.
  unfold Even. intros n E.
  induction E as [|n' E' IH].
  - (* E = ev_0 *)
    exists 0. reflexivity.
  - (* E = ev_SS n' E',  with IH : Even n' *)
    destruct IH as [k Hk]. rewrite Hk.
    exists (S k). simpl. reflexivity.
Qed.


Theorem ev_Even_iff : forall n,
  ev n <-> Even n.
Proof.
  intros n. split.
  - (* -> *) apply ev_Even.
  - (* <- *) unfold Even. intros [k Hk]. rewrite Hk. apply ev_double.
Qed.


Theorem ev_sum : forall n m, ev n -> ev m -> ev (n + m).
Proof.
  intros n m E.
  induction E.
  - intros H. simpl. apply H.
  - intros H. apply IHE in H.
    simpl. apply ev_SS. apply H.
Qed.

Theorem ev_ev__ev : forall n m,
  ev (n+m) -> ev n -> ev m.
  (* Hint: There are two pieces of evidence you could attempt to induct upon
      here. If one doesn't work, try the other. *)
Proof.
  intros n m E1 E2.
  induction E2.
  - simpl in E1. apply E1.
  - simpl in E1. inversion E1.
    apply IHE2 in H0. apply H0.
Qed.

(* For add_comm *)
From LF.induction Require Import basic_induction.
(* For double *)
From LF.induction Require Import double_plus.
(* For rewrite at *)
From Coq Require Import Setoids.Setoid.

Theorem ev_plus_plus : forall n m p,
  ev (n+m) -> ev (n+p) -> ev (m+p).
Proof.
  (* n+m+n+p = 2n+m+p, where 2n is guaranteed to be even. 
     Thus, apply ev_sum for the sum and ev_ev__ev for 
     from 2n+m+p to m+p
   *)
  intros n m p E1 E2.
  apply ev_ev__ev with (n := double n) (m:=m+p).
  - rewrite -> double_plus.
    (* Goal: transform n+n+(m+p) to (n+m) + (n+p). *)
    assert (n+n+(m+p) = (n+m)+(n+p)) as H.
    {
      rewrite -> add_assoc with (n := n+n) (m := m) (p := p).
      rewrite <- add_assoc with (n := n) (m := n) (p := m).
      rewrite -> add_comm with (n := n) (m := m) at 1.
      rewrite -> add_assoc with (n := n) (m := m) (p := n).
      rewrite <- add_assoc with (n := n+m) (m := n) (p := p).
      reflexivity.
    }
    rewrite -> H.
    apply ev_sum.
    + apply E1.
    + apply E2.
  - apply ev_double.
Qed.


