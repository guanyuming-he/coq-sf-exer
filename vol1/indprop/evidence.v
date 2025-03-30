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


Inductive ev' : nat -> Prop :=
  | ev'_0 : ev' 0
  | ev'_2 : ev' 2
  | ev'_sum n m (Hn : ev' n) (Hm : ev' m) : ev' (n + m).

Theorem ev'_ev : forall n, ev' n <-> ev n.
Proof.
  intros n.
  split.
  - intros E. induction E.
    + apply ev_0.
    + apply ev_SS. apply ev_0.
    + apply (ev_sum n m IHE1 IHE2).
  - intros E. induction E.
    + apply ev'_0.
    + assert (S (S n) = n + 2).
      { 
        assert (forall n, S n = n+1).
        { intros n0. rewrite -> add_comm.
          reflexivity. }
        rewrite -> H. rewrite -> H.
        rewrite <- add_assoc.
        reflexivity.
      }
      rewrite -> H.
      apply (ev'_sum n 2 IHE ev'_2).
Qed.

(* For list X*)
From LF.poly Require Import defns.
(* For In *)
From LF.logic Require Import prog_props.

Lemma Perm3_symm : forall (X : Type) (l1 l2 : list X),
  Perm3 l1 l2 -> Perm3 l2 l1.
Proof.
  intros X l1 l2 E.
  induction E as [a b c | a b c | l1 l2 l3 E12 IH12 E23 IH23].
  - apply perm3_swap12.
  - apply perm3_swap23.
  - apply (perm3_trans _ l2 _).
    + apply IH23.
    + apply IH12.
Qed.

Lemma Perm3_In : forall (X : Type) (x : X) (l1 l2 : list X),
    Perm3 l1 l2 -> In x l1 -> In x l2.
Proof.
  intros X x l1 l2.
  intros E1 E2.
  induction E1.
  - unfold In in E2.
    unfold In.
    destruct E2 as [H1 | [H2 | [H3 | H4] ] ].
    + right. left. apply H1.
    + left. apply H2.
    + right. right. left. apply H3.
    + destruct H4.
  - unfold In in E2.
    unfold In.
    destruct E2 as [H1 | [H2 | [H3 | H4] ] ].
    + left. apply H1.
    + right. right. left. apply H2.
    + right. left. apply H3.
    + destruct H4.
  - apply IHE1_1 in E2. apply IHE1_2 in E2.
    apply E2.
Qed.

Lemma Perm3_NotIn : forall (X : Type) (x : X) (l1 l2 : list X),
  Perm3 l1 l2 -> ~In x l1 -> ~In x l2.
Proof.
  intros X x l1 l2.    
  intros E1 E2.
  unfold not. unfold not in E2.
  induction E1.
  - unfold In in E2.
    unfold In.
    intros [H1 | [H2 | [H3|H4]]].
    + apply E2. right. left. apply H1.
    + apply E2. left. apply H2.
    + apply E2. right. right. left. apply H3.
    + destruct H4.
  - unfold In in E2.
    unfold In.
    intros [H1 | [H2 | [H3|H4]]].
    + apply E2. left. apply H1.
    + apply E2. right. right. left. apply H2.
    + apply E2. right. left. apply H3.
    + destruct H4.
  - apply IHE1_2. 
    apply (IHE1_1 E2).
Qed.

Example Perm3_example2 : ~Perm3 [1;2;3] [1;2;4].
Proof.
  unfold not.
  intros E.
  inversion E.
  assert (In 3 [1;2;3]).
  (* goal: show that 3 or 4 is in l2, and thus consequently
     in [1;2;4] or [1;2;3] *)
  { unfold In. right. right. left. reflexivity. }
  apply (Perm3_In nat 3 [1;2;3] l2 H) in H3.
  apply (Perm3_In nat 3 l2 [1;2;4] H0) in H3.
  unfold In in H3.
  destruct H3 as [F1|[F2|[F3|F4]]].
  - discriminate F1.
  - discriminate F2.
  - discriminate F3.
  - destruct F4.
Qed.








