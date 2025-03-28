From LF.basics Require Import numbers.

Inductive le : nat -> nat -> Prop :=
  | le_n (n : nat) : le n n
  | le_S (n m : nat) : le n m -> le n (S m).
Notation "n <= m" := (le n m) (at level 70).

Example le_3_5 : 3 <= 5.
Proof.
  apply le_S. apply le_S. apply le_n.
Qed.

Inductive clos_trans {X: Type} (R: X->X->Prop) : X->X->Prop :=
  | t_step (x y : X) :
      R x y ->
      clos_trans R x y
  | t_trans (x y z : X) :
      clos_trans R x y ->
      clos_trans R y z ->
      clos_trans R x z.

Inductive clos_refl_trans {X: Type} (R: X->X->Prop) : X->X->Prop :=
  | rt_step (x y : X) :
      R x y ->
      clos_refl_trans R x y
  | rt_refl (x : X) :
      clos_refl_trans R x x
  | rt_trans (x y z : X) :
      clos_refl_trans R x y ->
      clos_refl_trans R y z ->
      clos_refl_trans R x z.

Inductive clos_refl_trans_sym {X : Type} (R: X->X->Prop):
  X->X->Prop :=
  | rts_step (x y : X) :
      R x y ->
      clos_refl_trans_sym R x y
  | rts_refl (x : X):
      clos_refl_trans_sym R x x
  | rts_sym (x y : X) :
      clos_refl_trans_sym R x y ->
      clos_refl_trans_sym R y x
  | rts_trans (x y z : X) :
      clos_refl_trans_sym R x y ->
      clos_refl_trans_sym R y z ->
      clos_refl_trans_sym R x z.

(* For list X*)
From LF.poly Require Import defns.

Inductive Perm3 {X : Type} : list X -> list X -> Prop :=
  | perm3_swap12 (a b c : X) :
      Perm3 [a;b;c] [b;a;c]
  | perm3_swap23 (a b c : X) :
      Perm3 [a;b;c] [a;c;b]
  | perm3_trans (l1 l2 l3 : list X) :
      Perm3 l1 l2 -> Perm3 l2 l3 -> Perm3 l1 l3.

(* perm: is Perm3 [1;2;3] [1;2;3] True?
  Answer: Yes. see Perm3_refl. *)

Inductive ev : nat -> Prop :=
  | ev_0 : ev 0
  | ev_SS (n : nat) (H : ev n) : ev (S (S n)).

(* For double *)
From LF.induction Require Import double_plus.

Theorem ev_double : forall n,
  ev (double n).
Proof.
  intros n.
  induction n.
  - simpl. apply ev_0.
  - simpl. apply ev_SS. apply IHn.
Qed.

Lemma Perm3_rev : Perm3 [1;2;3] [3;2;1].
Proof.
  apply perm3_trans with (l2:=[2;3;1]).
  - apply perm3_trans with (l2:=[2;1;3]).
    + apply perm3_swap12.
    + apply perm3_swap23.
  - apply perm3_swap12.
Qed.

Lemma Perm3_ex1 : Perm3 [1;2;3] [2;3;1].
Proof.
  apply perm3_trans with (l2 := [2;1;3]).
  - apply perm3_swap12.
  - apply perm3_swap23.
Qed.

Lemma Perm3_refl : forall (X: Type) (x y z : X),
  Perm3 [x;y;z] [x;y;z].
Proof.
  intros X x y z.
  apply perm3_trans with (l2 := [y;x;z]).
  - apply perm3_swap12.
  - apply perm3_swap12.
Qed.
