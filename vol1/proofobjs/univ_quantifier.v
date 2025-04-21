From LF.indprop Require Import defns.

Theorem ev_plus4 : forall n, ev n -> ev (4 + n).
Proof.
  intros n H. simpl.
  apply ev_SS.
  apply ev_SS.
  apply H.
Qed.

Check ev_plus4 : forall n (_ : ev n), ev (4 + n).

Definition ev_plus4' : forall n, ev n -> ev (4 + n) :=
  fun (n : nat) => fun (H : ev n) =>
    ev_SS (S (S n)) (ev_SS n H).

Definition ev_plus4'' (n : nat) (H : ev n)
                    : ev (4 + n) :=
  ev_SS (S (S n)) (ev_SS n H).
Check ev_plus4'' : forall n : nat, ev n -> ev (4 + n).

Definition ev_plus2 : Prop :=
  forall n, forall (E : ev n), ev (n + 2).

Definition ev_plus2' : Prop :=
  forall n, forall (_ : ev n), ev (n + 2).

Definition ev_plus2'' : Prop :=
  forall n, ev n -> ev (n + 2).

