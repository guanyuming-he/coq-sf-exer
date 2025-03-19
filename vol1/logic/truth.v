From LF.poly Require Import defns.

Definition disc_fn (n: nat) : Prop :=
  match n with
  | O => True
  | S _ => False
  end.

Theorem disc_example : forall n, ~ (O = S n).
Proof.
  intros n contra.
  assert (H : disc_fn O). { simpl. apply I. }
  rewrite contra in H. simpl in H. apply H.
Qed.

Definition disc_fn_list {X : Type} (l : list X) : Prop :=
  match l with
  | nil => True 
  | cons _ _ => False
  end.

Theorem nil_is_not_cons : forall X (x : X) (xs : list X), ~ (nil = x :: xs).
Proof.
  intros X x xs.
  unfold not.
  intros H.
  assert (truth : disc_fn_list (@nil X)). { simpl. apply I. }
  rewrite H in truth.
  simpl in truth. apply truth.
Qed.
