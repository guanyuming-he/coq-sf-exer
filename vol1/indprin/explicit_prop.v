From LF.induction Require Import basic_induction.

Definition P_npm_comm (n:nat) : Prop :=
  forall m : nat, n + m = m + n.

Theorem add_comm' : forall n : nat,
  P_npm_comm n.
Proof.
  apply nat_ind.
  - unfold P_npm_comm. simpl. intros m. rewrite -> add_0_r. reflexivity.
  - unfold P_npm_comm. intros n.
    intros H. intros m. simpl. rewrite -> H. rewrite -> plus_n_Sm. reflexivity.
Qed.

Definition P_nmp_add_assoc (n : nat) : Prop :=
  forall (m p : nat), n + (m + p) = (n + m) + p.

Theorem add_assoc' : forall n : nat,
  P_nmp_add_assoc n.
Proof.
  apply nat_ind.
  - unfold P_nmp_add_assoc. simpl. reflexivity.
  - unfold P_nmp_add_assoc. intros n H.
    simpl. intros m p. rewrite -> H.
    reflexivity.
Qed.
