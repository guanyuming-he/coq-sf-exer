From LF Require Import basics.numbers.

Theorem plus_id_exercise : forall n m o : nat,
  n = m -> m = o -> n + m =  m + o.
Proof.
  intros n m o.
  intros H_1.
  intros H_2.
  rewrite -> H_1.
  rewrite -> H_2.
  reflexivity.
Qed.

Theorem mult_n_1 : forall p : nat,
  p * 1 = p.
Proof.
  intros p.
  rewrite <- mult_n_Sm.
  rewrite <- mult_n_O.
  reflexivity.
Qed.
  
Theorem andb_true_elim2 : forall b c : bool,
  andb b c = true -> c = true.
Proof.
  intros b c.
  destruct b eqn:Eb.
    - destruct c eqn:Ec.
      + reflexivity.
      + simpl. intros H. rewrite <- H. reflexivity.
    - destruct c eqn:Ec.
      + simpl. intros H. rewrite <- H. reflexivity.
      + simpl. intros H. rewrite <- H. reflexivity.
Qed.

Theorem zero_nbeq_plus_1 : forall n : nat,
  0 =? (n + 1) = false.
Proof.
  intros [ | n'].
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

