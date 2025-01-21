Require Import LF.Basics.
Require Import LF.basic_induction.

Fixpoint double (n:nat) := 
  match n with 
  | 0 => 0
  | S n' => S (S (double n'))
  end.

Lemma double_plus : forall n, double n = n+n.
Proof.
  intros n.
  induction n as [| n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite -> IHn'. rewrite <- plus_n_Sm. reflexivity.
Qed.
