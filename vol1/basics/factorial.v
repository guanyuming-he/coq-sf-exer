Require Import numbers.

Fixpoint factorial (n:nat) : nat
  :=
  match n with
  | 0 => S 0
  | S n' => mul n (factorial n')
  end.

Example test_factorial1: (factorial 3) = 6.
Proof. simpl. reflexivity. Qed.
Example test_factorial2: (factorial 5) = (mult 10 12).
Proof. simpl. reflexivity. Qed.
