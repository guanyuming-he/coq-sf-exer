Require Import booleans.
Require Import numbers.

Definition ltb (n m : nat) : booleans.bool
  :=
  if eqb n m then false
  else leb n m.

Example test_ltb1: (ltb 2 2) = false.
Proof. simpl. reflexivity. Qed.
Example test_ltb2: (ltb 2 4) = true.
Proof. simpl. reflexivity. Qed.
Example test_ltb3: (ltb 4 2) = false.
Proof. simpl. reflexivity. Qed.

