From LF Require Import basics.booleans.

Definition andb3 (b1:bool) (b2:bool) (b3:bool) : bool
  :=
  if andb (andb b1 b2) b3 then true
  else false.
Example test_andb31: (andb3 true true true) = true.
Proof. simpl. reflexivity. Qed.
Example test_andb32: (andb3 false true true) = false.
Proof. simpl. reflexivity. Qed.
Example test_andb33: (andb3 true false true) = false.
Proof. simpl. reflexivity. Qed.
Example test_andb34: (andb3 true true false) = false.
Proof. simpl. reflexivity. Qed.
