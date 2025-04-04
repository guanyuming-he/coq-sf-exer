From LF.poly Require Import defns.

Definition hd_error {X : Type} (l : list X) : option X
  :=
  match l with
  | nil => None
  | h :: t => Some h
  end.


Example test_hd_error1 : hd_error [1;2] = Some 1.
Proof. reflexivity. Qed.
Example test_hd_error2 : hd_error [[1];[2]] = Some [1].
Proof. reflexivity. Qed.
