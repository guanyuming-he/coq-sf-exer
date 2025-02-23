From LF.poly Require Import defns.
From LF.basics Require Import numbers.


(* One example: count the number of trues *)
Example fold_types_different:
  fold (fun (b : bool) (n : nat) => if b then S n else n) 
  [true;false;true;false] 0 = 2.
Proof. reflexivity. Qed.
