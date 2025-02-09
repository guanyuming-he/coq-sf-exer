From LF Require Import lists.defns.

Fixpoint nonzeros (l:natlist) : natlist
  :=
  match l with
  | nil => nil
  | h :: t => 
      match h with 
      | 0 => nonzeros t
      | S n' => h :: (nonzeros t)
      end
  end.

Example test_nonzeros:
  nonzeros [0;1;0;2;3;0;0] = [1;2;3].
Proof. reflexivity. Qed.

Fixpoint oddmembers (l:natlist) : natlist
  :=
  match l with
  | nil => nil
  | h :: t => 
      match odd h with 
      | true => h :: (oddmembers t)
      | false => oddmembers t 
      end 
  end.

Example test_oddmembers:
  oddmembers [0;1;0;2;3;0;0] = [1;3].
Proof. reflexivity. Qed.


Definition countoddmembers (l:natlist) : nat
  :=
  length (oddmembers l).

Example test_countoddmembers1:
  countoddmembers [1;0;3;1;4;5] = 4.
Proof. reflexivity. Qed.

Example test_countoddmembers2:
  countoddmembers [0;2;4] = 0.
Proof. reflexivity. Qed.

Example test_countoddmembers3:
  countoddmembers nil = 0.
Proof. reflexivity. Qed.

Fixpoint alternate (l1 l2 : natlist) : natlist
  :=
  match l1 with 
  | nil => l2
  | h :: t => 
      match l2 with
      | nil => l1
      | h' :: t' => h :: h' :: (alternate t t')
      end 
  end.

Example test_alternate1:
  alternate [1;2;3] [4;5;6] = [1;4;2;5;3;6].
Proof. reflexivity. Qed.
Example test_alternate2:
  alternate [1] [4;5;6] = [1;4;5;6].
Proof. reflexivity. Qed.
Example test_alternate3:
  alternate [1;2;3] [4] = [1;4;2;3].
Proof. reflexivity. Qed.
Example test_alternate4:
  alternate [] [20;30] = [20;30].
Proof. reflexivity. Qed.
