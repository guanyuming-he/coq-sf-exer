Require Import booleans.

(*I am using The standard library's nat *)

Fixpoint plus (m n : nat) : nat :=
  match m with
  | 0 => n
  | S m' => S (plus m' n)
  end.

Fixpoint mul (m n : nat) : nat :=
  match m with
  | 0 => 0
  | S m' => plus n (mul m' n)
  end.

Fixpoint eqb (n m : nat) : bool :=
  match n with
  | 0 => match m with
         | 0 => true
         | S m' => false
         end
  | S n' => match m with
            | 0 => false
            | S m' => eqb n' m'
            end
  end.

Fixpoint leb (n m : nat) : bool :=
  match n with
  | 0 => true
  | S n' =>
      match m with
      | 0 => false
      | S m' => leb n' m'
      end
  end.

Notation "x =? y" := (eqb x y) (at level 70) : nat_scope.
Notation "x <=? y" := (leb x y) (at level 70) : nat_scope.
