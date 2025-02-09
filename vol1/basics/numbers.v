From LF Require Export basics.booleans.

Module NatPlayground.

Inductive nat : Type :=
  | O
  | S (n : nat).

Definition pred (n : nat) : nat :=
  match n with
  | O => O
  | S n' => n'
  end.

End NatPlayground.

(* Even odd *)

Fixpoint even (n:nat) : bool :=
  match n with
  | O => true
  | S O => false
  | S (S n') => even n'
  end.

Definition odd (n:nat) : bool :=
  negb (even n).

Module NatPlayground2.

Fixpoint plus (m n : nat) : nat :=
  match m with
  | 0 => n
  | S m' => S (plus m' n)
  end.

Fixpoint mult (m n : nat) : nat :=
  match m with
  | 0 => 0
  | S m' => plus n (mult m' n)
  end.

End NatPlayground2.

(* exp, eqb, leb *)

Fixpoint exp (base power : nat) : nat :=
  match power with
  | O => S O
  | S p => mult base (exp base p)
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

(* notations *)

Notation "x + y" := (plus x y)
                       (at level 50, left associativity)
                       : nat_scope.
Notation "x - y" := (minus x y)
                       (at level 50, left associativity)
                       : nat_scope.
Notation "x * y" := (mult x y)
                       (at level 40, left associativity)
                       : nat_scope.
Check ((0 + 1) + 1) : nat.
Notation "x =? y" := (eqb x y) (at level 70) : nat_scope.
Notation "x <=? y" := (leb x y) (at level 70) : nat_scope.
