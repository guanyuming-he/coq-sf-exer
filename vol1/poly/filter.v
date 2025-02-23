From LF.basics Require Import numbers.
From LF.poly Require Import defns.

Definition filter_even_gt7 (l : list nat) : list nat
  :=
  filter (fun n : nat => andb (even n) (8 <=? n)) l.

Example test_filter_even_gt7_1 :
  filter_even_gt7 [1;2;6;9;10;3;12;8] = [10;12;8].
Proof. reflexivity. Qed.
Example test_filter_even_gt7_2 :
  filter_even_gt7 [5;2;6;19;129] = [].
Proof. reflexivity. Qed.

Definition partition {X : Type}
  (test : X -> bool) (l : list X)
  : list X * list X
  :=
  pair 
  (filter test l)
  (filter (fun x => negb (test x)) l).
  (** Here's a version without filter,
  using Fixpoint:
  match l with
  | nil => [] * []
  | h :: t =>
      match partition test t with
      | pair a b =>
        if test h
        then pair (a ++ [h]) b
        else pair a (b ++ [h])
      end
  end.
   *)


Example test_partition1: partition odd [1;2;3;4;5] = ([1;3;5], [2;4]).
Proof. reflexivity. Qed.
Example test_partition2: partition (fun x => false) [5;9;0] = ([], [5;9;0]).
Proof. reflexivity. Qed.
