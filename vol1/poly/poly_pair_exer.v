From LF.poly Require Import defns.

(** 
 *Exercise combine_check
  I believe the type of combine is
   forall X : Type, forall Y : type, list X -> list X -> list (X * Y)

  I believe Compute (combine [1;2] [false;false;true;true])
  prints [ (1, false); (2, false) ].

 *)

Check @combine : forall X : Type, forall Y : Type,
  list X -> list Y -> list (X * Y).

Example combine_compute : (combine [1;2] [false;false;true;true]) = 
  [(1,false) ; (2,false)].
Proof.
  reflexivity. 
Qed.

Fixpoint split {X Y : Type} (l : list (X * Y)) : (list X) * (list Y) :=
  match l with
  | nil => ([], [])
  | (a, b) :: t => 
      match split t with 
      | pair x y =>
        ( a :: x,
          b :: y )
      end
  end.

Example test_split:
  split [(1,false);(2,false)] = ([1;2],[false;false]).
Proof.
  reflexivity. 
Qed.

