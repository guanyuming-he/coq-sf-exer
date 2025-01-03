Require Import numbers.

(* 
   The exercise asks me to write a fixpoint function that does terminate on all
   inputs, but that isn't accepted by Coq's Fixpoint.

   The only clue that I have is that Coq requires some argument will be
   "decreasing", from the book. Therefore, I will try write something in which some argument isn't 
   monotonically decreasing.

   For example, let f := 
   0 -> 0
   n -> n+1 for 1 <= n <= N
   0 for n > N.

   Let Fixpoint g := f(n) until n = 0.
   Let's set N := 3 for now.
*)


Fixpoint g (n: nat) : nat :=
  if n =? 0 then 0
  else if n <=? 3 then g (S n)
  else 0.

Compute (g 1).

