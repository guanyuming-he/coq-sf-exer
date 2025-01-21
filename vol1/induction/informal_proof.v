(* Theorem Addition_is_commutative *)

(* Proof
 we need to show that m+n = n+m.
 we induct on m.
 Base case:
 when m = 0, we need to show 0+n = n+0.
   by definition, 0+n = n.
   by add_0_r, n+0 = n.
   Thus, 0+n = n+0.
 Inductive step:
 when m = S m' for some m' : nat,
 we need to show S m' + n = n + (S m').
   by definition, S m' + n = S (m' + n).
   by plus_n_Sm, n + (S m') = S (n + m').
   by inductive hypothesis, m' + n = n + m',
   thus S m' + n = n + (S m'), as desired.
 We can now close the induction.
*)

(* Theorem (n ?= n) = true for any n *)

(* Proof
  we induct on n.
  Base case:
  when n = 0, 0 ?= 0 holds by definition.
  Inductive step:
  when n = S n' for some n' : nat,
  we need to show (S n' ?= S n') = true.
   By the definitino of ?=, it suffices to show n' ?= n',
   which holds by our inductive hypothesis.
We can now close the induction.
 *)
