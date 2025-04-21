Definition add1 : nat -> nat.
intro n.
Show Proof.
apply S.
Show Proof.
apply n. Defined.
Print add1.
(* ==>
    add1 = fun n : nat => S n
         : nat -> nat
*)
Compute add1 2.
(* ==> 3 : nat *)
