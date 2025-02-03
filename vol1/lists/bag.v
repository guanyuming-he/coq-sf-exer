From LF Require Import defns.
From LF Require Import list_funs.

Definition bag := natlist.

 Fixpoint count (v : nat) (s : bag) : nat
   :=
   match s with
   | nil => 0
   | h :: t => 
       (* if then else is essentially matching a boolean value
          with true and false *)
       if h =? v then S (count v t)
       else count v t
   end.

 Example test_count1: count 1 [1;2;3;1;4;1] = 3.
 Proof. reflexivity. Qed.
Example test_count2: count 6 [1;2;3;1;4;1] = 0.
 Proof. reflexivity. Qed.

 (* See
  * https://coq.inria.fr/doc/V8.20.0/refman/language/core/assumptions.html#functions-fun-and-function-types-forall
  * for what this bag -> bag -> bag is *)
 Definition sum : bag -> bag -> bag
   := alternate.

Example test_sum1: count 1 (sum [1;2;3] [1;4;1]) = 3.
Proof. reflexivity. Qed.
Definition add (v : nat) (s : bag) : bag
  := v :: s.

Example test_add1: count 1 (add 1 [1;4;1]) = 3.
Proof. reflexivity. Qed.
Example test_add2: count 5 (add 1 [1;4;1]) = 0.
Proof. reflexivity. Qed.

(*
   we could use Definition by saying (count v s) != 0
   but that is slower, because count still continues 
   even if it sees an occurrance.
   By definiting from scratch, we can terminate there.
 *)
Fixpoint member (v : nat) (s : bag) : bool
  :=
  match s with 
  | nil => false
  | h :: t => 
      if v =? h then true 
      else member v t 
  end.
Example test_member1: member 1 [1;4;1] = true.
Proof. reflexivity. Qed.
Example test_member2: member 2 [1;4;1] = false.
Proof. reflexivity. Qed.

Fixpoint remove_one (v : nat) (s : bag) : bag
  :=
  match s with 
  | nil => nil 
  | h :: t => 
      if h =? v then t 
      else h :: (remove_one v t)
  end.

Example test_remove_one1:
  count 5 (remove_one 5 [2;1;5;4;1]) = 0.
Proof. reflexivity. Qed.
Example test_remove_one2:
  count 5 (remove_one 5 [2;1;4;1]) = 0.
Proof. reflexivity. Qed.
Example test_remove_one3:
  count 4 (remove_one 5 [2;1;4;5;1;4]) = 2.
Proof. reflexivity. Qed.
Example test_remove_one4:
  count 5 (remove_one 5 [2;1;5;4;5;1;4]) = 1.
Proof. reflexivity. Qed.

Fixpoint remove_all (v:nat) (s:bag) : bag
  :=
  match s with 
  | nil => nil 
  | h :: t => 
      if h =? v then remove_all v t
      else h :: (remove_all v t)
  end.
Example test_remove_all1: count 5 (remove_all 5 [2;1;5;4;1]) = 0.
Proof. reflexivity. Qed.
Example test_remove_all2: count 5 (remove_all 5 [2;1;4;1]) = 0.
Proof. reflexivity. Qed.
Example test_remove_all3: count 4 (remove_all 5 [2;1;4;5;1;4]) = 2.
Proof. reflexivity. Qed.
Example test_remove_all4: count 5 (remove_all 5 [2;1;5;4;5;1;4;5;1;4]) = 0.
Proof. reflexivity. Qed.


Fixpoint included (s1 : bag) (s2 : bag) : bool
  (** 
  I can purely rely on count and remove_one to do this:

     - base case: s1 is nil -> true.
     - recursive step: if the count of the head of s1 in s2 is 0, then false.
       otherwise, remove the head of s1, and remove_one it from s2, and recursively
       call the function on them.
  *)
  :=
  match s1 with 
  | nil => true 
  | h :: t =>
      if (count h s2) =? 0 then false
      else included t (remove_one h s2)
  end.
Example test_included1: included [1;2] [2;1;4;1] = true.
Proof. reflexivity. Qed.
Example test_included2: included [1;2;2] [2;1;4;1] = false.
Proof. reflexivity. Qed.
