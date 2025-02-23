From LF.poly Require Import defns.

Module Church.

Definition cnat := forall X : Type, (X -> X) -> X -> X.

Definition one : cnat :=
  fun (X : Type) (f : X -> X) (x : X) => f x.

Definition two : cnat :=
  fun (X : Type) (f : X -> X) (x : X) => f (f x).

Definition zero : cnat :=
  fun (X : Type) (f : X -> X) (x : X) => x.

Definition three : cnat := @doit3times.

Definition scc (n : cnat) : cnat
  :=
  (* This is tricky, but remember that
  n X f x stands for n times applying f to x,
  then we just need to get f out.
  Maybe we can use an argument as f. *)
  fun (X : Type) (f : X -> X) (x : X) => f (n X f x).

Example scc_1 : scc zero = one.
Proof. reflexivity. Qed.
Example scc_2 : scc one = two.
Proof. reflexivity. Qed.
Example scc_3 : scc two = three.
Proof. reflexivity. Qed.

Definition plus (n m : cnat) : cnat
  :=
  (* Fortunately, I don't even need recursion here
  as applying n to m will give n more times f.
  *)
  fun (X : Type) (f : X -> X) (x : X) =>
  n X f (m X f x).

Example plus_1 : plus zero one = one.
Proof. reflexivity. Qed.
Example plus_2 : plus two three = plus three two.
Proof. reflexivity. Qed.
Example plus_3 :
  plus (plus two two) three = plus one (plus three three).
Proof. reflexivity. Qed.

Definition mult (n m : cnat) : cnat
  :=
  (* Because we can apply m X f to x,
     m X f is itself a function *)
  fun (X : Type) (f : X -> X) (x : X) =>
  n X (m X f) x.

Example mult_1 : mult one one = one.
Proof. reflexivity. Qed.
Example mult_2 : mult zero (plus three three) = zero.
Proof. reflexivity. Qed.
Example mult_3 : mult two three = plus three three.
Proof. reflexivity. Qed.

Definition exp (n m : cnat) : cnat
  :=
  (* This time we need to take mult n as a function *)
  fun (X : Type) (f : X -> X) (x : X) =>
  (* 
     do m times n multiply to one.
     But because we can't use cnat as the Type argument, 
     we have to move x out, as as a consequence unable to use mult,
     so the (fun g => n X g) is just copied mult impl, without x.
   *)
  (m (X -> X) (fun g => n X g) (one X f)) x.


Example exp_1 : exp two two = plus two two.
Proof. reflexivity. Qed.
Example exp_2 : exp three zero = one.
Proof. reflexivity. Qed.
Example exp_3 : exp three two = plus (mult two (mult two two)) one.
Proof. reflexivity. Qed.

End Church.
