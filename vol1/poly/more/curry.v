From LF.poly Require Import defns.

Definition prod_curry {X Y Z : Type}
 (f : X * Y -> Z) (x : X) (y : Y) : Z 
 := f (x, y).

Definition prod_uncurry {X Y Z : Type}
(f : X -> Y -> Z) (p : X * Y) : Z
  := f (fst p) (snd p).

Example test_map1': map (plus 3) [2;0;2] = [5;3;5].
Proof. reflexivity. Qed.

Check @prod_curry.
Check @prod_uncurry.
Theorem uncurry_curry : forall (X Y Z : Type)
  (f : X -> Y -> Z)
  x y,
  prod_curry (prod_uncurry f) x y = f x y.
Proof.
  intros X Y Z f x y.
  simpl. reflexivity.
Qed.

Theorem curry_uncurry : forall (X Y Z : Type)
  (f : (X * Y) -> Z) (p : X * Y),
  prod_uncurry (prod_curry f) p = f p.
Proof.
  intros X Y Z f p.
  destruct p.
  - simpl. reflexivity.
Qed.

(** nth_error_informal
  We induct on n.
  When n = 0,
  we show that l must equals to nil.
  Suppose for the sake of contradiction that 
  it equals h :: t instead, then by the definition    of length, length l equals S (length t), not equal to 0, a contradiction.

  Thus, l equals nil. Thus, by definition, nth_error l n = None.

  Now suppose inductively for n
 length l = n → @nth_error X l n = None  
 is true,
 then, if length l = S n, we show that l must equal to h :: t and length t must equal to n.

We have two cases, if l equals nil, then by definition it's impossible.
If l equals h :: t, then length l = S (length t). But it equals S n, then we have length t = n.

Expand the definition of nth_error, because S n != 0, it expands into 
nth_error t n, which by the inductive hypothesis is None.

We can now close the induciton.

 *)


