Require Import LF.Basics.
Require Import LF.double_plus.
Require Import LF.nat_bin.nat2bin.

(* copied from ../../basics/more/binary.v, as required by the exercise *)
Fixpoint incr (m:bin) : bin
  :=
  match m with
  | Z => B1 Z
  (* included by others, step 5.i | B0 Z => B1 Z *)
  (* included by others, step 5.ii | B1 Z => B0 (B1 Z) *)
  | B0 n => B1 n (* step 3 *)
  | B1 n => B0 (incr n) (* step 4 *)
  end.

Fixpoint bin_to_nat (m:bin) : nat
  :=
  (* starting from the least significant bit makes it easier. *)
  match m with
  | Z => 0 
  | B0 n => 2 * (bin_to_nat n)
  | B1 n => 1 + (2 * (bin_to_nat n))
  end.
Lemma double_incr : forall n : nat, double (S n) = S (S (double n)).
Proof.
  intros n.
  induction n.
  - simpl. reflexivity.
  - simpl. rewrite <- IHn. reflexivity.
Qed.
(* end copy *)

(*  returns 2 times b, which is simple in the binary case:
    just append 0 before the least significant bit. *)
Definition double_bin (b:bin) : bin
  :=
  (* 
     we could just return B0 b here,
     but the next example needs us to show that double Z = Z,
     so we have to do a match
   *)
  match b with
  | Z => Z
  | B0 b' => B0 (B0 b')
  | B1 b' => B0 (B1 b')
  end.

Example double_bin_zero : double_bin Z = Z.
Proof.
  simpl. reflexivity.
Qed.

Lemma double_incr_bin : forall b,
    double_bin (incr b) = incr (incr (double_bin b)).
Proof.
  intros b.
  destruct b.
  - simpl. reflexivity.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

(* 
  Now I explain why the failure occurs.
  This is because, we can append as many B0 after the most significant
  bit of a binary as we want, without changing its value
*) 
  
 Fixpoint normalize (b:bin) : bin
   :=
   match b with
   | Z => Z
   (* 
      the following two cases eliminates all 
      significant B0's recursively
   *)
   | B0 Z => Z
   | B0 n => 
       match normalize n with
       | Z => Z (* discard this B0 as well *)
       | n' => B0 n' (* keep the result if n is not reduced to Z *)
       end
   | B1 n => B1 (normalize n) 
   end.

Theorem bin_nat_bin : forall b, nat_to_bin (bin_to_nat b) = normalize b.
Proof.
Admitted.
