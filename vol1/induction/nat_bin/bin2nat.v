Require Import LF.Basics.
Require Import LF.double_plus.
Require Import LF.nat_bin.nat2bin.

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
  (* Proof Idea
     In principle, if we induct on b, then, we need to show - nat_to_bin
     (bin_to_nat Z) = normalize Z.  
     - if that's already true for some b, then
     nat_to_bin (bin_to_nat B0 b) = normalize (B0 b) 
     - if that's already true for some b, then 
     nat_to_bin (bin_to_nat B1 b) = normalize (B1 b)

     Note that, B0 b = double b.  B1 b = 1 + double b = incr (double b).  Inside
     normalize, normalize (double b) can be seen as resulting in double
     (normalize b), while normalize (B1 b) = B1 (normalize b).  Compare this
     with the fact that normalize (B0 b) != B0 (normalize b) in general, for
     when b = 0.  This irregularity is a result of, by definition, double Z = Z
     instead of B0 Z.

     Thus, we need to show, given the inductive hypothesis, 
     - nat_to_bin (bin_to_nat double b) = double (normalize b).  
     - nat_to_bin (bin_to_nat B1 b) = B1 (normalize b).

     OK, it's not immediately clear how to proceed,
     but we could try using the inductive hypothesis now, by rewriting <-
     - nat_to_bin (bin_to_nat double b) = double (nat_to_bin (bin_to_nat b))
     - nat_to_bin (bin_to_nat B1 b) = B1 (nat_to_bin (bin_to_nat b))

     They seem pretty intuitive, so, this is my proof strategy for now.
   *)
  (* lemma 1 *)
  assert (forall b : bin, normalize (B0 b) = double_bin (normalize b)) as lm1.
  {
    intros b.
    (* just verify each case by definition. *)
    destruct b.
    - simpl. reflexivity.
    - simpl. reflexivity.
    - simpl. reflexivity.
  }
  (* lemma 2*)
  assert (forall b : bin, normalize (B1 b) = B1 (normalize b)) as lm2.
  {
    intros b.
    (* just verify each case by definition. *)
    destruct b.
    - simpl. reflexivity.
    - simpl. reflexivity.
    - simpl. reflexivity.
  }
  assert (forall b : bin, bin_to_nat (B0 b) = bin_to_nat (double_bin b)) as lm3.
  {
    intros b.
    destruct b.
    - simpl. reflexivity.
    - simpl. reflexivity.
    - simpl. reflexivity.
  }
  assert (
    forall b : bin,
    bin_to_nat (double_bin b) = 2 * (bin_to_nat b)
  ) as lm4.       
  {
    intros b.
    destruct b.
    - simpl. reflexivity.
    - simpl. reflexivity.
    - simpl. reflexivity.
  }
  assert (
    forall n : nat,
    nat_to_bin (2 * n) = double_bin (nat_to_bin n)
  ) as lm5.       
  {
    intros n.
    induction n.
    - simpl. reflexivity.
    - simpl. rewrite -> double_incr_bin. rewrite <- IHn. rewrite <- plus_n_Sm.
      simpl. reflexivity.
  }
  assert (
    forall b : bin,
    B1 b = incr (double_bin b)
  ) as lm6.       
  {
    intros b.
    destruct b.
    - simpl. reflexivity.
    - simpl. reflexivity.
    - simpl. reflexivity.
 }

  intros b.
  induction b.
     - simpl. reflexivity.
     - rewrite -> lm1. rewrite <- IHb. rewrite -> lm3.
       rewrite -> lm4. rewrite -> lm5. reflexivity.
     - rewrite -> lm2. rewrite <- IHb. simpl. rewrite -> lm6.
       assert (forall n : nat, n+(n+0) = 2*n) as temp.
       { reflexivity. } 
       rewrite -> temp. rewrite -> lm5. reflexivity.
  Qed.
