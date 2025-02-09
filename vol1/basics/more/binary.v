From LF Require Import basics.numbers.

Inductive bin : Type :=
  | Z
  | B0 (n : bin)
  | B1 (n : bin).

(* 
  My answer to the comprehension check:
  B_0 Z equals 0b = 0.
*)

(* 
  My Note:
  According to the definition, the binary numbers
  are little-endian, where the most significant bit 
  is at the right-most position (biggest memory address.

  This indeed can make our lives easier in defining the following
  two functions.

  Nevertheless, one can always use a stack to reverse the order of the bits.
*)

Fixpoint incr (m:bin) : bin
  :=
  (* It would be hard to detect overflow in increament and act accordingly.
     However, since the binary numbers are little-endian,
     we start at the least significant bit.
     Thus, thanks to that, the process can become like this:
    
     1. Start at the least significant bit.
     2. try add 1 to the current bit.
     3. If the current bit is 0, then adding 1 succeeds. Returns B1 the rest.
     4. Otherwise, a overflow occurs at the current bit, resulting in adding 1 
     to the next bit and resetting the current bit to 0. 
     5. If all other bits are 1, we eventually will reach the most significant bit,
     where we have two cases:
        i. It is 0, that is, we encounter B0 Z, then we set it to 1.
        ii. It is 1, that is, we encounter B1 Z, then we add one more bit two it and
        returns B0 B1 Z at that time.
   *)
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

Example test_bin_incr1 : (incr (B1 Z)) = B0 (B1 Z).
Proof. simpl. reflexivity. Qed.
Example test_bin_incr2 : (incr (B0 (B1 Z))) = B1 (B1 Z).
Proof. simpl. reflexivity. Qed.
Example test_bin_incr3 : (incr (B1 (B1 Z))) = B0 (B0 (B1 Z)).
Proof. simpl. reflexivity. Qed.
Example test_bin_incr4 : bin_to_nat (B0 (B1 Z)) = 2.
Proof. simpl. reflexivity. Qed.
Example test_bin_incr5 :
        bin_to_nat (incr (B1 Z)) = 1 + bin_to_nat (B1 Z).
Proof. simpl. reflexivity. Qed.
Example test_bin_incr6 :
        bin_to_nat (incr (incr (B1 Z))) = 2 + bin_to_nat (B1 Z).
Proof. simpl. reflexivity. Qed.

