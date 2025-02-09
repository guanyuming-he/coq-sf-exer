From LF Require Export basics.more.binary.
From LF Require Export induction.basic_induction.

Fixpoint bin_to_nat (m:bin) : nat
  :=
  (* starting from the least significant bit makes it easier. *)
  match m with
  | Z => 0 
  | B0 n => 2 * (bin_to_nat n)
  | B1 n => 1 + (2 * (bin_to_nat n))
  end.

Theorem bin_to_nat_pres_incr : forall b : bin,
  bin_to_nat (incr b) = 1 + bin_to_nat b.
Proof.
  intros b.
  induction b as [ | | b IHb ].
  - simpl. reflexivity.
  - simpl. reflexivity.
  - simpl. rewrite -> IHb. simpl. rewrite <- plus_n_Sm. reflexivity.
Qed.

Fixpoint nat_to_bin (n : nat) : bin 
  :=
  match n with
  | 0 => Z
  | S n' => incr (nat_to_bin n')
  end.

Theorem nat_bin_nat : forall n, bin_to_nat (nat_to_bin n) = n.
Proof.
  intros n.
  induction n.
  - simpl. reflexivity.
  - simpl. rewrite -> bin_to_nat_pres_incr. rewrite -> IHn. reflexivity.
Qed.

