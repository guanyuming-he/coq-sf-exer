From LF Require Import induction.basic_induction.

Theorem plus_leb_compact_l : forall n m p : nat,
  n <=? m = true -> (p + n) <=? (p + m) = true.
Proof.
  intros n m p.
  induction p as [| p' IHp'].
  - simpl. intros H. rewrite -> H. reflexivity.
  - simpl. intros H. rewrite -> IHp'. 
    reflexivity.  rewrite -> H. reflexivity.
Qed.
  
