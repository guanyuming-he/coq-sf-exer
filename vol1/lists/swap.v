From LF Require Import lists.defns.

Theorem snd_fst_is_swap : forall (p : natprod),
  (snd p, fst p) = swap_pair p.
Proof.
  intros p. destruct p.
  { simpl. reflexivity. }
Qed.

Theorem fst_swap_is_snd : forall (p : natprod),
  fst (swap_pair p) = snd p.
Proof.
  intros p.
  rewrite <- snd_fst_is_swap.
  reflexivity.
Qed.
