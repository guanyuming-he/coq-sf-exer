From LF.induction Require Import basic_induction.

Example plus_is_O :
  forall n m : nat, n + m = 0 -> n = 0 /\ m = 0.
Proof.
  intros n m H.
  split.
  - destruct n.
    + reflexivity.
    + discriminate.
  - destruct m.
    + reflexivity.
    + rewrite -> add_comm in H. discriminate.
Qed.

Lemma proj2 : forall P Q : Prop,
  P /\ Q -> Q.
Proof.
  intros P Q [_ H2].
  apply H2.
Qed.

Theorem and_commut : forall P Q : Prop,
  P /\ Q -> Q /\ P.
Proof.
  intros P Q [HP HQ].
  split.
    - (* left *) apply HQ.
    - (* right *) apply HP. Qed.

Theorem and_assoc : forall P Q R : Prop,
  P /\ (Q /\ R) -> (P /\ Q) /\ R.
Proof.
  intros P Q R [HP [HQ HR]].
  split.
  - split.
    { apply HP. }
    { apply HQ. }
  - apply HR.
Qed.
