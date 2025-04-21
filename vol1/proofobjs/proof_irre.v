Definition propositional_extensionality : Prop :=
  forall (P Q : Prop), (P <-> Q) -> P = Q.

Theorem pe_implies_or_eq :
  propositional_extensionality ->
  forall (P Q : Prop), (P \/ Q) = (Q \/ P).
Proof.
  intros pe P Q.
  apply pe.
  split.
  - intros [p|q]. 
    + right. apply p.
    + left. apply q.
  - intros [q|p]. 
    + right. apply q.
    + left. apply p.
Qed.

Lemma pe_implies_true_eq :
  propositional_extensionality ->
  forall (P : Prop), P -> True = P.
Proof. 
  intros pe P p.
  apply pe.
  split.
  - intros _. apply p.
  - intros _. apply I.
Qed.

Definition proof_irrelevance : Prop :=
  forall (P : Prop) (pf1 pf2 : P), pf1 = pf2.

Theorem pe_implies_pi :
  propositional_extensionality -> proof_irrelevance.
Proof.
  intros pe.
  unfold propositional_extensionality in pe.
  unfold proof_irrelevance.
  intros P pf1 pf2.
  (* can use either pf1 or pf2. doesn't matter. *)
  assert (H := (pe_implies_true_eq pe P pf1)).
  (* rewrite <- H to get pf1 pf2 : True doesn't work.
     The only way left is destruct. *)
  destruct H.
  (* The only way to get to True is through I.
     Hence, destruct will show that they must equal to I *)
  destruct pf1.
  destruct pf2.
  reflexivity.
Qed.

