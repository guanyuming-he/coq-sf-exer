Theorem ex_falso_quodlibet : forall (P:Prop),
  False -> P.
Proof.
  (* WORKED IN CLASS *)
  intros P contra.
  destruct contra. Qed.

 
Theorem not_implies_our_not : forall (P:Prop),
  not P -> (forall (Q:Prop), P -> Q).
Proof.
  intros P H.
  intros Q HP.
  unfold not in H.
  apply H in HP.
  destruct HP.
Qed.

(**
  *double_neg_informal
  Prove P -> ~~P.
  Proof. 
    Given P, we assume ~P.
    That gives a contradiction, so we must not have ~P, that is,
    we must have the negation of ~P, ~~P, as desired.
 *)


Theorem contrapositive : forall (P Q : Prop),
  (P -> Q) -> (~Q -> ~P).
Proof.
  intros P Q.
  intros H.
  intros NQ.
  unfold not.
  intros HP.
  apply H in HP.
  unfold not in NQ.
  apply NQ in HP.
  apply HP.
Qed.


Theorem not_both_true_and_false : forall P : Prop,
  ~ (P /\ ~P).
Proof.
  intros P.
  unfold not.
  intros H.
  destruct H.
  apply H0 in H. apply H.
Qed.
