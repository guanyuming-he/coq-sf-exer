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

(**
  * not_PNP_informal
    We prove that P /\ ~P would lead to Falsehood.
    By /\, we have both P and ~P. By ~P,
     we have P -> False.
    Thus, we have False.
   *)

Theorem de_morgan_not_or : forall (P Q : Prop),
  ~ (P \/ Q) -> ~P /\ ~Q.
Proof.
  intros P Q.
  intros H.
  unfold not in H.
  unfold not.
  split.
  - intros HP. apply H. left. apply HP.
  - intros HQ. apply H. right. apply HQ.
Qed.

Lemma not_S_pred_n : ~(forall n : nat, S (pred n) = n).
Proof.
  unfold not.
  intros H.
  specialize H with (n := 0).
  discriminate.
Qed.

Theorem not_true_is_false : forall b : bool,
  b <> true -> b = false.
Proof.
  intros b.
  unfold not.
  intros H.
  destruct b.
  - exfalso. apply H. reflexivity.
  - reflexivity.
Qed.
