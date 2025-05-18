Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From LF.basics Require Import numbers.
From LF.indprop Require Import defns.
From LF.indprop Require Import indrela.



Definition relation (X : Type) := X -> X -> Prop.

Definition partial_function {X: Type} (R: relation X) :=
  forall x y1 y2 : X, R x y1 -> R x y2 -> y1 = y2.

(* It seems that the two following relations are not in IndProp. So I searched
 * the Internet and found them in older versions of LF. *)

(* Defined as nothing, i.e., nothing satisfies it. *)
Inductive empty_relation : nat -> nat -> Prop :=
  .
(* Defined as every pair satisfying it. *)
Inductive total_relation : nat -> nat -> Prop :=
  | total_rel (n m : nat) : total_relation n m.

Theorem total_relation_not_partial_function :
  ~ (partial_function total_relation).
Proof.
  unfold partial_function.
  unfold not. 
  intros H.
  assert (0 = 1) as contra.
  {
    apply (H 0 0 1).
    - apply total_rel.
    - apply total_rel.
  }
  discriminate contra.
Qed.

Theorem empty_relation_partial_function :
  partial_function empty_relation.
Proof.
  unfold partial_function.
  intros x y1 y2 H1 _.
  inversion H1.
Qed.

Definition reflexive {X: Type} (R: relation X) :=
  forall a : X, R a a.

Theorem le_reflexive :
  reflexive le.
Proof.
  unfold reflexive. intros n. apply le_n. Qed.

Definition transitive {X: Type} (R: relation X) :=
  forall a b c : X, (R a b) -> (R b c) -> (R a c).
Theorem le_trans :
  transitive le.
Proof.
  intros n m o Hnm Hmo.
  induction Hmo.
  - (* le_n *) apply Hnm.
  - (* le_S *) apply le_S. apply IHHmo. apply Hnm. 
Qed.


Theorem lt_trans:
  transitive lt.
Proof.
  unfold lt. unfold transitive.
  intros n m o Hnm Hmo.
  set (H1 := le_S (S n) m Hnm).
  apply le_trans with (a := (S n)) (b := (S m)) (c := o).
  apply H1.
  apply Hmo. 
Qed.


Theorem lt_trans' :
  transitive lt.
Proof.
  (* Prove this by induction on evidence that m is less than o. *)
  unfold lt. unfold transitive.
  intros n m o Hnm Hmo.
  (* Need to add these two remembers before the induction *)
  remember (S n) as sn.
  remember (S m) as sm.
  induction Hmo.
  - rewrite -> Heqsm. apply (le_S _ _ Hnm).
  - apply le_S. apply IHHmo. apply Heqsm.
Qed.

From LF.indprop Require Import reflect.

Theorem lt_trans'' :
  transitive lt.
Proof.
  unfold lt. unfold transitive.
  intros n m o.
  generalize dependent n.
  generalize dependent m.
  induction o.
  - intros n m Hnm Hmo. inversion Hmo. 
  - intros n m H1 H2.
    apply Sn_le_Sm__n_le_m in H2.
    destruct (eqbP n o).
    + apply le_S. rewrite <- H. apply H1.
    + assert (S n <= o) as H3.
      {
        inversion H2.
        - destruct (H H3).
        - apply n_le_m__Sn_le_Sm. apply H0.
      }
      apply le_S.
      apply (IHo _ _ H1 H3).
Qed.


(* Turns out the following three have already been proven by me as lemmas.*)

Theorem le_Sn_le : forall n m, S n <= m -> n <= m.
Proof.
  exact Sn_le_m__n_le_m.
Qed.


Theorem le_S_n : forall n m,
  (S n <= S m) -> (n <= m).
Proof.
  exact Sn_le_Sm__n_le_m.
Qed.

(* Informal proof: forall n, ~(Sn <= n):
  Induct on n.
  - Assume S 0 <= 0. Because 0 is not a successor of anyone, this can only come from le_n, which means S 0 = 0, a contradiction.
  - Assume S (S n) <= S n. By le_S_n, we thus have S n <= n, which gives a contradiction by the inductive hypothesis.
*)

Theorem le_Sn_n: forall n : nat, ~(S n <= n).
Proof.
  exact not_le_Sn_n.
Qed.




