Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From LF.basics Require Import numbers.
From LF.indprop Require Import defns.
From LF.indprop Require Import indrela.



Definition relation (X : Type) := X -> X -> Prop.

Definition partial_function {X: Type} (R: relation X) :=
  forall x y1 y2 : X, R x y1 -> R x y2 -> y1 = y2.

Inductive next_nat : nat -> nat -> Prop :=
  | nn n : next_nat n (S n).
Check next_nat : relation nat.
Theorem next_nat_partial_function :
  partial_function next_nat.
Proof.
  unfold partial_function.
  intros x y1 y2 H1 H2.
  inversion H1. inversion H2.
  reflexivity. Qed.

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


Definition symmetric {X: Type} (R: relation X) :=
  forall a b : X, (R a b) -> (R b a).

Theorem le_not_symmetric :
  ~ (symmetric le).
Proof.
  unfold not.
  unfold symmetric.
  intros H. 
  assert (0 <= 1) as H1.
  {
    apply le_S. apply le_n.
  }
  apply H in H1.
  inversion H1.
Qed.

Definition antisymmetric {X: Type} (R: relation X) :=
  forall a b : X, (R a b) -> (R b a) -> a = b.

Theorem le_antisymmetric :
  antisymmetric le.
Proof.
  unfold antisymmetric.
  induction a.
  - intros b _ H2.
    inversion H2.
    reflexivity.
  - intros b. destruct (eqbP b (S a)).
    + intros _ _. rewrite -> H. reflexivity.
    + intros H1 H2.
      inversion H2.
      * reflexivity.
      * apply (le_trans (S a) b a H1) in H4.
        apply not_le_Sn_n in H4.
        destruct H4.
Qed.


Theorem le_step : forall n m p,
  n < m ->
  m <= S p ->
  n <= p.
Proof.
  intros n m p H1 H2.
  unfold lt in H1.
  apply (le_trans _ _ _ H1) in H2.
  apply Sn_le_Sm__n_le_m. apply H2.
Qed.

Definition equivalence {X:Type} (R: relation X) :=
  (reflexive R) /\ (symmetric R) /\ (transitive R).


Definition order {X:Type} (R: relation X) :=
  (reflexive R) /\ (antisymmetric R) /\ (transitive R).

Definition preorder {X:Type} (R: relation X) :=
  (reflexive R) /\ (transitive R).
Theorem le_order :
  order le.
Proof.
  unfold order. split.
    - (* refl *) apply le_reflexive.
    - split.
      + (* antisym *) apply le_antisymmetric.
      + (* transitive. *) apply le_trans. Qed.


Inductive clos_refl_trans {A: Type} (R: relation A) : relation A :=
  | rt_step x y (H : R x y) : clos_refl_trans R x y
  | rt_refl x : clos_refl_trans R x x
  | rt_trans x y z
        (Hxy : clos_refl_trans R x y)
        (Hyz : clos_refl_trans R y z) :
        clos_refl_trans R x z.

Check le_ind.

Theorem next_nat_closure_is_le : forall n m,
  (n <= m) <-> ((clos_refl_trans next_nat) n m).
Proof.
  intros n m. split.
  - (* -> *)
    intro H. induction H.
    + (* le_n *) apply rt_refl.
    + (* le_S *)
      apply rt_trans with m. apply IHle. apply rt_step.
      apply nn.
  - (* <- *)
    intro H. induction H.
    + (* rt_step *) inversion H. apply le_S. apply le_n.
    + (* rt_refl *) apply le_n.
    + (* rt_trans *)
      apply le_trans with y.
      apply IHclos_refl_trans1.
      apply IHclos_refl_trans2. 
Qed.


Inductive clos_refl_trans_1n {A : Type}
                             (R : relation A) (x : A)
                             : A -> Prop :=
  | rt1n_refl : clos_refl_trans_1n R x x
  | rt1n_trans (y z : A)
      (Hxy : R x y) (Hrest : clos_refl_trans_1n R y z) :
      clos_refl_trans_1n R x z.

 Lemma rsc_R : forall (X:Type) (R:relation X) (x y : X),
  R x y -> clos_refl_trans_1n R x y.
Proof.
  intros X R x y H.
  apply rt1n_trans with y. apply H. apply rt1n_refl. 
Qed.

Lemma rsc_trans :
  forall (X:Type) (R: relation X) (x y z : X),
      clos_refl_trans_1n R x y ->
      clos_refl_trans_1n R y z ->
      clos_refl_trans_1n R x z.
Proof.
  intros X R x y z H1.
  induction H1.
  - intros H. apply H.
  - intros H. apply IHclos_refl_trans_1n in H.
    apply (rt1n_trans R x _ _ Hxy H).
Qed.

Theorem rtc_rsc_coincide :
  forall (X:Type) (R: relation X) (x y : X),
    clos_refl_trans R x y <-> clos_refl_trans_1n R x y.
Proof.
  intros X R x y. split.
  - intros H. induction H.
    + apply rsc_R. apply H.
    + apply rt1n_refl.
    + apply (rsc_trans X R x y z IHclos_refl_trans1 IHclos_refl_trans2).
  - intros H. induction H.
    + apply rt_refl.
    + apply rt_trans with (y := y).
      * apply rt_step. apply Hxy.
      * apply IHclos_refl_trans_1n.
Qed.
