From LF.poly Require Import defns.


Example injection_ex3 : forall (X : Type) (x y z : X) (l j : list X),
  x :: y :: l = z :: j ->
  j = z :: l ->
  x = y.
Proof.
  intros X x y z l j.
  intros H1.
  intros H2.
  injection H1.
  rewrite -> H2.
  intros H3.
  injection H3.
  symmetry.
  transitivity z.
  - apply H.
  - symmetry. apply H0.
Qed.
