From LF.poly Require Import defns.

Inductive nostutter {X:Type} : list X -> Prop :=
  (* My understanding of the defn:
     A list shutters iff there exists consequtive sublist of length 2 of it
     contains the same two elements.
  *)
  | nost_empty : nostutter []
  | nost_1 (x : X) : nostutter [x]
  | nost_induct 
      (x h : X) (t : list X) 
      (H1 : nostutter (h :: t)) (H2 : x <> h) :
      nostutter (x :: h::t).

Example test_nostutter_1: nostutter [3;1;4;1;5;6].
Proof. 
  repeat apply nost_induct; auto.
  apply nost_1.
Qed.

Example test_nostutter_2: nostutter (@nil nat).
Proof. 
  apply nost_empty.
Qed.

Example test_nostutter_3: nostutter [5].
Proof.
  apply nost_1.
Qed.

Example test_nostutter_4: not (nostutter [3;1;1;4]).
Proof.
  unfold not.
  intros H.
  inversion H.
  inversion H0. (* will get 1 <> 1 *)
  unfold not in H9. apply H9. reflexivity.
Qed.


Inductive merge {X:Type} : list X -> list X -> list X -> Prop :=
  (* My understanding:
     A list l is a merge of l1 and l2 (merge l1 l2 l), iff
     l1 and l2 are sublists of l, and that l contains only
     the elements of l1 and l2 (i.e. length l = length l1 + length l2)
   *)
  | merge_0 : merge [] [] []
  | merge_l x l1 l2 l (H : merge l1 l2 l)
      : merge (x::l1) l2 (x::l)
  | merge_r x l1 l2 l (H : merge l1 l2 l)
      : merge l1 (x::l2) (x::l).

(* For All *)
From LF.logic Require Import prog_props.

Theorem merge_filter : forall (X : Set) (test: X->bool) (l l1 l2 : list X),
  merge l1 l2 l ->
  All (fun n => test n = true) l1 ->
  All (fun n => test n = false) l2 ->
  filter test l = l1.
Proof.
  intros X test l l1 l2 H.
  induction H.
  - intros H1 H2. simpl. reflexivity.
  - intros H1 H2. simpl.
    destruct (test x) eqn:Ex.
    + simpl in H1. destruct H1 as [_ H1].
      rewrite (IHmerge H1 H2).
      reflexivity.
    + simpl in H1. destruct H1 as [H1 _].
      rewrite -> H1 in Ex. discriminate Ex.
  - intros H1 H2. simpl.
    destruct (test x) eqn:Ex.
    + simpl in H2. destruct H2 as [H2 _].
      rewrite -> H2 in Ex. discriminate Ex.
    + simpl in H2. destruct H2 as [_ H2].
      apply (IHmerge H1 H2).
Qed.


