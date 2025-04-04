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

(* For le *)
From LF.indprop Require Import defns.
(* For subseq *)
From LF.indprop Require Import r_subseq.
(* For many useful lemmas *)
From LF.indprop Require Import indrela.

Theorem filter_challenger_2 :
  (* 
     First, filter test l is such a subsequence that test evaluates to true.
     Second, for all such sequence l, length l <= length (filter test l).
   *)
  forall 
    (* I would want nat to be a general X, but unfortunately subseq from the
     * book is only defined for list nat. *)
    (test : nat -> bool)
    (l : list nat),
    forall sl : list nat,
    subseq sl l /\ All (fun n => test n = true) sl ->
    length sl <= length (filter test l).
Proof.
  intros test l sl [H1 H2].
  induction H1.
  - simpl. apply O_le_n.
  - simpl in H2. destruct H2 as [H2 H3].
    apply IHsubseq in H3.
    simpl.
    rewrite -> H2.
    simpl.
    apply n_le_m__Sn_le_Sm.
    apply H3.
  - apply IHsubseq in H2.
    simpl.
    destruct (test n).
    + simpl. 
      apply (le_trans
      _ _ _ H2).
      apply n_le_Sn.
    + apply H2.
Qed.
    
Inductive pal {X:Type} : list X -> Prop :=
  | pal_0 : pal []
  | pal_1 x : pal [x]
  | pal_induct (x : X) (l : list X) (H : pal l) : pal (x::l++[x]).

(* For list related theorems *)
From LF.poly Require Import poly_list_exer.

Theorem pal_app_rev : forall (X:Type) (l : list X),
  pal (l ++ (rev l)).
Proof.
  intros X l. induction l.
  - simpl. apply pal_0.
  - simpl. rewrite -> app_assoc. apply pal_induct. apply IHl.
Qed.

Theorem pal_rev : forall (X:Type) (l: list X) , pal l -> l = rev l.
Proof.
  intros X l H.
  induction H.
  - reflexivity.
  - reflexivity.
  - simpl. 
    assert (forall l : list X,
    rev (l ++ [x]) = x :: (rev l))
    as H1.
    {
      intros l1. induction l1.
      - reflexivity.
      - simpl. rewrite -> IHl1. reflexivity.
    }
    rewrite -> H1.
    rewrite <- IHpal.
    simpl.
    reflexivity.
Qed.

(* For properties about addition *)
From LF.induction Require Import basic_induction.

(* After a few hours of proving the following Theorem in vein,
   I searched for help online and found that I may need to prove something
   different in order to prove this theorem, to induct on something different.
   Hence this lemma. *)
Lemma palindrome_converse_nat : 
  forall (X : Type) (n: nat) (l: list X), 
  length l <= n -> l = rev l -> pal l.
Proof.
  (* Now, surprisingly, we induction on n instead. *)
  intros X n. induction n.
  - intros l. destruct l.
    + intros H1 H2. apply pal_0.
    + intros H1 H2. simpl in *.
      inversion H1 (* Impossible *).
  - intros l. destruct l.
    + intros H1 H2. apply pal_0.
    + intros H1 H2. simpl in *.
      apply Sn_le_Sm__n_le_m in H1.
      (* To see the first element of (rev l) ++ [x], we have to
          destruct rev l *)
      destruct (rev l) eqn:Erl.
      * simpl in H2. injection H2 as H3.
        rewrite -> H3. apply pal_1.
      * injection H2 as H3 H4.
        rewrite <- H3 in *.
        rewrite -> H4.
        apply pal_induct.
        rewrite -> H4 in Erl.
        rewrite rev_app_distr in Erl. injection Erl as El0.
        rewrite H4 in H1. rewrite app_length in H1.
        simpl in H1. rewrite <- plus_n_Sm in H1. rewrite -> add_0_r in H1.
        apply Sn_le_m__n_le_m in H1.
        apply eq_sym in El0.
        apply (IHn l0 H1 El0).
Qed.

Theorem palindrome_converse: forall {X: Type} (l: list X),
    l = rev l -> pal l.
Proof.
  intros X l.
  assert (exists n : nat, length l <= n) as H1.
  {
    induction l.
    - exists 0. apply le_n.
    - destruct IHl as [n IHl].
      exists (S n).
      simpl. apply n_le_m__Sn_le_Sm. apply IHl.
  }
  destruct H1 as [n H1].
  intros H2.
  apply (palindrome_converse_nat _ _ _ H1 H2).
Qed.

