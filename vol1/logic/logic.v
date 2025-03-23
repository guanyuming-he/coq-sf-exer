(* for lists and theorems regarding rev. *)
From LF.poly Require Import defns poly_list_exer.
From LF.more_tac Require Import apply.

Axiom functional_extensionality : forall {X Y: Type}
                                    {f g : X -> Y},
  (forall (x:X), f x = g x) -> f = g.

Fixpoint rev_append {X} (l1 l2 : list X) : list X :=
  match l1 with
  | [] => l2
  | x :: l1' => rev_append l1' (x :: l2)
  end.
Definition tr_rev {X} (l : list X) : list X :=
  rev_append l [].

(* Not in the book, but needed for the following proof. *)
Lemma cons_app_single_element : 
  forall {X : Type} (x : X) (l : list X),
  x :: l = [x] ++ l.
Proof.
  intros x l.
  reflexivity.
Qed.

Theorem tr_rev_correct : forall X, @tr_rev X = @rev X.
Proof.
  intros X.
  (* Our target, which we apply Axiom functional_extensionality
     on *) 
  assert (
    forall (l : list X), @tr_rev X l = @rev X l 
  ) as Tar.
  {
    intros l.
    induction l.
    - reflexivity.
    - simpl. unfold tr_rev. simpl. 
      rewrite <- IHl. unfold tr_rev.
      assert ( 
        forall (l1 l2 l3 : list X),
        rev_append l1 (l2 ++ l3) = (rev_append l1 l2) ++ l3
      ) as H.
      {
        intros l1. induction l1 as [| h1 t1].
        - reflexivity.
        - simpl. 
          intros l2 l3.
          rewrite -> cons_app_single_element.
          rewrite -> app_assoc.
          rewrite (IHt1 ([h1] ++ l2) l3).
          rewrite <- cons_app_single_element.
          reflexivity.
      }
      rewrite <- H. reflexivity.
  }
  apply functional_extensionality.
  apply Tar.
Qed.

Definition excluded_middle := forall P : Prop,
  P \/ ~ P.

(* For De Morgan's rule *)
From LF.logic Require Import falsehood.

(* This shows that neg LEM would lead to falsehood. *)
Theorem excluded_middle_irrefutable: forall (P : Prop),
  ~ ~ (P \/ ~ P).
Proof.
  intros P.
  unfold not. 
  intros H.
  apply (de_morgan_not_or P (P -> False)) in H.
  unfold not in H.
  destruct H as [H1 H2].
  contradiction.
Qed.

Theorem not_exists_dist :
  excluded_middle ->
  forall (X:Type) (P : X -> Prop),
    ~ (exists x, ~ P x) -> (forall x, P x).
Proof.
  intros LEM.
  intros X P.
  unfold not. intros H.
  intros x.
  unfold excluded_middle in LEM.
  specialize LEM with (P := P x).
  destruct LEM as [H1|H2].
  - apply H1.
  - unfold not in H2. 
    assert (exists x : X, P x -> False) as temp.
    { exists x. apply H2. }
    apply H in temp.
    contradiction.
Qed.


Definition peirce := forall P Q: Prop,
  ((P -> Q) -> P) -> P.
Definition double_negation_elimination := forall P:Prop,
  ~~P -> P.
Definition de_morgan_not_and_not := forall P Q:Prop,
  ~(~P /\ ~Q) -> P \/ Q.
Definition implies_to_or := forall P Q:Prop,
  (P -> Q) -> (~P \/ Q).
Definition consequentia_mirabilis := forall P:Prop,
  (~P -> P) -> P.

Lemma neg_p_to_everything : forall P Q : Prop,
  ~P -> (P -> Q).
Proof.
  intros P Q.
  intros H1 H2.
  unfold not in H1.
  apply H1 in H2.
  destruct H2.
Qed.

Theorem lem_to_peirce :
  excluded_middle -> peirce.
Proof.
  unfold excluded_middle. unfold peirce.
  intros LEM. 
  intros P Q.
  intros H.
  specialize LEM with (P := P).
  destruct LEM as [L|L].
  - apply L.
  - apply H.
    apply neg_p_to_everything.
    apply L.
Qed.

Theorem peirce_to_neg_elim :
  peirce -> double_negation_elimination.
Proof.
  unfold peirce. unfold double_negation_elimination.
  intros H.
  intros P Hneg.
  unfold not in Hneg.
  (* Try to apply H *)
  assert ((P -> False) -> P) as temp.
  { intros H'. apply Hneg in H'. destruct H'. }
  apply H in temp.
  apply temp.
Qed.

Theorem neg_elim_to_demorg_and_or :
  double_negation_elimination -> de_morgan_not_and_not.
Proof.
  unfold double_negation_elimination. unfold de_morgan_not_and_not.
  intros H.
  intros P Q.
  specialize H with (P := (P \/ Q)).
  intros H1.
  apply H.
  unfold not.
  intros H_neg_or.
  apply de_morgan_not_or in H_neg_or.
  (* H1 and H_neg_or *)
  contradiction.
Qed.

Lemma if_trans: forall (P Q R: Prop),
  (P -> Q) -> (Q -> R) -> (P -> R).
Proof.
  intros P Q R H1 H2 HP.
  apply H1 in HP.
  apply H2 in HP.
  apply HP.
Qed.

Theorem de_morg_and_or_to_imply_elim :
  de_morgan_not_and_not -> implies_to_or.
Proof.
  unfold de_morgan_not_and_not. unfold implies_to_or.
  intros H.
  intros P Q H1.
  specialize H with (P := ~P) (Q := Q).
  apply H.
  unfold not.
  intros [H2 H3].
  apply H2.
  apply (if_trans P Q False).
  - apply H1.
  - apply H3.
Qed. 

Lemma imply_obvious : forall P : Prop,
  P -> P.
Proof.
  intros P H.
  apply H.
Qed.

Theorem imply_elim_to_cm :
  implies_to_or -> consequentia_mirabilis.
Proof.
  unfold implies_to_or. unfold consequentia_mirabilis.
  intros H.
  intros P.
  specialize H with (P := P) (Q := P) as H1.
  assert (~P \/ P) as temp.
  { apply H1. apply imply_obvious. }
  intros H2.
  apply H in H2.
  destruct temp, H2.
  + unfold not in H2. apply H2 in H0. destruct H0.
  + apply H2.
  + apply H0.
  + apply H0.
Qed.

