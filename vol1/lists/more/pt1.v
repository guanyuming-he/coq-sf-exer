From LF.lists Require Import defns list_funs.

Theorem app_nil_r : forall l : natlist,
  l ++ [] = l.
Proof.
  intros l.
  induction l.
  - reflexivity.
  - simpl. rewrite -> IHl. reflexivity.
Qed.


Theorem rev_app_distr: forall l1 l2 : natlist,
  rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
  intros l1.
  induction l1.
  - simpl. intros l2. rewrite -> app_nil_r. reflexivity.
  - intros l2. simpl. rewrite -> IHl1. rewrite -> app_assoc. reflexivity.
Qed.

Theorem rev_involutive : forall l : natlist,
  rev (rev l) = l.
Proof.
  intros l.
  induction l.
  - simpl. reflexivity.
  - simpl. rewrite -> rev_app_distr. rewrite -> IHl. reflexivity.
Qed.

Theorem app_assoc4 : forall l1 l2 l3 l4 : natlist,
  l1 ++ (l2 ++ (l3 ++ l4)) = ((l1 ++ l2) ++ l3) ++ l4.
Proof.
  (** 
     well, in general, not just for natlists, we apply the normal associativity
     twice to get this.
  *)
  intros l1 l2 l3 l4.
  rewrite -> app_assoc.
  rewrite -> app_assoc.
  reflexivity.
Qed.

Lemma nonzeros_app : forall l1 l2 : natlist,
  nonzeros (l1 ++ l2) = (nonzeros l1) ++ (nonzeros l2).
Proof.
  intros l1.
  induction l1.
  - simpl. reflexivity.
  - simpl. destruct n.
    + simpl. exact IHl1.
    + simpl. intros l2. rewrite -> IHl1. reflexivity.
Qed.



Fixpoint eqblist (l1 l2 : natlist) : bool
  :=
  match l1 with 
  | nil => 
      match l2 with
      | nil => true
      | _ :: _ => false 
      end
  | h :: t =>
      match l2 with
      | nil => false 
      | h' :: t' =>
        if h =? h' then eqblist t t'
        else false 
      end
   end.
Example test_eqblist1 :
  (eqblist nil nil = true).
Proof. reflexivity. Qed.

Example test_eqblist2 :
  eqblist [1;2;3] [1;2;3] = true.
Proof. reflexivity. Qed.

Example test_eqblist3 :
  eqblist [1;2;3] [1;2;4] = false.
Proof. reflexivity. Qed.

Theorem eqblist_refl : forall l:natlist,
  true = eqblist l l.
Proof.
  intros l.
  induction l.
  - reflexivity.
  - simpl. assert (forall n: nat, n =? n = true).
    { intros n0. induction n0. 
      + reflexivity.
      + simpl. rewrite -> IHn0. reflexivity.
    }
    rewrite -> H. apply IHl.
Qed.
