From LF.basics Require Import numbers.

Theorem eqb_sym : forall (n m : nat),
  (n =? m) = (m =? n).
Proof.
  intros n.
  induction n.
  - simpl. intros m. destruct m.
+ reflexivity.
    + reflexivity.
  - simpl. intros m. destruct m.
    + reflexivity.
    + simpl. apply IHn.
Qed.

(**
  * Informal proof of the above theorem.
    We induct on n.
   - When n = 0, it follows by definition.
   - Suppose inductively it works for n, we now consider
    S n.
    To judge if S n =? m or not, we have to see if m equals some S m',
    that is, if m != 0 or not.
    + if m = 0, then by definition we have S n =? 0 = 0 =? S n = false.
    + if m = S m', then by definition we have S n =? m = n =? m' and
      m =? S n = m' =? n. Apply the inductive hypothesis solves the case.

  We can now close the induction
*)

Theorem eqb_trans : forall n m p,
  n =? m = true ->
  m =? p = true ->
  n =? p = true.
Proof.
  intros n m.
  generalize dependent n.
  induction m.
  - simpl. intros n p.
    destruct n eqn:En, p eqn:Ep.
     reflexivity.
    + simpl. discriminate.
    + simpl. discriminate.
    + simpl. discriminate.
  - simpl. intros n p.
    destruct n eqn:En, p eqn:Ep.
    + simpl. discriminate.
    + simpl. discriminate.
    + simpl. discriminate.
    + simpl. apply IHm.
Qed.

From LF.poly Require Import defns.
Fixpoint split {X Y : Type} (l : list (X*Y))
   : (list X) * (list Y) :=
  match l with
  | [] => ([], [])
  | (x, y) :: t =>
      match split t with
      | (lx, ly) => (x :: lx, y :: ly)
      end
  end.

(* different from the previous combine_split,
   we must here require l1 and l2 have the same length for
   split to be the inverse for combine.
 *)
Definition split_combine_statement : Prop
  :=
  forall 
  (X Y : Type) (l : list (X*Y)) (l1 : list X) (l2 : list Y),
  length l1 = length l2 -> combine l1 l2 = l -> split l = (l1, l2).  

Theorem split_combine : split_combine_statement.
Proof.
  intros X Y l.
  induction l as [| h t IHl].
  - destruct l1 as [| h1 t1] eqn:El1, l2 as [| h2 t2] eqn:El2.
    + simpl. reflexivity.
    + simpl. discriminate.
    + simpl. discriminate.
    + simpl. discriminate.
  - destruct l1 as [| h1 t1] eqn:El1, l2 as [| h2 t2] eqn:El2.
    + simpl. discriminate.
    + simpl. discriminate.
    + simpl. discriminate.
    + simpl. 
      intros H. injection H as Ht1t2.
      intros H1. injection H1 as H2 H3.
      apply IHl in Ht1t2.
      { 
        rewrite -> Ht1t2. destruct h. 
        injection H2 as H4 H5.
        rewrite -> H4. rewrite -> H5.
        reflexivity.
      }
      { apply H3. }
Qed.

From LF.poly Require Import filter.

Theorem filter_exercise : 
  forall 
  (X : Type) (test : X -> bool)
  (x : X) (l lf : list X),
    filter test l = x :: lf ->
    test x = true.
Proof.
  intros X test x l.
  generalize dependent x.
  induction l.
  - intros x lf. simpl. discriminate.
  - intros x0 lf. simpl.
    destruct (test x) eqn:Eh.
    + intros H. injection H as H1 H2.
      rewrite -> H1 in Eh. apply Eh.
    + intros H. apply IHl in H. apply H.
Qed.

(* similar to filter *)
Fixpoint forallb 
  {X : Type} 
  (test : X -> bool) (l : list X)
  : bool
  :=
  match l with
  | [] => true
  | h :: t =>
      if test h then forallb test t 
      else false
  end.

Fixpoint existsb 
  {X : Type} 
  (test : X -> bool) (l : list X)
  : bool
  :=
  match l with
  | [] => false
  | h :: t =>
      if test h then true
      else existsb test t
  end.

Example test_forallb_1 : forallb odd [1;3;5;7;9] = true.
Proof. reflexivity. Qed.
Example test_forallb_2 : forallb negb [false;false] = true.
Proof. reflexivity. Qed.
Example test_forallb_3 : forallb even [0;2;4;5] = false.
Proof. reflexivity. Qed.
Example test_forallb_4 : forallb (eqb 5) [] = true.
Proof. reflexivity. Qed.

Example test_existsb_1 : existsb (eqb 5) [0;2;3;6] = false.
Proof. reflexivity. Qed.
Example test_existsb_2 : existsb (andb true) [true;true;false] = true.
Proof. reflexivity. Qed.
Example test_existsb_3 : existsb odd [1;0;0;0;0;3] = true.
Proof. reflexivity. Qed.
Example test_existsb_4 : existsb even [] = false.
Proof. reflexivity. Qed.

Definition existsb' {X : Type} (test : X -> bool) (l : list X) : bool
  :=
  negb (forallb (fun (x : X) => negb (test x)) l).

Theorem existsb_existsb' : forall (X : Type) (test : X -> bool) (l : list X),
  existsb test l = existsb' test l.
Proof. 
  intros X test l.
  generalize dependent test.
  induction l.
  - simpl. intros test. reflexivity.
  - simpl. intros test. destruct (test x) eqn:Htest.
    + simpl. unfold existsb'. simpl. 
      rewrite -> Htest. simpl. reflexivity.
    + simpl. unfold existsb'. simpl.
      rewrite -> Htest. simpl. 
      (* at this step, note the RHS has become the unfolded existsb' test l *)
      apply IHl.
Qed.
