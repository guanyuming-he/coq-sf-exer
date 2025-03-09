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
   we must here require l1 and l2 non-empty to ensure
   split is the inverse for combine.
 *)
Definition split_combine_statement : Prop
  :=
  forall (X Y : Type) (l : list (X * Y)) (l1 : list X) (l2 : list Y),
  l1 <> [] -> l2 <> [] -> combine l1 l2 = l -> split l = (l1, l2). 

Theorem split_combine : split_combine_statement.
Proof.
  intros X Y l.
  induction l as [ | h t] eqn:Hl.
  - simpl. intros l1 l2. destruct l1 eqn:Hl1, l2 eqn:Hl2.
    + simpl. reflexivity.
    + simpl. contradiction.
    + simpl. contradiction.
    + simpl. discriminate.
  - simpl. intros l1 l2. destruct l1 as [ | h1 t1] eqn:Hl1, l2 as [ | h2 t2] eqn:Hl2.
    + simpl. discriminate.
    + simpl. contradiction.
    + simpl. contradiction.
    + intros H1 H2 H3.
      simpl in H3. injection H3 as H4 H5.
      destruct t1 as [| h1' t1'] eqn:Ht1, t2 as [| h2' t2'] eqn:Ht2.
      { simpl in H5. rewrite <- H5. simpl.
        destruct h. 
        injection H4 as H6 H7. rewrite -> H6. rewrite -> H7.
        reflexivity.
      } 
      { simpl in H5. rewrite <- H5. simpl.
        destruct h.         injection H4 as H6 H7. rewrite -> H6. rewrite -> H7.
        reflexivity.
      } 

      apply IHl in H5.
      { 
        rewrite -> H5. simpl. destruct x. 
        injection H4 as H6 H7. rewrite -> H6. rewrite H7.
        reflexivity. 
      }
      { 
