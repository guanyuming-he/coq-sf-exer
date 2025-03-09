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

Theorem combine_split : forall X Y (l : list (X * Y)) l1 l2,
  split l = (l1, l2) ->
  combine l1 l2 = l.
Proof.
  intros X Y l.
  induction l.
  - simpl. intros l1 l2 H.
    injection H as H1.
    rewrite <- H1. rewrite <- H.
    reflexivity.
  - intros l1 l2.
    simpl.
    destruct x.
    { 
      simpl. 
      destruct (split l).
      {
        simpl. 
        intros H.
        injection H as H1 H2.
        destruct l1.
        { discriminate. }
        { destruct l2.
          { discriminate. }
          { injection H1 as H11 H12.
            injection H2 as H21 H22.
            simpl.
            rewrite -> IHl.
            { rewrite H11. rewrite H21. reflexivity. }
            { rewrite H12. rewrite H22. reflexivity. }
          }
        }
      }
    }
Qed.

Theorem bool_fn_applied_thrice :
  forall (f : bool -> bool) (b : bool),
  f (f (f b)) = f b.
Proof.
  intros f b.
  destruct b eqn:Eb.
  - destruct (f true) eqn:Ef0, (f false) eqn:Ef1.
    + rewrite -> Ef0. rewrite -> Ef0. reflexivity.
    + rewrite -> Ef0. rewrite -> Ef0. reflexivity.
    + apply Ef0.
    + apply Ef1.
  - destruct (f true) eqn:Ef0, (f false) eqn:Ef1.
    + rewrite -> Ef0. rewrite -> Ef0. reflexivity.
    + rewrite -> Ef1. rewrite -> Ef1. reflexivity.
    + rewrite -> Ef0. rewrite -> Ef1. reflexivity.
    + rewrite -> Ef1. rewrite -> Ef1. reflexivity.
Qed.
