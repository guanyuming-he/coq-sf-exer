From LF.poly Require Import defns
poly_list_exer.

Lemma cons_app_commutative :
  forall (X : Type) (a : X) (l1 l2 : list X),
  (a :: l1) ++ l2 = a :: (l1 ++ l2).
Proof.
  intros X a l1.
  destruct l1.
  - simpl. reflexivity.
  - simpl. intros l2. reflexivity.
Qed.

Theorem map_rev : forall (X Y : Type) (f : X -> Y) (l : list X),
  map f (rev l) = rev (map f l).
Proof.
  intros X Y f l.
  assert (
    forall (f : X -> Y) (l : list X) (x : X),
    map f (x :: l) = (f x) :: (map f l)
  ) as H.
  {
    intros f0 l0 x0.
    simpl. reflexivity.
  }
  assert (
    forall (a b : list X),
    map f (a ++ b) = (map f a) ++ (map f b)
  ) as H1.
  {
    intros a.
    induction a.
    - simpl. reflexivity.
    - intros b. rewrite -> cons_app_commutative. rewrite -> H. rewrite -> IHa. reflexivity.
  }
  induction l.
  - simpl. reflexivity.
  - rewrite -> H. simpl. rewrite -> H1. rewrite -> IHl. reflexivity.
Qed.

Fixpoint flat_map {X Y: Type} (f: X -> list Y) (l: list X) : list Y
  :=
  match l with 
  | nil => nil
  | h :: t =>
      (f h) ++ (flat_map f t)
  end.

Example test_flat_map1:
  flat_map (fun n => [n;n;n]) [1;5;4]
  = [1; 1; 1; 5; 5; 5; 4; 4; 4].
Proof. reflexivity. Qed.

Definition option_map {X Y : Type} (f : X -> Y) (xo : option X) : option Y 
  :=
  match xo with
  | None => None
  | Some x => Some (f x)
  end.

(** Exercise implicit_args *)
Module implicit_args.
Definition option_map' (X Y : Type) (f : X -> Y) (xo : option X) : option Y
  :=
  match xo with
  | None => None 
  | Some x => Some (f x)
  end.
End implicit_args.



