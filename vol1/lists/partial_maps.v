From LF.induction Require Import eqb_refl. 
From LF.lists Require Import defns options.

Inductive id : Type :=
  | Id (n : nat).

Definition eqb_id (x1 x2 : id) :=
  match x1, x2 with
  | Id n1, Id n2 => n1 =? n2
  end.

Theorem eqb_id_refl : forall x, eqb_id x x = true.
Proof.
  intros x.
  destruct x. simpl. 
  rewrite eqb_refl.
  reflexivity.
Qed.

Inductive partial_map : Type :=
  | empty
  | record (i : id) (v : nat) (m : partial_map).

Definition update (d : partial_map)
                  (x : id) (value : nat)
                  : partial_map :=
  record x value d.

Fixpoint find (x : id) (d : partial_map) : natoption :=
  match d with
  | empty =>  None
  | record y v d' =>  if eqb_id x y
                     then Some v
                     else find x d'
  end.

Theorem update_eq :
  forall (d : partial_map) (x : id) (v: nat),
    find x (update d x v) = Some v.
Proof.
  intros d x v.
  simpl.  rewrite -> eqb_id_refl. reflexivity.
Qed.

Theorem update_neq :
  forall (d : partial_map) (x y : id) (o: nat),
  eqb_id x y = false -> find x (update d y o) = find x d.
Proof.
  intros d x y o.
  intros H. simpl. rewrite -> H.
  reflexivity.
Qed.
