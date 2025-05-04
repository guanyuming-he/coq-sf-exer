Theorem plus_one_r' : forall n:nat,
  n + 1 = S n.
Proof.
  apply nat_ind.
  - reflexivity.
  - intros n H.
    simpl.
    rewrite -> H.
    reflexivity.
Qed.

(* Write out the induction principle that Coq will generate for the following
 * datatype *)
Inductive rgb : Type :=
  | red
  | green
  | blue.
Check rgb_ind :
  forall P : rgb -> Prop,
    P red ->
    P green ->
    P blue ->
    (forall c : rgb, P c).

Inductive booltree : Type :=
  | bt_empty
  | bt_leaf (b : bool)
  | bt_branch (b : bool) (t1 t2 : booltree).

(* What is the induction principle for booltree? Of course you could
   ask Coq, but try not to do that. Instead, write it down yourself on
   paper. Then look at the definition of booltree_ind_type, below.
   It has three missing pieces, which are provided by the definitions
   in between here and there. Fill in those definitions based on what
   you wrote on paper. *)
Definition booltree_property_type : Type := booltree -> Prop.
  
Definition base_case (P : booltree_property_type) : Prop :=
  P bt_empty.

Definition leaf_case (P : booltree_property_type) : Prop :=
  forall b : bool, P (bt_leaf b).

Definition branch_case (P : booltree_property_type) : Prop :=
  forall 
    (b : bool)
    (t1 : booltree)
    (_ : P t1)
    (t2 : booltree)
    (_ : P t2),
    P (bt_branch b t1 t2). 

Definition booltree_ind_type :=
  forall (P : booltree_property_type),
    base_case P ->
    leaf_case P ->
    branch_case P ->
    forall (b : booltree), P b.

Theorem booltree_ind_type_correct : booltree_ind_type.
Proof.
  exact booltree_ind.
Qed.

(* Here is an induction principle for a toy type:
  forall P : Toy -> Prop,
    (forall b : bool, P (con1 b)) ->
    (forall (n : nat) (t : Toy), P t -> P (con2 n t)) ->
    forall t : Toy, P t
Give an Inductive definition of Toy, such that the induction principle Coq
   generates is that given above:
 *)

Inductive Toy : Type :=
  | con1 (b : bool)
  | con2 (n : nat) (t : Toy).

Theorem Toy_correct : exists f g,
  forall P : Toy -> Prop,
    (forall b : bool, P (f b)) ->
    (forall (n : nat) (t : Toy), P t -> P (g n t)) ->
    forall t : Toy, P t.
Proof.
  exists con1, con2.
  exact Toy_ind.
Qed.
