Inductive tree (X:Type) : Type :=
  | leaf (x : X)
  | node (t1 t2 : tree X).
Check tree_ind :
  forall 
    (X : Type)
    (P : (tree X -> Prop)),
    (forall (x : X), P (leaf X x)) ->
    (forall 
      (t1 : tree X)
      (_ : P t1)
      (t2 : tree X)
      (_ : P t2),
      P (node X t1 t2)
    )->
  forall t : tree X, P t.

(* Find an inductive definition that gives rise to the following induction
 * principle.*)

Inductive mytype (X : Type) : Type :=
  | constr1 (x : X)
  | constr2 (n : nat)
  | constr3 (m : mytype X) (n : nat).

Check mytype_ind :
    forall (X : Type) (P : mytype X -> Prop),
        (forall x : X, P (constr1 X x)) ->
        (forall n : nat, P (constr2 X n)) ->
        (forall m : mytype X, P m ->
           forall n : nat, P (constr3 X m n)) ->
        forall m : mytype X, P m. 


(* Find an inductive definition that gives rise to the following induction
 * principle.*)

Inductive foo (X Y : Type) : Type :=
  | bar (x : X)
  | baz (y : Y)
  | quux (f1 : nat -> foo X Y).

Check foo_ind :
forall (X Y : Type) (P : foo X Y -> Prop),
   (forall x : X, P (bar X Y x)) ->
   (forall y : Y, P (baz X Y y)) ->
   (forall f1 : nat -> foo X Y,
     (forall n : nat, P (f1 n)) -> P (quux X Y f1)) ->
   forall f2 : foo X Y, P f2.


(* Consider the following inductive definition: *)
Inductive foo' (X:Type) : Type :=
  | C1 (l : list X) (f : foo' X)
  | C2.
(* What induction principle will Coq generate for foo'? (Fill in the blanks,
 * then check your answer with Coq.) *) 

Check foo'_ind :
   forall (X : Type) (P : foo' X -> Prop),
      (forall (l : list X) (f : foo' X),
            P f ->
            P (C1 X l f)) ->
      (P (C2 X)) ->
     forall f : foo' X, P f.
