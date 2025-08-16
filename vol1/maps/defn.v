From Coq Require Import Arith.
From Coq Require Import Bool.
From Coq Require Export Strings.String.
From Coq Require Import FunctionalExtensionality.
From Coq Require Import List.
Import ListNotations.
Set Default Goal Selector "!".


Definition total_map (A : Type) := string -> A.


Definition t_empty {A : Type} (v : A) : total_map A :=
  (fun _ => v).

Definition t_update {A : Type} (m : total_map A)
                    (x : string) (v : A) :=
  fun x' => if String.eqb x x' then v else m x'.

Definition examplemap :=
  t_update (t_update (t_empty false) "foo" true)
           "bar" true.

Notation "'_' '!->' v" := (t_empty v)
  (at level 100, right associativity).
Example example_empty := (_ !-> false).

Notation "x '!->' v ';' m" := (t_update m x v)
                              (at level 100, v at next level, right associativity).

Definition examplemap' :=
  ( "bar" !-> true;
    "foo" !-> true;
    _ !-> false
  ).

Lemma t_apply_empty : forall (A : Type) (x : string) (v : A),
  (_ !-> v) x = v.
Proof.
  intros A x v.
  reflexivity.
Qed.

Lemma t_update_eq : forall (A : Type) (m : total_map A) x v,
  (x !-> v ; m) x = v.
Proof.
  intros A m x v.
  unfold t_update.
  rewrite -> String.eqb_refl.
  reflexivity.
Qed.

Theorem t_update_neq : forall (A : Type) (m : total_map A) x1 x2 v,
  x1 <> x2 ->
  (x1 !-> v ; m) x2 = m x2.
Proof.
  intros A m x1 x2 v.
  intros H.
  unfold t_update.
  rewrite <- String.eqb_neq in H.
  rewrite -> H.
  reflexivity.
Qed.

Lemma t_update_shadow : forall (A : Type) (m : total_map A) x v1 v2,
  (x !-> v2 ; x !-> v1 ; m) = (x !-> v2 ; m).
Proof.
  intros A m x v1 v2.
  (* 
     Two functions are equal iff for all inputs their values are equal.
     To convert the goal to that form, apply functional_extensionality.
     I am pretty sure this is intended for us to use, as the package is imported. *)
  apply functional_extensionality.
  unfold t_update.
  intros x0. destruct (String.eqb x x0).
  - reflexivity.
  - reflexivity.
Qed.

Theorem t_update_same : forall (A : Type) (m : total_map A) x,
  (x !-> m x ; m) = m.
Proof.
  intros A m x.
  apply functional_extensionality.
  unfold t_update.
  intros x0. destruct (eqb_spec x x0). (* c.f. line 75 destruct, where e isn't generated. *)
  - rewrite -> e. reflexivity.
  - reflexivity.
Qed.

Theorem t_update_permute : forall (A : Type) (m : total_map A)
                                  v1 v2 x1 x2,
  x2 <> x1 ->
  (x1 !-> v1 ; x2 !-> v2 ; m)
  =
  (x2 !-> v2 ; x1 !-> v1 ; m).
Proof.
  intros A m v1 v2 x1 x2 H.
  apply functional_extensionality.
  unfold t_update.
  intros x. destruct (eqb_spec x1 x), (eqb_spec x2 x).
  - rewrite <- e in e0. apply H in e0. destruct e0. (* contra *)
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

(* Partial map section *)

Definition partial_map (A : Type) := total_map (option A).
Definition empty {A : Type} : partial_map A :=
  t_empty None.
Definition update {A : Type} (m : partial_map A)
           (x : string) (v : A) :=
  (x !-> Some v ; m).

Notation "x '|->' v ';' m" := (update m x v)
  (at level 100, v at next level, right associativity).

Notation "x '|->' v" := (update empty x v)
  (at level 100).
Definition examplepmap :=
  ("Church" |-> true ; "Turing" |-> false).

Lemma apply_empty : forall (A : Type) (x : string),
  @empty A x = None.
Proof.
  intros. unfold empty. rewrite t_apply_empty.
  reflexivity.
Qed.

Lemma update_eq : forall (A : Type) (m : partial_map A) x v,
  (x |-> v ; m) x = Some v.
Proof.
  intros. unfold update. rewrite t_update_eq.
  reflexivity.
Qed.

#[global] Hint Resolve update_eq : core.
Theorem update_neq : forall (A : Type) (m : partial_map A) x1 x2 v,
  x2 <> x1 ->
  (x2 |-> v ; m) x1 = m x1.
Proof.
  intros A m x1 x2 v H.
  unfold update.
  apply (t_update_neq (option A) _ _ _ (Some v) H).
Qed.

Lemma update_shadow : forall (A : Type) (m : partial_map A) x v1 v2,
  (x |-> v2 ; x |-> v1 ; m) = (x |-> v2 ; m).
Proof.
  intros A m x v1 v2. unfold update. 
  apply t_update_shadow.
Qed.

Theorem update_same : forall (A : Type) (m : partial_map A) x v,
  m x = Some v ->
  (x |-> v ; m) = m.
Proof.
  intros A m x v H. unfold update. 
  rewrite <- H.
  apply t_update_same.
Qed.

Theorem update_permute : forall (A : Type) (m : partial_map A)
                                x1 x2 v1 v2,
  x2 <> x1 ->
  (x1 |-> v1 ; x2 |-> v2 ; m) = (x2 |-> v2 ; x1 |-> v1 ; m).
Proof.
  intros A m x1 x2 v1 v2. unfold update.
  apply t_update_permute.
Qed.


Definition includedin {A : Type} (m m' : partial_map A) :=
  forall x v, m x = Some v -> m' x = Some v.


Lemma includedin_update : forall (A : Type) (m m' : partial_map A)
                                 (x : string) (vx : A),
  includedin m m' ->
  includedin (x |-> vx ; m) (x |-> vx ; m').
Proof.
  intros A m m' x vx H.
  unfold includedin.
  intros x0 v H1.
  destruct (eqb_spec x x0).
  - rewrite -> e in *. rewrite update_eq in H1.
    rewrite <- H1. apply update_eq.
  - rewrite -> (update_neq _ _ _ _ _ n) in H1.
    rewrite <- H1. rewrite -> (update_neq _ _ _ _ _ n).
    unfold includedin in H.
    rewrite -> H1. apply H in H1.
    apply H1.
Qed.

