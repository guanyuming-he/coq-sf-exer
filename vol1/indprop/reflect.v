(* bool *)
From LF.basics Require Import booleans.
(* eqb_eq *)
From LF.logic Require Import decidable.

Inductive reflect (P : Prop) : bool -> Prop :=
  | ReflectT (H : P) : reflect P true
  | ReflectF (H : ~ P) : reflect P false.

Theorem iff_reflect : forall P b, (P <-> b = true) -> reflect P b.
Proof.
  (* WORKED IN CLASS *)
  intros P b H. destruct b eqn:Eb.
  - apply ReflectT. rewrite H. reflexivity.
  - apply ReflectF. rewrite H. intros H'. discriminate.
Qed.

Theorem reflect_iff : forall P b, reflect P b -> (P <-> b = true).
Proof.
  intros P b H.
  destruct b.
  - split. 
    + intros _. reflexivity.
    + intros _. inversion H. apply H0.
  - split.
    + inversion H.
      intros H1. contradiction.
    + intros contra. discriminate contra.
Qed.

(* For numbers *)
From LF.basics Require Import numbers.

Lemma eqbP : forall n m, reflect (n = m) (n =? m).
Proof.
  intros n m. apply iff_reflect. rewrite eqb_eq. reflexivity.
Qed.

(* For list *)
From LF.poly Require Import defns.
(* For In *)
From LF.logic Require Import prog_props.

Theorem filter_not_empty_In' : forall n l,
  filter (fun x => n =? x) l <> [] ->
  In n l.
Proof.
  intros n l. induction l as [|m l' IHl'].
  - (* l =  *)
    simpl. intros H. apply H. reflexivity.
  - (* l = m :: l' *)
    simpl. destruct (eqbP n m) as [EQnm | NEQnm].
    + (* n = m *)
      intros _. rewrite EQnm. left. reflexivity.
    + (* n <> m *)
      intros H'. right. apply IHl'. apply H'.
Qed.


Fixpoint count n l :=
  match l with
  | [] => 0
  | m :: l' => (if n =? m then 1 else 0) + count n l'
  end.
Theorem eqbP_practice : forall n l,
  count n l = 0 -> ~(In n l).
Proof.
  intros n l Hcount. induction l as [| m l' IHl'].
  - unfold not. intros contra. inversion contra.
  - simpl in Hcount.
    destruct (eqbP n m) as [EQnm | NEQnm].
    + discriminate Hcount.
    + unfold not. simpl in Hcount. apply IHl' in Hcount.
      simpl. intros [H | H].
      * rewrite -> H in NEQnm. contradiction.
      * apply Hcount in H. destruct H.
Qed.



