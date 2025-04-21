(* For list X *)
From LF.poly Require Import defns.

Module EqualityPlayground.

Inductive eq {X:Type} : X -> X -> Prop :=
  | eq_refl : forall x, eq x x.
Notation "x == y" := (eq x y)
                       (at level 70, no associativity)
                     : type_scope.

Lemma four: 2 + 2 == 1 + 3.
Proof.
  apply eq_refl.
Qed.

Definition four' : 2 + 2 == 1 + 3 :=
  eq_refl 4.
Definition singleton : forall (X:Type) (x:X), []++[x] == x::[] :=
  fun (X:Type) (x:X) => eq_refl [x].

Theorem eq_add' : forall (n1 n2 : nat), n1 == n2 -> (S n1) == (S n2).
Proof.
  intros n1 n2 Heq.
  Fail rewrite Heq. (* doesn't work for _our_ == relation *)
  destruct Heq as [n]. (* n1 and n2 replaced by n in the goal! *)
  Fail reflexivity. (* doesn't work for _our_ == relation *)
  apply eq_refl.
Qed.

Definition eq_cons : forall (X : Type) (h1 h2 : X) (t1 t2 : list X),
    h1 == h2 -> t1 == t2 -> h1 :: t1 == h2 :: t2
    :=
    fun X h1 h2 t1 t2 (Hh : h1==h2) (Ht : t1==t2) =>
    match Hh with
    | eq_refl h =>
      match Ht with 
      | eq_refl t =>
        eq_refl (h::t)
      end
    end.

Lemma equality__leibniz_equality : forall (X : Type) (x y: X),
  x == y -> forall (P : X -> Prop), P x -> P y.
Proof.
  intros X x y Heq.
  intros P HPx.
  destruct Heq as [a].
  apply HPx.
Qed.

Definition equality__leibniz_equality_term : forall (X : Type) (x y: X),
    x == y -> forall P : (X -> Prop), P x -> P y
    :=
    fun X x y Heq P =>
    match Heq with 
    (* It is indeed curious that, if we don't listen to the hint to match
     * immediately when we can but instead after we introduced HPx,
       then giving HPx won't work.
       However, introducing P or not does not affect this.
     *)
    | eq_refl a => fun HPx => HPx
    end.

Lemma leibniz_equality__equality : forall (X : Type) (x y: X),
  (forall P:X->Prop, P x -> P y) -> x == y.
Proof.
  (* The key is letting P a := x == a. *)
  intros X x y H.
  apply (H (fun a => x == a)).
  apply eq_refl.
Qed.

End EqualityPlayground.
