(* for double *)
From LF.induction Require Import double_plus.

Definition Even x := exists n : nat, x = double n.

Lemma four_is_Even : Even 4.
Proof.
  unfold Even. exists 2. reflexivity.
Qed.

Theorem dist_not_exists : forall (X:Type) (P : X -> Prop),
  (forall x, P x) -> ~ (exists x, ~ P x).
Proof.
  intros X P.
  intros H.
  unfold not.
  intros [ x Hx ].
  apply Hx. apply H.
Qed.

Theorem dist_exists_or : forall (X:Type) (P Q : X -> Prop),
  (exists x, P x \/ Q x) <-> (exists x, P x) \/ (exists x, Q x).
Proof.
  intros X P Q.
  split.
  - intros [ x [HP | HQ] ].
    + left. exists x. apply HP.
    + right. exists x. apply HQ.
  - intros [ [x HP] | [x HQ] ].
    + exists x. left. apply HP.
    + exists x. right. apply HQ.
Qed.

(* for <=? *)
From LF.basics Require Import numbers.

(* The following two theorems provide an alternative
   definition of leb: leb n m iff exists x, m = n+x.
*)

Theorem leb_plus_exists : forall n m : nat, 
  n <=? m = true -> exists x : nat, m = n+x.
Proof.
  intros n.
  induction n as [| n' IHn'].
  - simpl. intros m H. exists m. reflexivity.
  - intros m H. destruct m as [| m'].
    + discriminate.
    + simpl in H. apply IHn' in H. destruct H as [x].
      exists x. rewrite H. reflexivity.
Qed.

Theorem plus_exists_leb : 
  forall n m, (exists x, m = n+x) -> n <=? m = true.
Proof.
  intros n m.
  (* destruct exists to get x, and destruct x to get 0 | S x' *)
  intros [ [| x'] ].
  - rewrite H. 
    (* If I don't use assert to create a sub context here,
       induction will fuck up the inductive hypothesis, as if 
       I used induction ... as [...] eqn:... *)
    assert (forall n : nat, (n <=? n+0) = true) as H1.
    {
      intros n0.
      induction n0.
      { reflexivity. }
      { simpl. apply IHn0. }
    }
    apply H1.
  - rewrite H.
    (* If I don't use assert to create a sub context here,
       induction will fuck up the inductive hypothesis, as if 
       I used induction ... as [...] eqn:... *)
    assert (forall n m : nat, (n <=? n + S m) = true) as H2.
    {
      intros n0.
      induction n0.
      { reflexivity. }
      { simpl. apply IHn0. }
    }
    apply H2.
Qed.

 
