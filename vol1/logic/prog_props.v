From LF.poly Require Import defns.

Fixpoint In {A : Type} (x : A) (l : list A) : Prop :=
  match l with
  | [] => False
  | x' :: l' => x' = x \/ In x l'
  end.

Theorem In_map :
  forall (A B : Type) (f : A -> B) (l : list A) (x : A),
  In x l -> In (f x) (map f l).
Proof.
  intros A B f l x.
  induction l as [|x' l' IHl'].
  - (* l = nil, contradiction *)
    simpl. intros [].
  - (* l = x' :: l' *)
    simpl. intros [H | H].
    + rewrite H. left. reflexivity.
    + right. apply IHl'. apply H.
Qed.

Theorem In_map_iff :
  forall (A B : Type) (f : A -> B) (l : list A) (y : B),
  In y (map f l) <-> exists x, f x = y /\ In x l.
Proof.
  intros A B f l y. split.
  - induction l as [|x l' IHl'].
    + simpl. intros [].
    + simpl. intros [ H | H ].
      { exists x. split.
        { apply H. }
        { left. reflexivity. }
      }
      { apply IHl' in H. destruct H as [ x0 H ].
        destruct H as [ H1 H2 ].
        exists x0. split.
        { apply H1. }
        { right. apply H2. }
      }
  - intros [ x [H1 H2] ].
    (* Note that we can't apply In_map to H2 to do 
    forward reasoning, because not enough information
       there is for Coq to deduce B and f *)
    rewrite <- H1. apply In_map. apply H2.
Qed.

Theorem In_app_iff : forall A l l' (a:A),
  In a (l++l') <-> In a l \/ In a l'.
Proof.
  intros A l. induction l as [|a' l' IH].
  - split. 
    + simpl. intros H. right. apply H.
    + simpl. intros [ contra | H ].
      { contradiction. }
      { apply H. }
  - split. 
    + simpl. intros [H | H].
      { left. left. apply H. }
      { apply IH in H. destruct H as [H | H].
        - left. right. apply H.
        - right. apply H.
      }
    + simpl. intros [ [H1|H2] | H3 ].
      { left. apply H1. }
      { right. apply IH. left. apply H2. }
      { right. apply IH. right. apply H3. }
Qed.

(* P holds for x :: l iff P holds for x and P holds for all of l *)
Fixpoint All {T : Type} (P : T -> Prop) (l : list T) : Prop
  :=
  match l with
  | [] => True (* vacuously true *)
  | h :: t => P h /\ All P t 
  end.

Theorem All_In : 
  forall T (P : T -> Prop) (l : list T),
  (forall x, In x l -> P x) <->
    All P l.
Proof.
  intros T P l. induction l.
  - split. 
    + simpl. intros H. apply I.
    + simpl. intros _ x. contradiction.
  - split.
    + simpl. intros H. split.
      { apply H. left. reflexivity. }
      { 
        apply IHl. intros x0 H1. apply H.
        right. apply H1.
      }
    + simpl. intros [H1 H2].
      intros x0.
      intros [H3 | H3].
      { rewrite H3 in H1. apply H1. }
      { 
        apply IHl in H3. 
        { apply H3. }
        { apply H2. }
      }
Qed.

(* for even *)
From LF.basics Require Import numbers.

Definition combine_odd_even (Podd Peven : nat -> Prop) : nat -> Prop
  :=
  fun n : nat => if even n then Peven n else Podd n.

Theorem combine_odd_even_intro :
  forall (Podd Peven : nat -> Prop) (n : nat),
    (odd n = true -> Podd n) ->
    (odd n = false -> Peven n) ->
    combine_odd_even Podd Peven n.
Proof.
  intros Po Pe n.
  intros H1 H2.
  unfold combine_odd_even.
  destruct (even n) eqn:Hn.
  - simpl. apply H2. unfold odd. rewrite -> Hn. reflexivity.
  - simpl. apply H1. unfold odd. rewrite -> Hn. reflexivity.
Qed.

Theorem combine_odd_even_elim_odd :
  forall (Podd Peven : nat -> Prop) (n : nat),
    combine_odd_even Podd Peven n ->
    odd n = true ->
    Podd n.
Proof.
  intros Po Pe n H1 H2.
  unfold combine_odd_even in H1. 
  unfold odd in H2.
  destruct (even n) eqn:En.
  - simpl in H2. discriminate.
  - apply H1.
Qed.

Theorem combine_odd_even_elim_even :
  forall (Podd Peven : nat -> Prop) (n : nat),
    combine_odd_even Podd Peven n ->
    odd n = false ->
    Peven n.
Proof.
  intros Po Pe n H1 H2.
  unfold combine_odd_even in H1.
  unfold odd in H2.
  destruct (even n) eqn:En.
  - apply H1.
  - simpl in H2. discriminate.
Qed.
