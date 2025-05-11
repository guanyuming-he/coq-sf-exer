Print nat_ind.

From LF.basics Require Import numbers.
From LF.indprop Require Import defns.
From LF.indprop Require Import evidence.

Lemma even_ev' : forall n : nat, 
  (even n = true -> ev n) /\ 
  (even (S n) = true -> ev (S n)).
Proof.
  induction n.
  - split.
    + intros _. apply ev_0.
    + intros contra. discriminate contra.
  - split.
    + destruct IHn as [_ H2]. exact H2.
    + intros H.  simpl in H.
      destruct IHn as [H1 _]. apply H1 in H.
      apply ev_SS. apply H.
Qed.


Notation "( x , y , .. , z )" := (pair .. (pair x y) .. z) : core_scope.
Inductive t_tree (X : Type) : Type :=
| t_leaf
| t_branch : (t_tree X * X * t_tree X) -> t_tree X.
Arguments t_leaf {X}.
Arguments t_branch {X}.

Check t_tree_ind.

Fixpoint reflect {X : Type} (t : t_tree X) : t_tree X :=
  match t with
  | t_leaf => t_leaf
  | t_branch (l, v, r) => t_branch (reflect r, v, reflect l)
  end.

Definition better_t_tree_ind_type : Prop
  :=
  forall (X : Type) (P : t_tree X -> Prop),
  (P (t_leaf)) ->
  (
    forall t : (t_tree X * X * t_tree X),
    match t with 
    | (t1, _, t2) => 
        P t1 -> P t2 -> P (t_branch t)
    end (* It turns out I must put everything above end *)  
  ) ->
  forall t : t_tree X, P t.

Definition better_t_tree_ind : better_t_tree_ind_type
  :=
  fun X P => fun P_leaf => fun P_branch =>
  fix f (t : t_tree X) :=
    match t with
    | t_leaf => P_leaf 
    | t_branch t =>
      match t with
      | (t1, x, t2) =>
          P_branch (t1, x, t2) (f t1) (f t2)
      end
    end.

Theorem reflect_involution : forall (X : Type) (t : t_tree X),
    reflect (reflect t) = t.
Proof. 
  intros X. apply better_t_tree_ind.
  - unfold reflect. reflexivity.
  - intros [[t1 x] t2].
    intros IH1 IH2.
    simpl. rewrite -> IH1. rewrite IH2.
    reflexivity.
Qed.

