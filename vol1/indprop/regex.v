Inductive reg_exp (T : Type) : Type :=
  | EmptySet
  | EmptyStr
  | Char (t : T)
  | App (r1 r2 : reg_exp T)
  | Union (r1 r2 : reg_exp T)
  | Star (r : reg_exp T).

Arguments EmptySet {T}.
Arguments EmptyStr {T}.
Arguments Char {T} _.
Arguments App {T} _ _.
Arguments Union {T} _ _.
Arguments Star {T} _.


Reserved Notation "s =~ re" (at level 80).

(* For list X *)
From LF.poly Require Import defns.

Inductive exp_match {T} : list T -> reg_exp T -> Prop :=
  | MEmpty : [] =~ EmptyStr
  | MChar x : [x] =~ (Char x)
  | MApp s1 re1 s2 re2
             (H1 : s1 =~ re1)
             (H2 : s2 =~ re2)
           : (s1 ++ s2) =~ (App re1 re2)
  | MUnionL s1 re1 re2
                (H1 : s1 =~ re1)
              : s1 =~ (Union re1 re2)
  | MUnionR s2 re1 re2
                (H2 : s2 =~ re2)
              : s2 =~ (Union re1 re2)
  | MStar0 re : [] =~ (Star re)
  | MStarApp s1 s2 re
                 (H1 : s1 =~ re)
                 (H2 : s2 =~ (Star re))
               : (s1 ++ s2) =~ (Star re)

  where "s =~ re" := (exp_match s re).

Fixpoint reg_exp_of_list {T} (l : list T) :=
  match l with
  | [] => EmptyStr
  | x :: l' => App (Char x) (reg_exp_of_list l')
  end.
Example reg_exp_ex4 : [1; 2; 3] =~ reg_exp_of_list [1; 2; 3].
Proof.
  simpl. apply (MApp [1]).
  { apply MChar. }
  apply (MApp [2]).
  { apply MChar. }
  apply (MApp [3]).
  { apply MChar. }
  apply MEmpty.
Qed.

(* For important results about lists *)
From LF.poly Require Import poly_list_exer.

 Lemma MStar1 :
  forall T s (re : reg_exp T) ,
    s =~ re ->
    s =~ Star re.
Proof.
  intros T s re H.
  rewrite <- (app_nil_r _ s).
  apply MStarApp.
  - apply H.
  - apply MStar0.
Qed.

Lemma EmptySet_is_empty : forall T (s : list T),
  ~ (s =~ EmptySet).
Proof.
  intros T s.
  unfold not.
  intros H. inversion H.
Qed.

Lemma MUnion' : forall T (s : list T) (re1 re2 : reg_exp T),
  s =~ re1 \/ s =~ re2 ->
  s =~ Union re1 re2.
Proof.
  intros T s re1 re2 [H | H].
  - apply MUnionL. apply H.
  - apply MUnionR. apply H.
Qed.

(* For In *)
From LF.logic Require Import prog_props.

Lemma MStar' : forall T (ss : list (list T)) (re : reg_exp T),
  (forall s, In s ss -> s =~ re) ->
  fold app ss [] =~ Star re.
Proof.
  intros T ss.
  induction ss.
  - intros re _.
    simpl. apply MStar0.
  - intros re H.
    simpl in H.
    simpl.
    apply MStarApp.
    + apply H. left. reflexivity.
    + apply IHss.
      intros s H1.
      apply H.
      right. apply H1.
Qed.


Definition EmptyStr' {T:Type} := @Star T (EmptySet).

Theorem EmptyStr_not_needed : forall T (l : list T),
  (l =~ @EmptyStr' T) <-> (l =~ @EmptyStr T).
Proof.
  intros T l.
  split.
  - intros H. inversion H.
    + apply MEmpty.
    + inversion H2. (* inversion any of H2 and H3 *)
  -  intros H. inversion H.
    apply MStar0.
Qed.

Fixpoint re_chars {T} (re : reg_exp T) : list T :=
  match re with
  | EmptySet => []
  | EmptyStr => []
  | Char x => [x]
  | App re1 re2 => re_chars re1 ++ re_chars re2
  | Union re1 re2 => re_chars re1 ++ re_chars re2
  | Star re => re_chars re
  end.

From Coq Require Import Setoids.Setoid.

Theorem in_re_match : forall T (s : list T) (re : reg_exp T) (x : T),
  s =~ re ->
  In x s ->
  In x (re_chars re).
Proof.
  intros T s re x Hmatch Hin.
  induction Hmatch
    as [| x'
        | s1 re1 s2 re2 Hmatch1 IH1 Hmatch2 IH2
        | s1 re1 re2 Hmatch IH | s2 re1 re2 Hmatch IH
        | re | s1 s2 re Hmatch1 IH1 Hmatch2 IH2].
  (* WORKED IN CLASS *)
  - (* MEmpty *)
    simpl in Hin. destruct Hin.
  - (* MChar *)
    simpl. simpl in Hin.
    apply Hin.
  - (* MApp *)
    simpl.
    (*  Something interesting happens in the MApp case. We obtain two induction
     *  hypotheses: One that applies when x occurs in s1 (which matches re1),
     *  and a second one that applies when x occurs in s2 (which matches re2).
     *  *)
    rewrite In_app_iff in *.
    destruct Hin as [Hin | Hin].
    + (* In x s1 *)
      left. apply (IH1 Hin).
    + (* In x s2 *)
      right. apply (IH2 Hin).
  - (* MUnionL *)
    simpl. rewrite In_app_iff.
    left. apply (IH Hin).
  - (* MUnionR *)
    simpl. rewrite In_app_iff.
    right. apply (IH Hin).
  - (* MStar0 *)
    destruct Hin.
  - (* MStarApp *)
    simpl.
    (* Here again we get two induction hypotheses, and they illustrate why we
     * need induction on evidence for exp_match, rather than induction on the
     * regular expression re: The latter would only provide an induction
     * hypothesis for strings that match re, which would not allow us to reason
     * about the case In x s2. *)
    rewrite In_app_iff in Hin.
    destruct Hin as [Hin | Hin].
    + (* In x s1 *)
      apply (IH1 Hin).
    + (* In x s2 *)
      apply (IH2 Hin).
Qed.

From LF.basics Require Import booleans.

Fixpoint re_not_empty {T : Type} (re : reg_exp T) : bool
  :=
  match re with
  | EmptySet => false
  | EmptyStr => true (* epsilon is also a string *)
  | Char x => true 
    (* any concat with the empty set is empty *)
  | App re1 re2 => andb (re_not_empty re1) (re_not_empty re2)
  | Union re1 re2 => orb (re_not_empty re1) (re_not_empty re2)
  | Star re => true (* star includes epsilon, so not empty *)
  end.

Lemma re_not_empty_correct : forall T (re : reg_exp T),
  (exists s, s =~ re) <-> re_not_empty re = true.
Proof.
  split.
  - intros H.
    destruct H.
    induction H.
    + reflexivity.
    + reflexivity.
    + simpl. rewrite -> IHexp_match1. rewrite ->IHexp_match2. reflexivity.
    + simpl. rewrite -> IHexp_match. reflexivity.
    + simpl. rewrite -> IHexp_match. rewrite -> orb_commutative. reflexivity.
    + reflexivity.
    + reflexivity.
  - induction re.
    + intros H. discriminate H.
    + intros _. exists []. apply MEmpty.
    + intros _. exists [t]. apply MChar.
    + intros H. simpl in H.
      destruct (re_not_empty re1), (re_not_empty re2). 
      { (* have to use assert to get true=true out *)
        assert (exists s : list T, s =~ re1) as H1.
        { apply IHre1. reflexivity. }
        assert (exists s : list T, s =~ re2) as H2.
        { apply IHre2. reflexivity. }
        destruct H1 as [s1 H1].
        destruct H2 as [s2 H2].
        exists (s1++s2).
        apply MApp.
        { apply H1. }
        { apply H2. }
      }
      {
        discriminate H.
      }
      {
        discriminate H.
      }
      {
        discriminate H.
      }
    + intros H. simpl in H.
      destruct (re_not_empty re1), (re_not_empty re2). 
      { (* have to use assert to get true=true out *)
        assert (exists s : list T, s =~ re1) as H1.
        { apply IHre1. reflexivity. }
        assert (exists s : list T, s =~ re2) as H2.
        { apply IHre2. reflexivity. }
        destruct H1 as [s1 H1].
        exists s1. apply MUnionL.
        apply H1.
      }
      {
        assert (exists s : list T, s =~ re1) as H1.
        { apply IHre1. reflexivity. }
        destruct H1 as [s1 H1].
        exists s1. apply MUnionL.
        apply H1.
      }
      {
        assert (exists s : list T, s =~ re2) as H2.
        { apply IHre2. reflexivity. }
        destruct H2 as [s2 H2].
        exists s2. apply MUnionR.
        apply H2.
      }
      { discriminate H. }
    + intros _. (* useless, always true *)
      destruct (re_not_empty re).
      { exists []. apply MStar0. }
      { exists []. apply MStar0. }
Qed.
