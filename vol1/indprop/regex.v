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


Lemma star_app: forall T (s1 s2 : list T) (re : reg_exp T),
  s1 =~ Star re ->
  s2 =~ Star re ->
  s1 ++ s2 =~ Star re.
Proof.
  intros T s1 s2 re H1.
  remember (Star re) as re' eqn:Eq.
  induction H1
  as [|x'|s1 re1 s2' re2 Hmatch1 IH1 Hmatch2 IH2
      |s1 re1 re2 Hmatch IH|re1 s2' re2 Hmatch IH
      |re''|s1 s2' re'' Hmatch1 IH1 Hmatch2 IH2].
  - (* MEmpty *) discriminate.
  - (* MChar *) discriminate.
  - (* MApp *) discriminate.
  - (* MUnionL *) discriminate.
  - (* MUnionR *) discriminate.
  - intros H. simpl.
    apply H.
  - intros H.
    apply (IH2 Eq) in H.
    rewrite <- app_assoc.
    apply (MStarApp _ _ _ Hmatch1 H).
Qed.


Lemma MStar'' : forall T (s : list T) (re : reg_exp T),
  s =~ Star re ->
  exists ss : list (list T),
    s = fold app ss []
    /\ forall s', In s' ss -> s' =~ re.
Proof.
  intros T s re H.
  remember (Star re) as re'.
  induction H.
  - exists [].
    split.
    + reflexivity.
    + intros s' contra.
      destruct contra.
  - (* Char x = Star re is impossible. Star is either only containing epsilon 
      or is infinite.*)
    inversion Heqre'.
  - inversion Heqre'. (* Impossible *)
  - inversion Heqre'. (* Impossible *)
  - inversion Heqre'. (* Impossible *)
  - exists []. split.
    + reflexivity.
    + intros s' contra. destruct contra.
  - destruct (IHexp_match2 Heqre') as [ss [H1 H2]].
    injection Heqre' as Heq.
    rewrite -> Heq in *.
    (* Because s2 = fold app ss, to satisfy left,
       ss0 must equal to s1 :: ss. *)
    exists (s1::ss).
    split.
    + simpl. rewrite -> H1. reflexivity.
    + intros s' H'.
      simpl in H'.
      destruct H' as [H'|H'].
      { rewrite <- H'. apply H. }
      { apply H2. apply H'. }
Qed.

(* For le *)
From LF.indprop Require Import defns.
(* For properties about le *)
From LF.indprop Require Import indrela.

Module Pumping.

Fixpoint pumping_constant {T} (re : reg_exp T) : nat :=
  match re with
  | EmptySet => 1
  | EmptyStr => 1
  | Char _ => 2
  | App re1 re2 =>
      pumping_constant re1 + pumping_constant re2
  | Union re1 re2 =>
      pumping_constant re1 + pumping_constant re2
  | Star r => pumping_constant r
  end.


Lemma pumping_constant_ge_1 :
  forall T (re : reg_exp T),
    pumping_constant re >= 1.
Proof.
  intros T re. induction re.
  - (* EmptySet *)
    simpl. apply le_n.
  - (* EmptyStr *)
    apply le_n.
  - (* Char *)
    apply le_S. apply le_n.
  - (* App *)
    simpl.
    apply le_trans with (n:=pumping_constant re1).
    apply IHre1. apply le_plus_l.
  - (* Union *)
    simpl.
    apply le_trans with (n:=pumping_constant re1).
    apply IHre1. apply le_plus_l.
  - (* Star *)
    simpl. apply IHre.
Qed.

Lemma pumping_constant_0_false :
  forall T (re : reg_exp T),
    pumping_constant re = 0 -> False.
Proof.
  intros T re H.
  assert (Hp1 : pumping_constant re >= 1).
  { apply pumping_constant_ge_1. }
  rewrite H in Hp1. inversion Hp1.
Qed.

Fixpoint napp {T} (n : nat) (l : list T) : list T :=
  match n with
  | 0 => []
  | S n' => l ++ napp n' l
  end.

Lemma napp_plus: forall T (n m : nat) (l : list T),
  napp (n + m) l = napp n l ++ napp m l.
Proof.
  intros T n m l.
  induction n as [|n IHn].
  - reflexivity.
  - simpl. rewrite IHn, app_assoc. reflexivity.
Qed.

Lemma napp_star :
  forall T m s1 s2 (re : reg_exp T),
    s1 =~ re -> s2 =~ Star re ->
    napp m s1 ++ s2 =~ Star re.
Proof.
  intros T m s1 s2 re Hs1 Hs2.
  induction m.
  - simpl. apply Hs2.
  - simpl. rewrite <- app_assoc.
    apply MStarApp.
    + apply Hs1.
    + apply IHm.
Qed.

(* My own lemma *)
Lemma not_pc_le_0 : forall T (re : reg_exp T),
  ~ (pumping_constant re <= 0).
Proof.
  intros T re.
  unfold not.
  intros H.
  (* try to get 0 >= with le_trans *)
  (* turn ge into le to use le_trans *)
  assert (1 <= pumping_constant re) as H0.
  { apply pumping_constant_ge_1. }
  (* Here is 1 <= 0 *)
  assert (1 <= 0) as contra.
  { apply (le_trans _ _ _ H0 H). }
  inversion contra.
Qed.

(* My own lemma *)
Lemma MStarStarApp : forall T (re : reg_exp T) (s1 s2 : list T),
  s1 =~ Star re -> s2 =~ Star re -> s1 ++ s2 =~ Star re.
Proof.
  intros T re s1 s2 H1.
  remember (Star re) as re'.
  induction H1.
  - intros H. simpl. apply H.
  - discriminate Heqre'.
  - discriminate Heqre'.
  - discriminate Heqre'.
  - discriminate Heqre'.
  - intros H. simpl. apply H.
  - injection Heqre' as Heq.
    rewrite -> Heq in *.
    (* Extract Star re = Star re out of IHexp_match2 *)
    assert (s2 =~ Star re -> s0 ++ s2 =~ Star re) as IH2.
    { apply IHexp_match2. reflexivity. }
    intros H2.
    apply IH2 in H2.
    rewrite <- app_assoc.
    apply (MStarApp s1 (s0++s2) _).
    { apply H1_. }
    { apply H2. }
Qed.

(* Immediate corollary of my own lemma *)
Corollary MStarNApp : forall T (re : reg_exp T) (s1 : list T),
  s1 =~ Star re -> forall m : nat, napp m s1 =~ Star re.
Proof.
  intros T re s1 H.
  intros m. induction m.
  - simpl. apply MStar0.
  - simpl. 
    apply (MStarStarApp T re s1 (napp m s1)).
    + apply H.
    + apply IHm.
Qed.

Lemma weak_pumping : forall T (re : reg_exp T) s,
  s =~ re ->
  pumping_constant re <= length s ->
  exists s1 s2 s3,
    s = s1 ++ s2 ++ s3 /\
    s2 <> [] /\
    forall m, s1 ++ napp m s2 ++ s3 =~ re.
Proof.
  intros T re s Hmatch.
  induction Hmatch
    as [ | x | s1 re1 s2 re2 Hmatch1 IH1 Hmatch2 IH2
       | s1 re1 re2 Hmatch IH | s2 re1 re2 Hmatch IH
       | re | s1 s2 re Hmatch1 IH1 Hmatch2 IH2 ].
  - (* MEmpty *)
    simpl. intros contra. inversion contra.
  - intros contra. simpl in contra.
    inversion contra. inversion H1.
  - intros H.
    simpl in H. rewrite -> app_length in H.
    apply plus_le_cases in H.
    destruct H as [H | H].
    + apply IH1 in H.
      destruct H as [s0 [s3 [s4]]].
      exists s0, s3, (s4++s2).
      destruct H as [H1 H2].
      split.
      { 
        rewrite -> H1. rewrite <- app_assoc with 
        (l := s0) (m := (s3++s4)) (n := s2). rewrite <- app_assoc.
        reflexivity. 
      }
      {
        destruct H2 as [H2 H3].
        split.
        { apply H2. }
        { 
          intros m. 
          rewrite -> app_assoc with 
            (l := napp m s3) (m := s4) (n := s2).
          rewrite -> app_assoc with 
            (l := s0) (m := napp m s3 ++ s4) (n := s2).
          apply (MApp (s0 ++ napp m s3 ++ s4) re1 s2 re2).
          { apply H3. }
          { apply Hmatch2. }
        }
      }
    + apply IH2 in H. 
      destruct H as [s0 [s3 [s4]]].
      exists (s1++s0), s3, s4.
      destruct H as [H1 H2].
      split.
      { 
        rewrite -> H1. rewrite -> app_assoc.
        reflexivity.
      }
      {
        destruct H2 as [H2 H3].
        split.
        { apply H2. }
        {
          intros m. rewrite <- app_assoc.
          apply (MApp s1 re1 _ re2).
          { apply Hmatch1. }
          { apply H3. }
        }
      }
  - intros H. simpl in H.
    apply plus_le in H.
    destruct H as [H1 H2].
    apply IH in H1.
    destruct H1 as [s2 [s3 [s4]]].
    destruct H as [H3 [H4 H5]].
    exists s2, s3, s4.
    split.
    { apply H3. }
    { split.
      { apply H4. }
      { 
        intros m. 
        apply (MUnionL (s2 ++ napp m s3 ++ s4)).
        apply H5.
      }
    }
    (* basically the same as the above one, just swap 1 and 2 and L and R 
       in a few places. *)
  - intros H. simpl in H.
    apply plus_le in H.
    destruct H as [H1 H2].
    apply IH in H2.
    destruct H2 as [s1 [s3 [s4]]].
    destruct H as [H3 [H4 H5]].
    exists s1, s3, s4.
    split.
    { apply H3. }
    { split.
      { apply H4. }
      { 
        intros m. 
        apply (MUnionR (s1 ++ napp m s3 ++ s4)).
        apply H5.
      }
    }
  - intros contra. simpl in contra.
    apply not_pc_le_0 in contra.
    destruct contra.
  - intros H.
    (* unfortunately, for general
    a <= b + c, we can have neither
    a <= b \/ a <= c nor a <= b /\ a <= b.
    However, since pumping_constant >= 1,
    we can at least say that at least one of length s1 or length s2
    is >= 1.
    Well, that is not enough to satisfy the hypotheses of
    the two IH's, unless pumping_constant re = 1, which we don't know about.
    So I guess that means we will have to go without the two IH's.
    *)
    (* I don't really know what the s0 s3 and s4 should be, without the IH's,
      but since we are working with 1, and we know EmptyStr gives 1,
      so why not try setting all those that can be empty to []?
      By the hypotheses of the pumping lemma, only s3 should not be empty, so we set
       both s0 and s4 to empty to see what happens.
      In this cas, by the left, we must have s3 = (s1++s2). *)
    exists [], (s1++s2), [].
    split. { rewrite app_nil_r. simpl. reflexivity. }
    {
      split.
      { 
        unfold not. (* use H to get pumping_constant (Star re) <= 0 *)
        intros H1.
        rewrite -> H1 in H. simpl in H.
        apply not_pc_le_0 in H.
        destruct H.
      }
      {
        simpl. intros m. rewrite -> app_nil_r.
        (* 
           Hmatch 1 and 2 gives  (s1++s2) =~ Star re.
           Then, use my corollary to prove that napp m of that 
           is also in L(Star re)
         *)
        apply (
          MStarNApp _ re (s1++s2)
          (MStarApp s1 s2 re Hmatch1 Hmatch2) (*s1++s2 =~ Star re*)
        ).
      }
    }
Qed.

From LF.induction Require Import basic_induction.

Lemma pumping : forall T (re : reg_exp T) s,
  s =~ re ->
  pumping_constant re <= length s ->
  exists s1 s2 s3,
    s = s1 ++ s2 ++ s3 /\
    s2 <> [] /\
    length s1 + length s2 <= pumping_constant re /\
    forall m, s1 ++ napp m s2 ++ s3 =~ re.
Proof.
  intros T re s Hmatch.
  induction Hmatch
    as [ | x | s1 re1 s2 re2 Hmatch1 IH1 Hmatch2 IH2
       | s1 re1 re2 Hmatch IH | s2 re1 re2 Hmatch IH
       | re | s1 s2 re Hmatch1 IH1 Hmatch2 IH2 ].
  - (* MEmpty *)
    simpl. intros contra. inversion contra.
  - intros contra. simpl in contra. inversion contra.
    inversion H1. (* 2 <= 1 is impossible, because 2 <= 0 is *)
  - intros H.
    simpl in H. rewrite -> app_length in H.
    apply plus_le_cases in H.
    destruct H as [H | H].
    + apply IH1 in H.
      destruct H as [s0 [s3 [s4]]].
      exists s0, s3, (s4++s2).
      destruct H as [H1 H2].
      split.
      { 
        rewrite -> H1. rewrite <- app_assoc with 
        (l := s0) (m := (s3++s4)) (n := s2). rewrite <- app_assoc.
        reflexivity. 
      }
      {
        destruct H2 as [H2 H3].
        split.
        { apply H2. }
        { 
          split.
          {
            simpl.
            destruct H3 as [H3 _].
            apply (le_trans
              (length s0 + length s3) (pumping_constant re1)
              (pumping_constant re1 + pumping_constant re2)
            ).
            apply H3.
            apply le_plus_l.
          }
          { intros m. 
            rewrite -> app_assoc with 
              (l := napp m s3) (m := s4) (n := s2).
            rewrite -> app_assoc with 
              (l := s0) (m := napp m s3 ++ s4) (n := s2).
            apply (MApp (s0 ++ napp m s3 ++ s4) re1 s2 re2).
            { apply H3. }
            { apply Hmatch2. }
          }
        }
      }
    + (* apply IH2 in H, but also keep H *)
      assert (IH2o := IH2 H).
      destruct IH2o as [s0 [s3 [s4]]].
      destruct H0 as [H1 [H2 [H3 H4]]].
      (* Now, we have to rely on the 
         LEM like prop: n < m \/ n >= m.
         We do this on length s1 vs pumping_constant re1,
         because we can then either use the IH or directly prove the goal.
       *)
      destruct (lt_ge_cases (length s1) (pumping_constant re1)).
       * exists (s1++s0), s3, s4.
         split.
         { 
           rewrite -> H1. rewrite -> app_assoc.
           reflexivity.
         }
         {
           split.
           { apply H2. }
           {
             split.
             {
                apply n_lt_m__n_le_m in H0.
                rewrite -> app_length.
                simpl. rewrite <- add_assoc.
                apply (le_cases_plus _ _ _ _ H0 H3).
             }
             {
               intros m. rewrite <- app_assoc.
               apply (MApp s1 re1 _ re2).
               { apply Hmatch1. }
               { apply H4. }
             }
           }
         }
       * assert (IH1o := IH1 H0).
         destruct IH1o as [s5 [s6 [s7 ]]].
         destruct H5 as [H5 [H6 [H7 H8]]].
         exists s5, s6, (s7++s2).
         split.
         { 
           rewrite -> app_assoc.
           rewrite -> app_assoc.
           rewrite <- app_assoc with _ s5 s6 s7.
           rewrite -> H5. reflexivity.
         }
         split.
         { apply H6. }
         split.
         { simpl. 
           apply (le_plus_trans _ _ _ H7).
         }
         {
           intros m.
           rewrite -> app_assoc.
           rewrite -> app_assoc.
           rewrite <- app_assoc with _ s5 (napp m s6) s7.
           apply (MApp (s5 ++ napp m s6 ++ s7) re1 s2 re2).
           apply H8. apply Hmatch2.
         }
  - intros H. simpl in H.
    apply plus_le in H.
    destruct H as [H1 H2].
    apply IH in H1.
    destruct H1 as [s2 [s3 [s4]]].
    destruct H as [H3 [H4 H5]].
    exists s2, s3, s4.
    split.
    { apply H3. }
    { split.
      { apply H4. }
      split.
      {
        destruct H5 as [H5 _].
        simpl.
        apply (le_plus_trans _ _ _ H5).
      }
      {
        intros m. 
        apply (MUnionL (s2 ++ napp m s3 ++ s4)).
        apply H5.
      }
    }
    (* basically the same as the above one, just swap 1 and 2 and L and R 
       in a few places. *)
  - intros H. simpl in H.
    apply plus_le in H.
    destruct H as [H1 H2].
    apply IH in H2.
    destruct H2 as [s1 [s3 [s4]]].
    destruct H as [H3 [H4 H5]].
    exists s1, s3, s4.
    split.
    { apply H3. }
    { split.
      { apply H4. }
      split.
      {
        destruct H5 as [H5 _].
        simpl. rewrite add_comm with (pumping_constant re1) _.
        apply (le_plus_trans _ _ _ H5).
      }
      {
        intros m. 
        apply (MUnionR (s1 ++ napp m s3 ++ s4)).
        apply H5.
      }
    }
  - intros contra. simpl in contra.
    apply not_pc_le_0 in contra.
    destruct contra.
  - intros H.
    (* Here, unfortunately, like in the MApp case,
       we have to base on lt_ge_cases (length s1) (pumping_constant re) and
       that for s2 to decide which variables to use in exists.
     *)
    destruct 
      s1 eqn:Es1,
      (lt_ge_cases (length s2) (pumping_constant re)).
    + exists [], s1, s2.
      split. 
      { rewrite -> Es1. reflexivity. }
      split.
      { 
        unfold not.
        intros H2.
        simpl in H.
        simpl in H.
        unfold lt in H0.
        (* we now have S (l s2) <= l s2 *)
        assert (H3 := le_trans _ _ _ H0 H).
        apply not_le_Sn_n in H3.
        destruct H3.
      }
      split.
      {
        rewrite -> Es1.
        simpl. 
        assert (0 <= 1) as H1. { apply le_S. apply le_n. }
        apply (le_trans 0 1 (pumping_constant re) H1).
        apply pumping_constant_ge_1.
      }
      {
        simpl. intros m. 
        apply (MStarStarApp T re (napp m s1) s2
          (MStarNApp _ re s1 (MStar1 _ _ _ Hmatch1) m) Hmatch2
        ).
      }
    + apply IH2 in H1.
      destruct H1 as [s0 [s3 [s4]]].
      destruct H1 as [H1 [H2 [H3 H4]]].
      exists [], s1, s2.
      
Qed.

End Pumping.
