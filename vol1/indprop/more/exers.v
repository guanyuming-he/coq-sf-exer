From LF.basics Require Import booleans.
From LF.poly Require Import defns.

Inductive nostutter {X:Type} : list X -> Prop :=
  (* My understanding of the defn:
     A list shutters iff there exists consequtive sublist of length 2 of it
     contains the same two elements.
  *)
  | nost_empty : nostutter []
  | nost_1 (x : X) : nostutter [x]
  | nost_induct 
      (x h : X) (t : list X) 
      (H1 : nostutter (h :: t)) (H2 : x <> h) :
      nostutter (x :: h::t).

Example test_nostutter_1: nostutter [3;1;4;1;5;6].
Proof. 
  repeat apply nost_induct; auto.
  apply nost_1.
Qed.

Example test_nostutter_2: nostutter (@nil nat).
Proof. 
  apply nost_empty.
Qed.

Example test_nostutter_3: nostutter [5].
Proof.
  apply nost_1.
Qed.

Example test_nostutter_4: not (nostutter [3;1;1;4]).
Proof.
  unfold not.
  intros H.
  inversion H.
  inversion H0. (* will get 1 <> 1 *)
  unfold not in H9. apply H9. reflexivity.
Qed.


Inductive merge {X:Type} : list X -> list X -> list X -> Prop :=
  (* My understanding:
     A list l is a merge of l1 and l2 (merge l1 l2 l), iff
     l1 and l2 are sublists of l, and that l contains only
     the elements of l1 and l2 (i.e. length l = length l1 + length l2)
   *)
  | merge_0 : merge [] [] []
  | merge_l x l1 l2 l (H : merge l1 l2 l)
      : merge (x::l1) l2 (x::l)
  | merge_r x l1 l2 l (H : merge l1 l2 l)
      : merge l1 (x::l2) (x::l).

(* For All *)
From LF.logic Require Import prog_props.

Theorem merge_filter : forall (X : Set) (test: X->bool) (l l1 l2 : list X),
  merge l1 l2 l ->
  All (fun n => test n = true) l1 ->
  All (fun n => test n = false) l2 ->
  filter test l = l1.
Proof.
  intros X test l l1 l2 H.
  induction H.
  - intros H1 H2. simpl. reflexivity.
  - intros H1 H2. simpl.
    destruct (test x) eqn:Ex.
    + simpl in H1. destruct H1 as [_ H1].
      rewrite (IHmerge H1 H2).
      reflexivity.
    + simpl in H1. destruct H1 as [H1 _].
      rewrite -> H1 in Ex. discriminate Ex.
  - intros H1 H2. simpl.
    destruct (test x) eqn:Ex.
    + simpl in H2. destruct H2 as [H2 _].
      rewrite -> H2 in Ex. discriminate Ex.
    + simpl in H2. destruct H2 as [_ H2].
      apply (IHmerge H1 H2).
Qed.

(* For le *)
From LF.indprop Require Import defns.
(* For subseq *)
From LF.indprop Require Import r_subseq.
(* For many useful lemmas *)
From LF.indprop Require Import indrela.

Theorem filter_challenger_2 :
  (* 
     First, filter test l is such a subsequence that test evaluates to true.
     Second, for all such sequence l, length l <= length (filter test l).
   *)
  forall 
    (* I would want nat to be a general X, but unfortunately subseq from the
     * book is only defined for list nat. *)
    (test : nat -> bool)
    (l : list nat),
    forall sl : list nat,
    subseq sl l /\ All (fun n => test n = true) sl ->
    length sl <= length (filter test l).
Proof.
  intros test l sl [H1 H2].
  induction H1.
  - simpl. apply O_le_n.
  - simpl in H2. destruct H2 as [H2 H3].
    apply IHsubseq in H3.
    simpl.
    rewrite -> H2.
    simpl.
    apply n_le_m__Sn_le_Sm.
    apply H3.
  - apply IHsubseq in H2.
    simpl.
    destruct (test n).
    + simpl. 
      apply (le_trans
      _ _ _ H2).
      apply n_le_Sn.
    + apply H2.
Qed.
    
Inductive pal {X:Type} : list X -> Prop :=
  | pal_0 : pal []
  | pal_1 x : pal [x]
  | pal_induct (x : X) (l : list X) (H : pal l) : pal (x::l++[x]).

(* For list related theorems *)
From LF.poly Require Import poly_list_exer.

Theorem pal_app_rev : forall (X:Type) (l : list X),
  pal (l ++ (rev l)).
Proof.
  intros X l. induction l.
  - simpl. apply pal_0.
  - simpl. rewrite -> app_assoc. apply pal_induct. apply IHl.
Qed.

Theorem pal_rev : forall (X:Type) (l: list X) , pal l -> l = rev l.
Proof.
  intros X l H.
  induction H.
  - reflexivity.
  - reflexivity.
  - simpl. 
    assert (forall l : list X,
    rev (l ++ [x]) = x :: (rev l))
    as H1.
    {
      intros l1. induction l1.
      - reflexivity.
      - simpl. rewrite -> IHl1. reflexivity.
    }
    rewrite -> H1.
    rewrite <- IHpal.
    simpl.
    reflexivity.
Qed.

(* For properties about addition *)
From LF.induction Require Import basic_induction.

(* After a few hours of proving the following Theorem in vein,
   I searched for help online and found that I may need to prove something
   different in order to prove this theorem, to induct on something different.
   This is because if I induct on l, the IH will not be general enough to
   support my advance.  As such, I have to make something up, inducting on it,
   and then be able to make the IH forall l, ...  Hence this lemma. *)
Lemma palindrome_converse_nat : 
  forall (X : Type) (n: nat) (l: list X), 
  length l <= n -> l = rev l -> pal l.
Proof.
  (* Now, surprisingly, we induction on n instead. *)
  intros X n. induction n.
  - intros l. destruct l.
    + intros H1 H2. apply pal_0.
    + intros H1 H2. simpl in *.
      inversion H1 (* Impossible *).
  - intros l. destruct l.
    + intros H1 H2. apply pal_0.
    + intros H1 H2. simpl in *.
      apply Sn_le_Sm__n_le_m in H1.
      (* To see the first element of (rev l) ++ [x], we have to
          destruct rev l *)
      destruct (rev l) eqn:Erl.
      * simpl in H2. injection H2 as H3.
        rewrite -> H3. apply pal_1.
      * injection H2 as H3 H4.
        rewrite <- H3 in *.
        rewrite -> H4.
        apply pal_induct.
        rewrite -> H4 in Erl.
        rewrite rev_app_distr in Erl. injection Erl as El0.
        rewrite H4 in H1. rewrite app_length in H1.
        simpl in H1. rewrite <- plus_n_Sm in H1. rewrite -> add_0_r in H1.
        apply Sn_le_m__n_le_m in H1.
        apply eq_sym in El0.
        apply (IHn l0 H1 El0).
Qed.

Theorem palindrome_converse: forall {X: Type} (l: list X),
    l = rev l -> pal l.
Proof.
  intros X l.
  assert (exists n : nat, length l <= n) as H1.
  {
    induction l.
    - exists 0. apply le_n.
    - destruct IHl as [n IHl].
      exists (S n).
      simpl. apply n_le_m__Sn_le_Sm. apply IHl.
  }
  destruct H1 as [n H1].
  intros H2.
  apply (palindrome_converse_nat _ _ _ H1 H2).
Qed.

(* In is defined in the prog_props Imported earlier. *)

(* I know I could define this inductively, the usual way,
   but I want to see how hard it will be if I define this in the intuitive way.
*)
Definition disjoint {X : Type} (l1 l2 : list X) : Prop
  :=
  forall x : X,
  (In x l1 -> ~(In x l2)) /\ (In x l2 -> ~(In x l1)).

(* My own lemmas about disjoint *)
Lemma disjoint_ne_head : forall (X : Type) (x1 x2 : X) (l1 l2 : list X),
  disjoint (x1::l1) (x2::l2) -> x1 <> x2.
Proof.
  intros X x1 x2 l1 l2 H.
  unfold not.
  intros Ne.
  unfold disjoint in H.
  destruct (H x1) as [H1 H2].
  rewrite <- Ne in H1.
  simpl in H1.
  apply H1.
  - left. reflexivity.
  - left. reflexivity.
Qed.

Lemma disjoint_reduce_l : forall (X : Type) (x : X) (l1 l2 : list X),
  disjoint (x::l1) l2 -> disjoint l1 l2.
Proof.
  intros X x l1 l2 H.
  unfold disjoint in *.
  intros y.
  split.
  - destruct (H y) as [H1 H2].
    simpl in H1.
    intros H3. apply H1.
    right. apply H3.
  - destruct (H y) as [H1 H2].
    intros H3. apply H2 in H3.
    simpl in H3.
    unfold not. unfold not in H3.
    intros H4. apply H3.
    right. apply H4.
Qed.


Inductive NoDup {X : Type} : list X -> Prop :=
  | nodup_0 : NoDup []
  | nodup_ind (x : X) (l : list X) 
      (H1: ~(In x l)) (H2: NoDup l) :
      NoDup (x::l).

(* For rewriting iff *)
From Coq Require Import Setoids.Setoid.

Theorem nodup_disjoint :
  forall (X : Type) (l1 l2 : list X),
  NoDup (l1++l2) -> disjoint l1 l2.
Proof.
  intros X l1.
  induction l1.
  - intros l2 H. unfold disjoint.
    intros x. split.
    + intros contra. inversion contra.
    + intros _. unfold not. intros contra.
      inversion contra.
  - intros l2 H.
    simpl in H.
    inversion H.
    apply IHl1 in H3.
    unfold disjoint.
    intros x1. split.
    + rewrite In_app_iff in H0.
      intros H4. unfold not. intros H5.
      simpl in H4.
      destruct H4 as [H4 | H4].
      * rewrite -> H4 in H0.
        apply H0. right. apply H5.
      * unfold disjoint in H3.
        destruct (H3 x1) as [H6 H7].
        apply H6 in H4.
        apply (H4 H5).
    + rewrite In_app_iff in H0.
      intros H4. unfold not. intros H5.
      simpl in H5. destruct H5 as [H5 | H5].
      * rewrite -> H5 in H0. apply H0. right. apply H4.
      * unfold disjoint in H3.
        destruct (H3 x1) as [H6 H7].
        apply H6 in H5.
        apply (H5 H4).
Qed.

Lemma in_split : forall (X:Type) (x:X) (l:list X),
  In x l ->
  exists l1 l2, l = l1 ++ x :: l2.
Proof.
  intros X x l.
  generalize dependent x.
  induction l.
  - intros x contra. inversion contra.
  - intros x0.
    intros [H | H].
    + rewrite -> H.
      exists [], l.
      simpl. reflexivity.
    + apply IHl in H.
      destruct H as [l1 [l2 H]].
      exists (x::l1), l2.
      rewrite -> H.
      simpl.
      reflexivity.
Qed.

Inductive repeats {X:Type} : list X -> Prop :=
  (* generate: from none to some *)
  | repeat_gen (x : X) (l : list X)
      (H: In x l) : repeats (x::l)
  (* extension : from some to some. *)
  | repeat_exp (x : X) (l : list X)
      (H: repeats l) : repeats (x::l).

(* For LEM *)
From LF.logic Require Import logic.

Theorem pigeonhole_principle: excluded_middle ->
  forall (X:Type) (l1 l2:list X),
  (forall x, In x l1 -> In x l2) ->
  length l2 < length l1 ->
  repeats l1.
Proof.
  intros EM X l1. induction l1 as [|x l1' IHl1'].
  - intros l2 _ contra.
    unfold lt in contra.
    simpl in contra.
    inversion contra.
  - intros l2 H1 H2.
    (* Now we reason by cases:
        x in l1' or x not in l1' *)
    unfold excluded_middle in EM.
    destruct (EM (In x l1')) as [H3|H3].
    + apply repeat_gen.
      apply H3.
    + apply repeat_exp.
      (* Now I seem stuck, so I consider using in_split.
         To use that, I need to show In x l2, which fortunately
         can be obtained from (H1 x) *)
      assert (In x l2) as H4.
      {
        apply (H1 x).
        simpl. left. reflexivity.
      }
      destruct (in_split _ _ _ H4) as [l3 [l4 H5]].
      (* Now consider l2 with x removed: l3++l4 *)
      apply (IHl1' (l3++l4)).
      {
        intros x0 H'.
        rewrite -> In_app_iff.
        assert (H1' := H1 x0).
        simpl in H1'. assert (In x0 l2) as H1''.
        {
          apply H1'.
          simpl. right. apply H'.
        }
        rewrite -> H5 in H1''.
        rewrite -> In_app_iff in H1''.
        simpl in H1''.
        destruct H1'' as [H1''|[H1''|H1'']].
        * left. apply H1''.
        * rewrite -> H1'' in H3. (* Now H3 and H' contradicts *)
          destruct (H3 H').
        * right. apply H1''.
      }
      {
        rewrite -> H5 in H2.
        rewrite -> app_length in H2. simpl in H2.
        rewrite -> app_length.
        unfold lt in H2. unfold lt.
        apply Sn_le_Sm__n_le_m.
        rewrite <- plus_n_Sm in H2.
        apply H2.
      }
Qed.

(* For re *)
From LF.indprop Require Import regex.

Require Import Coq.Strings.Ascii.

Definition string := list ascii.

Lemma provable_equiv_true : forall (P : Prop), P -> (P <-> True).
Proof.
  intros.
  split.
  - intros. constructor.
  - intros _. apply H.
Qed.

Lemma not_equiv_false : forall (P : Prop), ~P -> (P <-> False).
Proof.
  intros.
  split.
  - apply H.
  - intros. destruct H0.
Qed.

Lemma null_matches_none : forall (s : string), (s =~ EmptySet) <-> False.
Proof.
  intros.
  apply not_equiv_false.
  unfold not. intros. inversion H.
Qed.


Lemma empty_matches_eps : forall (s : string), s =~ EmptyStr <-> s = [ ].
Proof.
  split.
  - intros. inversion H. reflexivity.
  - intros. rewrite H. apply MEmpty.
Qed.

Lemma empty_nomatch_ne : forall (a : ascii) s, (a :: s =~ EmptyStr) <-> False.
Proof.
  intros.
  apply not_equiv_false.
  unfold not. intros. inversion H.
Qed.

Lemma char_nomatch_char :
  forall (a b : ascii) s, b <> a -> (b :: s =~ Char a <-> False).
Proof.
  intros.
  apply not_equiv_false.
  unfold not.
  intros.
  apply H.
  inversion H0.
  reflexivity.
Qed.


Lemma char_eps_suffix : forall (a : ascii) s, a :: s =~ Char a <-> s = [ ].
Proof.
  split.
  - intros. inversion H. reflexivity.
  - intros. rewrite H. apply MChar.
Qed.

Lemma app_exists : forall (s : string) re0 re1,
  s =~ App re0 re1 <->
  exists s0 s1, s = s0 ++ s1 /\ s0 =~ re0 /\ s1 =~ re1.
Proof.
  intros.
  split.
  - intros. inversion H. exists s1, s2. split.
    * reflexivity.
    * split. apply H3. apply H4.
  - intros [ s0 [ s1 [ Happ [ Hmat0 Hmat1 ] ] ] ].
    rewrite Happ. apply (MApp s0 _ s1 _ Hmat0 Hmat1).
Qed.

Lemma app_ne : forall (a : ascii) s re0 re1,
  a :: s =~ (App re0 re1) <->
  ([ ] =~ re0 /\ a :: s =~ re1) \/
  exists s0 s1, s = s0 ++ s1 /\ a :: s0 =~ re0 /\ s1 =~ re1.
Proof.
  intros a s r0 r1.
  split.
  - intros H. inversion H.
    destruct s1.
    + left. split.
      { apply H3. } { simpl. apply H4. }
    + simpl in H1. inversion H1.
      right.
      exists s1, s2.
      split.
      { reflexivity. }
      split.
      { rewrite -> H6 in H3. apply H3. }
      { apply H4. }
  - intros [H1 | H1].
    + destruct H1 as [H1 H2]. 
      assert (a::s = [] ++ (a::s)) as H3.
     { reflexivity. } 
     rewrite -> H3. apply MApp.
     { apply H1. }
     { apply H2. }
    + destruct H1 as [s1 [s2 [H]]].
      rewrite -> H.
      assert (a:: (s1++s2) = ((a::s1)++s2)) as H3.
      { reflexivity. }
      destruct H0 as [H4 H5].
      rewrite -> H3. apply MApp.
      { apply H4. }
      { apply H5. }
Qed.

Lemma star_ne : forall (a : ascii) s re,
  a :: s =~ Star re <->
  exists s0 s1, s = s0 ++ s1 /\ a :: s0 =~ re /\ s1 =~ Star re.
Proof.
  intros a s re.
  split.
  - remember (Star re) as re'.
    remember (a::s) as l. (* This is needed to discriminate the first case *)
    intros H.
    induction H.
    + discriminate Heql.
    + inversion Heqre'. (* Char can never equal to Star, contradiction *)
    + (* I don't know why this works, but this works *)
      discriminate.
    + (* I don't know why this works, but this works *)
      discriminate.
    + (* I don't know why this works, but this works *)
      discriminate.
    + (* I don't know why this works, but this works *)
      discriminate.
    + (* To get head s1, have to destruct it *)
      destruct s1 eqn:Es1.
      * injection Heqre' as H1.
        rewrite -> H1 in *.
        apply IHexp_match2.
        { reflexivity. }
        { simpl in Heql. apply Heql. }
      * injection Heqre' as H1.
        rewrite -> H1 in *.
        injection Heql as H2 H3.
        rewrite <- H2 in *.
        exists l, s2.
        split.
        { apply eq_sym. apply H3. }
        split.
        { apply H. }
        { apply H0. }
  -
    intros [s0 [s1 [H1 [H2 H3]]]].
    rewrite -> H1.
    assert (a :: s0++s1 = (a::s0) ++s1) as H4.
    { reflexivity. }
    rewrite -> H4.
    apply MStarApp.
    { apply H2. }
    { apply H3. }
Qed.

From LF.indprop Require Import reflect.

Definition refl_matches_eps m :=
  forall re : reg_exp ascii, reflect ([ ] =~ re) (m re).

Fixpoint match_eps (re: reg_exp ascii) : bool
  :=
  match re with
  | EmptySet => false
  | EmptyStr => true 
  | Char _ => false
  | App re1 re2 => andb (match_eps re1) (match_eps re2)
  | Union re1 re2 => orb (match_eps re1) (match_eps re2)
  | Star _ => true
  end.

(* My own lemma *)
Lemma app_nil_both_nil :
  forall (X : Type) (s1 s2 : list X), s1++s2 = [] -> (s1 = [] /\ s2 = []).
Proof.
  destruct s1, s2.
  * split. reflexivity. reflexivity.
  * intros H0. discriminate H0.
  * intros H0. discriminate H0.
  * intros H0. discriminate H0.
Qed.


Lemma match_eps_refl : refl_matches_eps match_eps.
Proof.
  unfold refl_matches_eps.
  intros re. 
  assert (@nil ascii = ([] ++ [])) as H.
  { reflexivity. }
  induction re.
  - simpl. apply ReflectF.
    unfold not. intros contra. inversion contra.
  - simpl. apply ReflectT.
    apply MEmpty.
  - simpl. apply ReflectF.
    unfold not. intros contra. inversion contra.
  - simpl. apply reflect_iff in IHre1, IHre2.
    destruct (match_eps re1), (match_eps re2).
    + apply ReflectT. 
      rewrite -> H. apply MApp.
      { apply IHre1. reflexivity. }
      { apply IHre2. reflexivity. }
    + apply ReflectF.
      unfold not. 
      intros H1.
      inversion H1.
      destruct (app_nil_both_nil _ s1 s2 H0) as [_ H'].
      rewrite -> H' in H5.
      apply IHre2 in H5. discriminate H5.
    + apply ReflectF.
      unfold not. 
      intros H1.
      inversion H1.
      destruct (app_nil_both_nil _ s1 s2 H0) as [H' _].
      rewrite -> H' in H4. apply IHre1 in H4.
      discriminate H4.
    + apply ReflectF.
      unfold not. intros H1. inversion H1.
      destruct (app_nil_both_nil _ s1 s2 H0) as [_ H'].
      rewrite -> H' in H5. apply IHre2 in H5.
      discriminate H5.
  - simpl.
    inversion IHre1.
    + apply ReflectT. apply MUnionL.
      apply H1.
    + inversion IHre2.
      * apply ReflectT. apply MUnionR.
        apply H3.
      * apply ReflectF.
        unfold not. intros H'.
        inversion H'.
        { apply (H1 H6). }
        { apply (H3 H6). }
  - apply ReflectT.
    apply MStar0.
Qed.

Definition is_der re (a : ascii) re' :=
  forall s, a :: s =~ re <-> s =~ re'.

Definition derives d := forall a re, is_der re a (d a re).

(* Deal with the strange Ascii.eqb *)
Lemma ascii_equals_self : forall x : ascii, Ascii.eqb x x = Coq.Init.Datatypes.true.
Proof.
  intros [[] [] [] [] [] [] [] []]; reflexivity.
Qed.

Fixpoint derive (a : ascii) (re : reg_exp ascii) : reg_exp ascii
  (* returns r such that isder re a r. *)
  :=
  match re with
  | EmptySet => EmptySet
  | EmptyStr => EmptySet
  | Char b => 
      (* Note that this Ascii.eqb is hard to work with *)
      if Ascii.eqb a b then
      EmptyStr else
      EmptySet
  | App re1 re2 => 
      if (match_eps re1) then
      (* both are possible, using a Union *)
      Union (derive a re2) (App (derive a re1) re2) else 
      App (derive a re1) re2
  | Union re1 re2 => Union (derive a re1) (derive a re2)
  | Star re => App (derive a re) (Star re)
  end.

Example c := ascii_of_nat 99.
Example d := ascii_of_nat 100.

Example test_der0 : match_eps (derive c (EmptySet)) = false.
Proof.
  simpl. reflexivity.
Qed.

Example test_der1 : match_eps (derive c (Char c)) = true.
Proof.
  simpl. reflexivity.
Qed.

Example test_der2 : match_eps (derive c (Char d)) = false.
Proof.
  reflexivity.
Qed.

Example test_der3 : match_eps (derive c (App (Char c) EmptyStr)) = true.
Proof.
  reflexivity.
Qed.

Example test_der4 : match_eps (derive c (App EmptyStr (Char c))) = true.
Proof.
  reflexivity.
Qed.

Example test_der5 : match_eps (derive c (Star (Char c))) = true.
Proof.
  reflexivity.
Qed.

Example test_der6 :
  match_eps (derive d (derive c (App (Char c) (Char d)))) = true.
Proof.
  reflexivity.
Qed.

Example test_der7 :
  match_eps (derive d (derive c (App (Char d) (Char c)))) = false.
Proof.
  reflexivity.
Qed.

Lemma derive_corr : derives derive.
Proof.
  unfold derives.      
  intros a re.
  induction re.
  - simpl. unfold is_der.
    intros s. split.
    + intros contra. inversion contra.
    + intros contra. inversion contra.
  - unfold is_der. intros s. split.
    + intros contra. inversion contra.
    + intros contra. inversion contra.
  - unfold is_der. intros s. split.
    + intros H. inversion H.
      simpl.
      rewrite -> ascii_equals_self.
      apply MEmpty.
    + intros H.
      (* discuss by case a=t or not *)
      destruct (Ascii.eqb a t) eqn:H1.
      * simpl in H. rewrite -> H1 in H. simpl in H. inversion H.
        rewrite -> Ascii.eqb_eq in H1. rewrite -> H1. apply MChar.
      * simpl in H. rewrite -> H1 in H. (* impossible *) inversion H.
  - simpl.
    unfold is_der in IHre1, IHre2.
    destruct (match_eps re1) eqn:E.
    + unfold is_der.
      intros s. split.
      * intros H. rewrite -> app_ne in H.
        destruct H as [H|H].
        {
          destruct H as [H1 H2].
          apply IHre2 in H2.
          apply MUnionL. apply H2.
        }
        {
          destruct H as [s0 [s1 [H1 H2]]].
          rewrite -> H1.
          apply MUnionR. apply MApp.
          {
            destruct H2 as [H2 H3].
            apply IHre1 in H2.
            apply H2.
          }
          { 
            destruct H2 as [_ H2].
            apply H2.
          }
        }
      *
        intros H.
        inversion H.
        {
          apply app_ne.
          apply IHre2 in H2.
          left.
          split.
          { 
            assert (H4 := reflect_iff _ _ (match_eps_refl re1)).
            apply H4. apply E.
          }
          { apply H2. }
        }
        {
          apply app_ne.
          apply app_exists in H1.
          destruct H1 as [s0 [s1 [H4 [H5 H6]]]].
          apply IHre1 in H5.
          right. exists s0, s1.
          split.
          { apply H4. }
          split.
          { apply H5. }
          { apply H6. }
        }
    + unfold is_der.
      intros s. split.
      * intros H.
        apply app_ne in H.
        destruct H as [H | H].
        { 
          destruct H as [H1 H2].
          assert (H4 := reflect_iff _ _ (match_eps_refl re1)).
          apply H4 in H1. rewrite -> H1 in E.
          discriminate E.
        }
        {
          destruct H as [s0 [s1 [H1 [H2 H3]]]].
          apply app_exists.
          exists s0, s1.
          split.
          { apply H1. }
          split.
          { apply IHre1 in H2. apply H2. }
          { apply H3. }
        }
      * intros H. apply app_exists in H.
        apply app_ne.
        right.
        destruct H as [s0 [s1 [H1 [H2 H3]]]].
        exists s0, s1.
        split.
        { apply H1. }
        split.
        { apply IHre1 in H2. apply H2. }
        { apply H3. }
  - unfold is_der in *.
    intros s. split.
    + intros H.
      inversion H.
      { 
        apply IHre1 in H2.
        simpl.
        apply MUnionL. apply H2.
      }
      {
        apply IHre2 in H1.
        simpl.
        apply MUnionR. apply H1.
      }
    + intros H. simpl in H.
      inversion H.
      {
        apply IHre1 in H2. apply MUnionL. apply H2.
      }
      {
        apply IHre2 in H1. apply MUnionR. apply H1.
      }
  - unfold is_der in *.
    intros s. split.
    + intros H. simpl.
      apply star_ne in H.
      apply app_exists.
      destruct H as [s0 [s1 [H1 [H2 H3]]]].
      exists s0, s1.
      split.
      { apply H1. }
      split.
      { apply IHre in H2. apply H2. }
      { apply H3. }
    + intros H. simpl in H.
      apply app_exists in H.
      apply star_ne.
      destruct H as [s0 [s1 [H1 [H2 H3]]]].
      exists s0, s1.
      split.
      { apply H1. }
      split.
      { apply IHre in H2. apply H2. }
      { apply H3. }
Qed.

Definition matches_regex m : Prop :=
  forall (s : string) re, reflect (s =~ re) (m s re).

Fixpoint regex_match (s : string) (re : reg_exp ascii) : bool
  :=
  (* I could use derive to complete this *)
  match s with 
  | [] => match_eps re 
  | h :: t => regex_match t (derive h re)
  end.

Theorem regex_match_correct : matches_regex regex_match.
Proof.
  unfold matches_regex.
  intros s. induction s.
  - intros re. simpl. 
    apply (match_eps_refl re).
  - intros re.
    (* derive is our way to do induction *)
    simpl.
    assert (H := IHs (derive x re)).
    apply reflect_iff in H.
    destruct (regex_match s (derive x re)).
    + apply ReflectT.
      assert (s =~ derive x re) as H1.
      { apply H. reflexivity. }
      apply derive_corr.
      apply H1.
    + apply ReflectF.
      unfold not. intros H1. apply derive_corr in H1.
      apply H in H1. discriminate H1.
Qed.







    

