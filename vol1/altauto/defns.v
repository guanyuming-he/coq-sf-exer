Set Warnings "-notation-overridden,-notation-incompatible-prefix".
From Stdlib Require Import Arith List.

From LF.indprop Require Import defns.
From LF.indprop Require Import indrela.
From LF.indprop Require Import regex.

Fixpoint re_opt_e {T:Type} (re: reg_exp T) : reg_exp T :=
  match re with
  | App EmptyStr re2 => re_opt_e re2
  | App re1 re2 => App (re_opt_e re1) (re_opt_e re2)
  | Union re1 re2 => Union (re_opt_e re1) (re_opt_e re2)
  | Star re => Star (re_opt_e re)
  | _ => re
  end.

Lemma re_opt_e_match : forall T (re: reg_exp T) s,
  s =~ re -> s =~ re_opt_e re.
Proof.
  intros T re s M.
  induction M
    as [| x'
        | s1 re1 s2 re2 Hmatch1 IH1 Hmatch2 IH2
        | s1 re1 re2 Hmatch IH | s2 re1 re2 Hmatch IH
        | re | s1 s2 re Hmatch1 IH1 Hmatch2 IH2].
  - (* MEmpty *) simpl. apply MEmpty.
  - (* MChar *) simpl. apply MChar.
  - (* MApp *) simpl.
    destruct re1.
    + apply MApp.
      * apply IH1.
      * apply IH2.
    + inversion Hmatch1. simpl. apply IH2.
    + apply MApp.
      * apply IH1.
      * apply IH2.
    + apply MApp.
      * apply IH1.
      * apply IH2.
    + apply MApp.
      * apply IH1.
      * apply IH2.
    + apply MApp.
      * apply IH1.
      * apply IH2.
  - (* MUnionL *) simpl. apply MUnionL. apply IH.
  - (* MUnionR *) simpl. apply MUnionR. apply IH.
  - (* MStar0 *) simpl. apply MStar0.
  - (* MStarApp *) simpl. apply MStarApp.
    * apply IH1.
    * apply IH2.
Qed.

Theorem andb_eq_orb :
  forall (b c : bool),
  (andb b c = orb b c) ->
  b = c.
Proof. 
	intros b c.
	destruct b, c;
	intros H; try (discriminate H); reflexivity.
Qed.

Theorem add_assoc : forall n m p : nat,
    n + (m + p) = (n + m) + p.
Proof. 
	intros n. induction n; intros m p;
	try reflexivity;
	simpl; rewrite -> IHn; reflexivity.
Qed.

Fixpoint nonzeros (lst : list nat) :=
  match lst with
  | nil => nil
  | 0 :: t => nonzeros t
  | h :: t => h :: nonzeros t
  end.
Lemma nonzeros_app : forall lst1 lst2 : list nat,
  nonzeros (lst1 ++ lst2) = (nonzeros lst1) ++ (nonzeros lst2).
Proof. 
	 intros l1. induction l1 as [| x l1' IHl1]; intros l2;
	try reflexivity;
	destruct x; simpl; rewrite -> IHl1; reflexivity.
Qed.


Theorem add_assoc' : forall n m p : nat,
    n + (m + p) = (n + m) + p.
Proof. 
	intros n; intros m p; induction n;
	[
 		reflexivity |
		simpl; rewrite -> IHn; reflexivity
	].
Qed.

Theorem ev100: ev 100.
Proof.
	repeat (apply ev_SS).
	apply ev_0.
Qed.

Fixpoint re_opt {T:Type} (re: reg_exp T) : reg_exp T :=
  match re with
  | App _ EmptySet => EmptySet
  | App EmptyStr re2 => re_opt re2
  | App re1 EmptyStr => re_opt re1
  | App re1 re2 => App (re_opt re1) (re_opt re2)
  | Union EmptySet re2 => re_opt re2
  | Union re1 EmptySet => re_opt re1
  | Union re1 re2 => Union (re_opt re1) (re_opt re2)
  | Star EmptySet => EmptyStr
  | Star EmptyStr => EmptyStr
  | Star re => Star (re_opt re)
  | EmptySet => EmptySet
  | EmptyStr => EmptyStr
  | Char x => Char x
  end.
(* Here is an incredibly tedious manual proof of (one direction of)
   its correctness: *)
(* Use the tacticals described so far to shorten the proof. The proof
   above is about 200 lines. Reduce it to 50 or fewer lines of similar
   density. Solve each of the seven top-level bullets with a one-shot
   proof.

   Hint: use a bottom-up approach. First copy-paste the entire proof
   below. Then automate the innermost bullets first, proceeding
   outwards. Frequently double-check that the entire proof still
   compiles. If it doesn't, undo the most recent changes you made
   until you get back to a compiling proof. *)
Lemma re_opt_match' : forall T (re: reg_exp T) s,
  s =~ re -> s =~ re_opt re.
Proof.
  intros T re s M.
  induction M
    as [| x'
        | s1 re1 s2 re2 Hmatch1 IH1 Hmatch2 IH2
        | s1 re1 re2 Hmatch IH | s2 re1 re2 Hmatch IH
        | re | s1 s2 re Hmatch1 IH1 Hmatch2 IH2].
  - (* MEmpty *) simpl; apply MEmpty.
  - (* MChar *) simpl; apply MChar.
  - (* MApp *) simpl; destruct re1;
    try (inversion IH1; simpl; destruct re2; apply IH2);
    ( 
		  destruct re2;
			try ( inversion IH2; rewrite app_nil_r; apply IH1);
      (apply MApp; [ apply IH1 | apply IH2 ])
	  ).
  - (* My comment: search for for_each_goal in Ltac in Coq manual *)
    (* MUnionL *) simpl; destruct re1; 
		[ 
			inversion IH |
			(
				destruct re2;
				[
					apply IH |
					apply MUnionL; apply IH ..
			  ]
			) ..
		].
	- (* MUnionR *) simpl; destruct re1; 
		[ 
			apply IH |
			(
				destruct re2;
				[
					inversion IH |
					apply MUnionR; apply IH ..
			  ]
			) ..
		].
 - (* MStar0 *) simpl; destruct re;
	 [
	  apply MEmpty | apply MEmpty |
    apply MStar0 .. |
    simpl; destruct re; apply MStar0
	 ].
 - (* MStarApp *) simpl; destruct re;
	 try (inversion IH1; inversion IH2; apply MEmpty);
	 [ 
	 	 (apply star_app; [apply MStar1; apply IH1 | apply IH2 ])
		 ..
	 ].
Qed.


Theorem plus_id_exercise_from_basics : forall n m o : nat,
  n = m -> m = o -> n + m = m + o.
Proof. 
	intuition.
Qed.

Theorem add_assoc_from_induction : forall n m p : nat,
    n + (m + p) = (n + m) + p.
Proof. 
	intros. ring.
Qed.	

Theorem S_injective_from_tactics : forall (n m : nat),
  S n = S m ->
  n = m.
Proof. 
	congruence.
Qed.

Theorem or_distributes_over_and_from_logic : forall P Q R : Prop,
    P \/ (Q /\ R) <-> (P \/ Q) /\ (P \/ R).
Proof. 
	intuition.
Qed.


Example auto_example_5 : 2 = 2.
Proof.
  (* auto subsumes reflexivity because eq_refl is in the hint
     database. *)
  info_auto.
Qed.

Create HintDb rematch_db.
Hint Resolve star_app : rematch_db.
Hint Resolve re_opt_e_match : rematch_db.
Hint Constructors reg_exp : rematch_db.
Hint Constructors exp_match : rematch_db.

Lemma re_opt_match'' : forall T (re: reg_exp T) s,
  s =~ re -> s =~ re_opt re.
Proof.
  intros T re s M.
  induction M
    as [| x'
        | s1 re1 s2 re2 Hmatch1 IH1 Hmatch2 IH2
        | s1 re1 re2 Hmatch IH | s2 re1 re2 Hmatch IH
        | re | s1 s2 re Hmatch1 IH1 Hmatch2 IH2].
  - (* MEmpty *) simpl; auto with rematch_db.
  - (* MChar *) simpl; auto with rematch_db.
  - (* MApp *) simpl; destruct re1;
    [
			inversion IH1 |
			inversion IH1; simpl; destruct re2; auto |
			destruct re2;
			[
				inversion IH2 |
				inversion IH2; rewrite app_nil_r; auto |
			  auto with rematch_db ..
			] ..
		].
  - (* My comment: search for for_each_goal in Ltac in Coq manual *)
    (* MUnionL *) simpl; destruct re1; 
		[ 
			inversion IH |
			(
				destruct re2;
				[
					auto with rematch_db ..
			  ]
			) ..
		].
	- (* MUnionR *) simpl; destruct re1; 
		[ 
			auto with rematch_db |
			(
				destruct re2;
				[
					inversion IH |
					auto with rematch_db ..
			  ]
			) ..
		].
 - (* MStar0 *) simpl; destruct re;
	 [
	  auto with rematch_db .. |
    simpl; destruct re; auto with rematch_db
	 ].
 - (* MStarApp *) simpl; destruct re;
	 [
	   inversion IH1 |
	   inversion IH1; inversion IH2; auto with rematch_db |
		 auto with rematch_db ..
	 ].
Qed. 

(* This is the Module Pumping from indprop/regex.v *)
Import Pumping.

Create HintDb pump_db.
Hint Resolve app_length : rematch_db.
Hint Resolve app_assoc : rematch_db.
Hint Resolve MStarNApp : rematch_db.
Hint Constructors reg_exp : pump_db.
Hint Constructors exp_match : pump_db.

(* Can't find things to simplify using tactics other than auto
 maybe take a look later *)
Lemma weak_pumping' : forall T (re : reg_exp T) s,
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
          auto with pump_db.				
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
          auto with pump_db.        
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
				auto with pump_db.
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

(* Come to this later *)
Lemma pumping' : forall T (re : reg_exp T) s,
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
      (lt_ge_cases (length s1) (pumping_constant re)),
      (lt_ge_cases (length s2) (pumping_constant re)).
    + exists [], s1, s2.
      split. 
      { simpl. reflexivity. }
      split.
      { 
        unfold not.
        intros H2.
        rewrite -> H2 in *.
        unfold lt in H0, H1.
        simpl in *.
        assert (contra :=
          le_trans _ _ _ H1 H 
        ).
        apply not_le_Sn_n in contra. apply contra.
      }
      split.
      {
        simpl.
        apply n_lt_m__n_le_m.
        apply H0.
      }
      {
        intros m. simpl.
        (* 
            MStar1 re Hmatch1 gives s1 =~ Star re, then apply MStarNApp to
            get napp m s1 =~ Star re, and finally use MStarStarApp to get 
            the desired.
        *)
        apply (MStarStarApp T re (napp m s1) s2 
          ((MStarNApp T re s1 (MStar1 T s1 re Hmatch1)) m) Hmatch2
        ).
      }
    + (* Need to further prove by cases for s1 here *)
      destruct s1 as [| h1 t1] eqn:Es1.
      *
        apply IH2 in H1.
        destruct H1 as [s3 [s4 [s5]]].
        destruct H1 as [H1 [H2 [H3 H4]]].
        exists s3, s4, s5; auto.
			* exists [], s1, s2.
        split.
        { rewrite <- Es1. reflexivity. }
        split.
        { unfold not. intros H'. rewrite -> H' in Es1. discriminate Es1. }
        split.
        { simpl. apply n_lt_m__n_le_m. rewrite <- Es1 in H0. apply H0. }
        { 
          intros m. simpl.
          apply MStarStarApp.
          - apply MStarNApp. apply MStar1.  rewrite <- Es1 in Hmatch1. apply Hmatch1.
          - apply Hmatch2.
        }
    + (* Need to further prove by cases for s1, as well *)
      destruct s1 as [| h1 t1] eqn:Es1.
      * simpl in H0. 
        (* 1 <= 0 *)
        assert (contra :=
          le_trans _ _ _ 
          (pumping_constant_ge_1 T re)
          H0
        ). 
        inversion contra.
      * rewrite <- Es1 in H0, IH1. apply IH1 in H0.
        destruct H0 as [s3 [s4 [s5]]].
        destruct H0 as [H2 [H3 [H4 H5]]].
        exists s3, s4, (s5++s2).
        split.
        { 
          rewrite <- Es1. 
          rewrite -> app_assoc. rewrite -> app_assoc. 
          rewrite <- app_assoc with _ s3 s4 s5.
          rewrite <- H2.
          reflexivity.
        }
        split.
        { apply H3. }
        split.
        { simpl. apply H4. }
        { 
          intros m. rewrite -> app_assoc. rewrite -> app_assoc.
          apply (MStarApp _ s2).
          { rewrite <- app_assoc. apply H5. }
          { apply Hmatch2. }
        }
    + apply IH1 in H0. apply IH2 in H1.
      destruct 
        H0 as [s3 [s4 [s5]]], H1 as [s6 [s7 [s8]]].
      destruct 
        H0 as [H2 [H3 [H4 H5]]], H1 as [H6 [H7 [H8 H9]]].
      exists s3, s4, (s5++s2).
      split.
      { 
        rewrite -> app_assoc. rewrite -> app_assoc.
        rewrite <- app_assoc with _ s3 s4 s5.
        rewrite <- H2. reflexivity. 
      }
      split.
      { apply H3. }
      split.
      { apply H4. }
      {
        intros m.
        rewrite -> app_assoc. rewrite -> app_assoc.
        apply (MStarStarApp _ _ _ s2).
        { apply MStar1. rewrite <- app_assoc. apply H5. }
        { apply Hmatch2. }
      }
Qed.

Ltac destructpf x :=
  destruct x; try reflexivity.

Theorem andb3_exchange :
  forall b c d, andb (andb b c) d = andb (andb b d) c.
Proof. 
	intros b c d;
	destructpf b; destructpf c; destructpf d.
Qed.	

Ltac destructpf' x :=
	destruct x; simpl; try (intros H; rewrite H); try reflexivity.

Theorem andb_true_elim2' : forall b c : bool,
    andb b c = true -> c = true.
Proof.
	intros b c. destructpf' b; destructpf' c.
Qed.

Theorem andb3_exchange' :
  forall b c d, andb (andb b c) d = andb (andb b d) c.
Proof.
	intros b c d;
	destructpf' b; destructpf' c; destructpf' d.
Qed.	

Ltac imp_intuition :=
  repeat match goal with
				 | [ H : ?P |- ?P ] => apply H
				 | [ |- forall _, _ ] => intro
				 | [ H1 : ?P -> ?Q, H2 : ?P |- _ ] => apply H1 in H2
         end.

Example imp1 : forall (P : Prop), P -> P.
Proof. imp_intuition. Qed.
Example imp2 : forall (P Q : Prop), P -> (P -> Q) -> Q.
Proof. imp_intuition. Qed.
Example imp3 : forall (P Q R : Prop), (P -> Q -> R) -> (Q -> P -> R).
Proof. imp_intuition. Qed.

(* For me to understand how it plays out *)
Example imp3' : forall (P Q R : Prop), (P -> Q -> R) -> (Q -> P -> R).
Proof. 
	intros P Q R.
	intros H1.
	intros H2 H3.
	apply H1 in H3.
	apply H3. apply H2.
Qed.

Inductive nor (P Q : Prop) :=
	| stroke : ~P -> ~Q -> nor P Q.

Theorem nor_not_or : forall (P Q : Prop),
	nor P Q -> ~ (P \/ Q).
Proof.
	intros.
	destruct H.
	unfold not.
	intros Hor. destruct Hor.
	- contradiction.
	- contradiction.
Qed.

Ltac imp_intuition' :=
  repeat match goal with
				 | [ H : ?P |- ?P ] => apply H
				 | [ |- forall _, _ ] => intro
				 | [ H1 : ?P -> ?Q, H2 : ?P |- _ ] => apply H1 in H2
				 (* destruct nor *)
				 | [ H : nor _ _ |- _ ] => destruct H
				 | [ H : _ \/ _ |- _ ] => destruct H
				 | [ H : _ /\ _ |- _ ] => destruct H
				 (* unfold not *)
				 | [ |- ~(?P) ] => unfold not
				 (* contradiction *)
				 | [ H1 : ?P, H2 : ~(?P) |- _ ] => apply H2 in H1; destruct H1
				 (* split *)
				 | [ |- _ <-> _ ] => split
				 | [ |- _ /\ _ ] => split
				 (* apply stroke *)
				 | [ |- nor _ _ ] => apply stroke
         end.

Theorem nor_not_or' : forall (P Q : Prop),
	nor P Q -> ~ (P \/ Q).
Proof.
	imp_intuition'.
Qed.

Theorem nor_comm' : forall (P Q : Prop),
    nor P Q <-> nor Q P.
Proof. 
	imp_intuition'.
Qed.

Theorem nor_not' : forall (P : Prop),
    nor P P <-> ~P.
Proof. 
	imp_intuition'.
Qed.

Theorem nor_not_and' : forall (P Q : Prop),
    nor P Q -> ~ (P /\ Q).
Proof. 
	imp_intuition'.
Qed.
