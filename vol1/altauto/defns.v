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
	intros l1. induction l1; intros l2;
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
  - (* MEmpty *) simpl. apply MEmpty.
  - (* MChar *) simpl. apply MChar.
  - (* MApp *) simpl.
    destruct re1;
    try (inversion IH1; simpl; destruct re2; apply IH2);
    ( 
		  destruct re2;
			try ( inversion IH2; rewrite app_nil_r; apply IH1);
      (apply MApp; [ apply IH1 | apply IH2 ])
	  ).
  - (* MUnionL *) simpl.
    destruct re1;
    [
			inversion IH
 		|	 
			destruct re2;
			[
				apply IH
			|	(
				apply MUnionL; apply IH
				)
			| ..
			]
		].
  - (* MUnionR *) simpl.
    destruct re1.
    + apply IH.
    + destruct re2.
      * inversion IH.
      * apply MUnionR. apply IH.
      * apply MUnionR. apply IH.
      * apply MUnionR. apply IH.
      * apply MUnionR. apply IH.
      * apply MUnionR. apply IH.
    + destruct re2.
      * inversion IH.
      * apply MUnionR. apply IH.
      * apply MUnionR. apply IH.
      * apply MUnionR. apply IH.
      * apply MUnionR. apply IH.
      * apply MUnionR. apply IH.
    + destruct re2.
      * inversion IH.
      * apply MUnionR. apply IH.
      * apply MUnionR. apply IH.
      * apply MUnionR. apply IH.
      * apply MUnionR. apply IH.
      * apply MUnionR. apply IH.
    + destruct re2.
      * inversion IH.
      * apply MUnionR. apply IH.
      * apply MUnionR. apply IH.
      * apply MUnionR. apply IH.
      * apply MUnionR. apply IH.
      * apply MUnionR. apply IH.
    + destruct re2.
      * inversion IH.
      * apply MUnionR. apply IH.
      * apply MUnionR. apply IH.
      * apply MUnionR. apply IH.
      * apply MUnionR. apply IH.
      * apply MUnionR. apply IH.
 - (* MStar0 *) simpl.
    destruct re.
    + apply MEmpty.
    + apply MEmpty.
    + apply MStar0.
    + apply MStar0.
    + apply MStar0.
    + simpl.
      destruct re.
      * apply MStar0.
      * apply MStar0.
      * apply MStar0.
      * apply MStar0.
      * apply MStar0.
      * apply MStar0.
 - (* MStarApp *) simpl;
   destruct re;
	 [
     inversion IH1 
   | inversion IH1; inversion IH2; apply MEmpty 
   | [> apply star_app; 
		 [
       apply MStar1; apply IH1 |
       apply IH2
		 ]
		 ]
   | ..
	 ].
Qed.

