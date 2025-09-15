Set Warnings "-notation-overridden,-notation-incompatible-prefix".
From Stdlib Require Import Arith List.

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
	destruct a; simpl; rewrite -> IHl1; reflexivity.
Qed.
