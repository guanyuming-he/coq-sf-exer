From Coq Require Import Lia.
From Coq Require Import Arith.
From Coq Require Import PeanoNat.
Import Nat.
From Coq Require Import EqNat.
From LF.imp Require Import defns.
From LF.maps Require Import defn.


Notation "'LETOPT' x <== e1 'IN' e2"
   := (match e1 with
         | Some x => e2
         | None => None
       end)
   (right associativity, at level 60).
Fixpoint ceval_step (st : state) (c : com) (i : nat)
                    : option state :=
  match i with
  | O => None
  | S i' =>
    match c with
      | <{ skip }> =>
          Some st
      | <{ l := a1 }> =>
          Some (l !-> aeval st a1 ; st)
      | <{ c1 ; c2 }> =>
          LETOPT st' <== ceval_step st c1 i' IN
          ceval_step st' c2 i'
      | <{ if b then c1 else c2 end }> =>
          if (beval st b)
            then ceval_step st c1 i'
            else ceval_step st c2 i'
      | <{ while b1 do c1 end }> =>
          if (beval st b1)
          then LETOPT st' <== ceval_step st c1 i' IN
               ceval_step st' c i'
          else Some st
    end
  end.
Definition test_ceval (st:state) (c:com) :=
  match ceval_step st c 500 with
  | None => None
  | Some st => Some (st X, st Y, st Z)
  end.
Example example_test_ceval :
     test_ceval empty_st

     <{ X := 2;
        if (X <= 1)
        then Y := 3
        else Z := 4
        end }>

     = Some (2, 0, 4).
Proof. reflexivity. Qed.

(* 
	Somehow to custom syntax doesn't work, so I have to write using 
	these primitive constructions
*)
Definition pup_to_n : com
	:=
	CSeq
	(CAsgn "Y" (ANum 0)) 
	(
		CWhile (BLe (ANum 1) (AId "X")) 
		(
			CSeq 
			(CAsgn "Y" (APlus (AId "Y") (AId "X"))) 
			(CAsgn "X" (AMinus (AId "X") (ANum 1)))
		)
	)
.	

Example pup_to_n_1 :
  test_ceval (X !-> 5) pup_to_n
  = Some (0, 15, 0).
Proof.
	reflexivity.
Qed.


Definition peven : com
	:=
	CSeq 
	(
		CWhile 
		(BGt (AId "X") (ANum 1)) 
		(CAsgn "X" (AMinus (AId "X") (ANum 2)))
	)
	(
		CAsgn "Z" (AId "X")
	)
.


Example peven0 :
	test_ceval (X !-> 0) peven
  = Some (0, 0, 0).
Proof.
	reflexivity.
Qed.
Example peven1 :
	test_ceval (X !-> 1) peven
	= Some (1, 0, 1).
Proof.
	reflexivity.
Qed.
Example peven9 :
	test_ceval (X !-> 9) peven
  = Some (1, 0, 1).
Proof.
	reflexivity.
Qed.
Example peven12 :
	test_ceval (X !-> 12) peven
  = Some (0, 0, 0).
Proof.
	reflexivity.
Qed.

Theorem ceval_step__ceval: forall c st st',
      (exists i, ceval_step st c i = Some st') ->
      st =[ c ]=> st'.
Proof.
  intros c st st' H.
  inversion H as [i E].
  clear H.
  generalize dependent st'.
  generalize dependent st.
  generalize dependent c.
  induction i as [| i' ].
  - (* i = 0 -- contradictory *)
    intros c st st' H. discriminate H.
  - (* i = S i' *)
    intros c st st' H.
    destruct c;
           simpl in H; inversion H; subst; clear H.
      + (* skip *) apply E_Skip.
      + (* := *) apply E_Asgn. reflexivity.
      + (* ; *)
        destruct (ceval_step st c1 i') eqn:Heqr1.
        * (* Evaluation of r1 terminates normally *)
          apply E_Seq with s.
            apply IHi'. rewrite Heqr1. reflexivity.
            apply IHi'. assumption.
        * (* Otherwise -- contradiction *)
          discriminate H1.
      + (* if *)
        destruct (beval st b) eqn:Heqr.
        * (* r = true *)
          apply E_IfTrue. rewrite Heqr. reflexivity.
          apply IHi'. assumption.
        * (* r = false *)
          apply E_IfFalse. rewrite Heqr. reflexivity.
          apply IHi'. assumption.
      + (* while *) destruct (beval st b) eqn :Heqr.
        * (* r = true *)
         destruct (ceval_step st c i') eqn:Heqr1.
         { (* r1 = Some s *)
           apply E_WhileTrue with s. rewrite Heqr.
           reflexivity.
           apply IHi'. rewrite Heqr1. reflexivity.
           apply IHi'. assumption. }
         { (* r1 = None *) discriminate H1. }
        * (* r = false *)
          injection H1 as H2. rewrite <- H2.
          apply E_WhileFalse. apply Heqr. 
Qed.

(** 
	*Informal proof of ceval_step__ceval 
	
	The goal is to prove that, if the evaluation can ever terminate to some
	 results for program c from st to st', with a large enough recursive depth
	 limit,
	 then st' is the same as obtained from ceval.

	Intuitively, that means the program has no infinite loop. In other words, the
	program c from st can always finish within at most i recursive depth of
	 ceval_step.

	One attempt that works is to induct on i. Such attempts are commonly made to
	prove properties about proofs of length i, and here it's to prove properties
	about program executions of recursive depth i.

	Clearly, the base case i = 0 is vacuously true, as no valid program takes 0
	 recursive depth to evaluate: ceval_step must be called at least once.

	Now inductively suppose it's true for some i'.
	Consider the different forms of program c.
	1. If c is a skip, then ceval_step gives st' = st. This is also the result
	 that would be obtained from ceval.
	2. If c is a CAsgn, then ceval_step gives the variable assignment overriding
	st as st', and so would ceval.
	3. If c is a CSeq a b, then both of a and b have a depth limit of i'. Thanks
	 to the inductive hypothesis, suppose st =[a]=ceval_step=> st1 and st1
	 =[b]=ceval_step=> st2 (thus st' = st2), then st1 and st2 are also those
	 obtained by ceval. 
	4. If c is a CIf, then it follows similarly (because both ceval_step and
	 ceval use the same beval), except that it's either a or b, not both.
	5. Finally, it comes to a loop while b1 do c1 end
		5.1. First, if beval gives false, then both gives st.
		5.2. If beval succeeds, then both the evaluation of c1 and c under i' are
		promised by the inductive hypothesis to be the same for ceval_step and
		ceval. As they are the two used for the loop evaluation, the whole loop's
		result follows.
*)

Theorem ceval_step_more: forall i1 i2 st st' c,
  i1 <= i2 ->
  ceval_step st c i1 = Some st' ->
  ceval_step st c i2 = Some st'.
Proof.
induction i1 as [|i1']; intros i2 st st' c Hle Hceval.
  - (* i1 = 0 *)
    simpl in Hceval. discriminate Hceval.
  - (* i1 = S i1' *)
    destruct i2 as [|i2']. inversion Hle.
    assert (Hle': i1' <= i2') by lia.
    destruct c.
    + (* skip *)
      simpl in Hceval. inversion Hceval.
      reflexivity.
    + (* := *)
      simpl in Hceval. inversion Hceval.
      reflexivity.
    + (* ; *)
      simpl in Hceval. simpl.
      destruct (ceval_step st c1 i1') eqn:Heqst1'o.
      * (* st1'o = Some *)
        apply (IHi1' i2') in Heqst1'o; try assumption.
        rewrite Heqst1'o. simpl. simpl in Hceval.
        apply (IHi1' i2') in Hceval; try assumption.
      * (* st1'o = None *)
        discriminate Hceval.
    + (* if *)
      simpl in Hceval. simpl.
      destruct (beval st b); apply (IHi1' i2') in Hceval;
        assumption.
    + (* while *)
      simpl in Hceval. simpl.
      destruct (beval st b); try assumption.
      destruct (ceval_step st c i1') eqn: Heqst1'o.
      * (* st1'o = Some *)
        apply (IHi1' i2') in Heqst1'o; try assumption.
        rewrite -> Heqst1'o. simpl. simpl in Hceval.
        apply (IHi1' i2') in Hceval; try assumption.
      * (* i1'o = None *)
        simpl in Hceval. discriminate Hceval. 
Qed.	 


(* Reproof of the various le theorems in indprop, as we use Coq's le here. *)
Theorem le_plus_l : forall a b,
  a <= a + b.
Proof.
  intros a b. induction b.
  - simpl. rewrite -> add_0_r. apply le_n.
  - rewrite -> add_comm. simpl.
    rewrite <- add_comm.
    apply le_S with (n := a) (m := a + b).
    apply IHb.
Qed.
Theorem le_plus_trans : forall n m p : nat,
  n <= m ->
  n <= m + p.
Proof.
  intros n m p H.
  apply (
    le_trans n m (m+p)
    H
    (le_plus_l m p) (* m <= m+p *)
  ).
Qed.

Theorem ceval__ceval_step: forall c st st',
      st =[ c ]=> st' ->
      exists i, ceval_step st c i = Some st'.
Proof.
  intros c st st' Hce.
  induction Hce.
	- exists 1. reflexivity.
	- exists 1. simpl. rewrite -> H. reflexivity.
	- destruct IHHce1 as [i1 H1], IHHce2 as [i2 H2].
		exists (S (i1 + i2)).
		assert (i1 <= (i1+i2)) as HLe1.
		{
			apply le_plus_trans.
			apply le_n.
		}
		assert (i2 <= (i1+i2)) as HLe2.
		{
			rewrite add_comm.
			apply le_plus_trans.
			apply le_n.
		}
		assert (ceval_step st c1 (i1+i2) = Some st') as H3.
		{
			exact (ceval_step_more _ _ _ _ _ HLe1 H1).
		}
		assert (ceval_step st' c2 (i1+i2) = Some st'') as H4.
		{
			exact (ceval_step_more _ _ _ _ _ HLe2 H2).
		}
		simpl.
		rewrite -> H3.
		exact H4.
	- destruct IHHce as [i H1].
		exists (S i).
		simpl.
		rewrite -> H. simpl.
		exact H1.
	- destruct IHHce as [i H1].
		exists (S i).
		simpl.
		rewrite -> H. simpl.
		exact H1.
	- exists 1.
		simpl. rewrite -> H. simpl.
		reflexivity.
	- destruct IHHce1 as [i1 H1], IHHce2 as [i2 H2].
		exists (S (i1 + i2)).
		assert (i1 <= (i1+i2)) as HLe1.
		{
			apply le_plus_trans.
			apply le_n.
		}
		assert (i2 <= (i1+i2)) as HLe2.
		{
			rewrite add_comm.
			apply le_plus_trans.
			apply le_n.
		}
		assert (ceval_step st c (i1+i2) = Some st') as H3.
		{
			exact (ceval_step_more _ _ _ _ _ HLe1 H1).
		}
		assert (
			ceval_step st' 
			(CWhile b c) (i1+i2) = Some st''
		) as H4.
		{
			exact (ceval_step_more _ _ _ _ _ HLe2 H2).
		}
		simpl. rewrite H. simpl.
		rewrite -> H3.
		exact H4.
Qed.

Theorem ceval_and_ceval_step_coincide: forall c st st',
      st =[ c ]=> st'
  <-> exists i, ceval_step st c i = Some st'.
Proof.
  intros c st st'.
  split. apply ceval__ceval_step. apply ceval_step__ceval.
Qed.



Theorem ceval_deterministic' : forall c st st1 st2,
     st =[ c ]=> st1 ->
     st =[ c ]=> st2 ->
     st1 = st2.
Proof.
  intros c st st1 st2 He1 He2.
  apply ceval__ceval_step in He1.
  apply ceval__ceval_step in He2.
  inversion He1 as [i1 E1].
  inversion He2 as [i2 E2].
  apply ceval_step_more with (i2 := i1 + i2) in E1.
  apply ceval_step_more with (i2 := i1 + i2) in E2.
  rewrite E1 in E2. inversion E2. reflexivity.
  lia. lia. 
Qed.
