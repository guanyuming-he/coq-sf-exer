(* Actual definitions used *)

Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Bool.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.
From Coq Require Import EqNat. Import Nat.
From Coq Require Import Lia.
From Coq Require Import List. Import ListNotations.
From Coq Require Import Strings.String.
From LF.maps Require Import maps.
Set Default Goal Selector "!".

Definition state := total_map nat.


Inductive aexp : Type :=
  | ANum (n : nat)
  | AId (x : string) (* <--- NEW *)
  | APlus (a1 a2 : aexp)
  | AMinus (a1 a2 : aexp)
  | AMult (a1 a2 : aexp).

Definition W : string := "W".
Definition X : string := "X".
Definition Y : string := "Y".
Definition Z : string := "Z".

Inductive bexp : Type :=
  | BTrue
  | BFalse
  | BEq (a1 a2 : aexp)
  | BNeq (a1 a2 : aexp)
  | BLe (a1 a2 : aexp)
  | BGt (a1 a2 : aexp)
  | BNot (b : bexp)
  | BAnd (b1 b2 : bexp).

Coercion AId : string >-> aexp.
Coercion ANum : nat >-> aexp.
Declare Custom Entry com.
Declare Scope com_scope.
Declare Custom Entry com_aux.
Notation "<{ e }>" := e (e custom com_aux) : com_scope.
Notation "e" := e (in custom com_aux at level 0, e custom com) : com_scope.
Notation "( x )" := x (in custom com, x at level 99) : com_scope.
Notation "x" := x (in custom com at level 0, x constr at level 0) : com_scope.
Notation "f x .. y" := (.. (f x) .. y)
                  (in custom com at level 0, only parsing,
                  f constr at level 0, x constr at level 9,
                  y constr at level 9) : com_scope.
Notation "x + y" := (APlus x y) 
  (in custom com at level 50, left associativity).
Notation "x - y" := (AMinus x y) 
  (in custom com at level 50, left associativity).
Notation "x * y" := (AMult x y) 
  (in custom com at level 40, left associativity).
Notation "'true'" := true (at level 1).
Notation "'true'" := BTrue (in custom com at level 0).
Notation "'false'" := false (at level 1).
Notation "'false'" := BFalse (in custom com at level 0).
Notation "x <= y" := (BLe x y) 
  (in custom com at level 70, no associativity).
Notation "x > y" := (BGt x y) 
  (in custom com at level 70, no associativity).
Notation "x = y" := (BEq x y) 
  (in custom com at level 70, no associativity).
Notation "x <> y" := (BNeq x y) 
  (in custom com at level 70, no associativity).
Notation "x && y" := (BAnd x y) 
  (in custom com at level 80, left associativity).
Notation "'~' b" := (BNot b) 
  (in custom com at level 75, right associativity).
Open Scope com_scope.

Definition example_aexp : aexp := <{ 3 + (X * 2) }>.
Definition example_bexp : bexp := <{ true && ~(X <= 4) }>.

Fixpoint aeval (st : state) (* <--- NEW *)
               (a : aexp) : nat :=
  match a with
  | ANum n => n
  | AId x => st x (* <--- NEW *)
  | <{a1 + a2}> => (aeval st a1) + (aeval st a2)
  | <{a1 - a2}> => (aeval st a1) - (aeval st a2)
  | <{a1 * a2}> => (aeval st a1) * (aeval st a2)
  end.
Fixpoint beval (st : state) (* <--- NEW *)
               (b : bexp) : bool :=
  match b with
  | <{true}> => true
  | <{false}> => false
  | <{a1 = a2}> => (aeval st a1) =? (aeval st a2)
  | <{a1 <> a2}> => negb ((aeval st a1) =? (aeval st a2))
  | <{a1 <= a2}> => (aeval st a1) <=? (aeval st a2)
  | <{a1 > a2}> => negb ((aeval st a1) <=? (aeval st a2))
  | <{~ b1}> => negb (beval st b1)
  | <{b1 && b2}> => andb (beval st b1) (beval st b2)
  end.

Definition empty_st := (_ !-> 0).

 Notation "x '!->' v" := (x !-> v ; empty_st) (at level 100).
Example aexp1 :
    aeval (X !-> 5) <{ 3 + (X * 2) }>
  = 13.
Proof. reflexivity. Qed.

Example aexp2 :
    aeval (X !-> 5 ; Y !-> 4) <{ Z + (X * Y) }>
  = 20.
Proof. reflexivity. Qed.

Example bexp1 :
    beval (X !-> 5) <{ true && ~(X <= 4) }>
  = true.
Proof. reflexivity. Qed.


Inductive com : Type :=
  | CSkip
  | CAsgn (x : string) (a : aexp)
  | CSeq (c1 c2 : com)
  | CIf (b : bexp) (c1 c2 : com)
  | CWhile (b : bexp) (c : com).

 Notation "'skip'" :=
         CSkip (in custom com at level 0) : com_scope.
Notation "x := y" :=
         (CAsgn x y)
            (in custom com at level 0, x constr at level 0,
             y at level 85, no associativity) : com_scope.
Notation "x ; y" :=
         (CSeq x y)
           (in custom com at level 90,
            right associativity) : com_scope.
Notation "'if' x 'then' y 'else' z 'end'" :=
         (CIf x y z)
           (in custom com at level 89, x at level 99,
            y at level 99, z at level 99) : com_scope.
Notation "'while' x 'do' y 'end'" :=
         (CWhile x y)
           (in custom com at level 89, x at level 99,
            y at level 99) : com_scope.

Definition fact_in_coq : com := 
  <{ Z := X;
     Y := 1;
     while Z <> 0 do
       Y := Y * Z;
       Z := Z - 1
     end }>.

(* Both if then end and while do end uses end,
   so this locate will find both *)
Locate "end".

Reserved Notation
         "st '=[' c ']=>' st'"
         (at level 40, c custom com at level 99,
          st constr, st' constr at next level).

Inductive ceval : com -> state -> state -> Prop :=
  | E_Skip : forall st,
      st =[ skip ]=> st
  | E_Asgn  : forall st a n x,
      aeval st a = n ->
      st =[ x := a ]=> (x !-> n ; st)
  | E_Seq : forall c1 c2 st st' st'',
      st  =[ c1 ]=> st'  ->
      st' =[ c2 ]=> st'' ->
      st  =[ c1 ; c2 ]=> st''
  | E_IfTrue : forall st st' b c1 c2,
      beval st b = true ->
      st =[ c1 ]=> st' ->
      st =[ if b then c1 else c2 end]=> st'
  | E_IfFalse : forall st st' b c1 c2,
      beval st b = false ->
      st =[ c2 ]=> st' ->
      st =[ if b then c1 else c2 end]=> st'
  | E_WhileFalse : forall b st c,
      beval st b = false ->
      st =[ while b do c end ]=> st
  | E_WhileTrue : forall st st' st'' b c,
      beval st b = true ->
      st  =[ c ]=> st' ->
      st' =[ while b do c end ]=> st'' ->
      st  =[ while b do c end ]=> st''

  where "st =[ c ]=> st'" := (ceval c st st').

 Example ceval_example1:
  empty_st =[
     X := 2;
     if (X <= 1)
       then Y := 3
       else Z := 4
     end
  ]=> (Z !-> 4 ; X !-> 2).
Proof.
  (* We must supply the intermediate state *)
  apply E_Seq with (X !-> 2).
  - (* assignment command *)
    apply E_Asgn. reflexivity.
  - (* if command *)
    apply E_IfFalse.
    + reflexivity.
    + apply E_Asgn. reflexivity.
Qed.

Example ceval_example2:
  empty_st =[
    X := 0;
    Y := 1;
    Z := 2
  ]=> (Z !-> 2 ; Y !-> 1 ; X !-> 0).
Proof.
  apply E_Seq with (X !-> 0).  
  { apply E_Asgn. reflexivity. }
  apply (E_Seq _ _ (X !-> 0) (Y !-> 1; X !-> 0) _).
  { apply E_Asgn. reflexivity. }
  apply E_Asgn. reflexivity.
Qed.

Set Printing Implicit.
Check @ceval_example2.

Definition pup_to_n : com :=
  <{ 
     Y := 0;
     while X <> 0 do
       Y := Y + X;
       X := X - 1
     end }>.

Theorem pup_to_2_ceval :
  (X !-> 2) =[
    pup_to_n
  ]=> (X !-> 0 ; Y !-> 3 ; X !-> 1 ; Y !-> 2 ; Y !-> 0 ; X !-> 2).
Proof.
  unfold pup_to_n. 
  apply (E_Seq _ _ (X !-> 2) (Y !-> 0; X !-> 2) _).
  { apply E_Asgn. reflexivity. }
  apply E_WhileTrue with (st' := (X !-> 1; Y !-> 2; Y !-> 0; X !-> 2)).
  { reflexivity. }
  { 
    apply E_Seq with (st' := (Y !-> 2; Y !-> 0; X !-> 2));
      apply E_Asgn; reflexivity.
  }
  {
    apply E_WhileTrue with 
      (st' := (X !-> 0; Y !-> 3; X !-> 1; Y !-> 2; Y !-> 0; X !-> 2)).
    - reflexivity.
    - apply E_Seq with 
    (st' := (Y !-> 3; X !-> 1; Y !-> 2; Y !-> 0; X !-> 2));
      apply E_Asgn; reflexivity.
    - apply E_WhileFalse.
      reflexivity.
  }
Qed.

Theorem ceval_deterministic: forall c st st1 st2,
     st =[ c ]=> st1  ->
     st =[ c ]=> st2 ->
     st1 = st2.
Proof.
  intros c st st1 st2 E1 E2.
  generalize dependent st2.
  induction E1; intros st2 E2; inversion E2; subst.
  - (* E_Skip *) reflexivity.
  - (* E_Asgn *) reflexivity.
  - (* E_Seq *)
    rewrite (IHE1_1 st'0 H1) in *.
    apply IHE1_2. assumption.
  - (* E_IfTrue, b evaluates to true *)
      apply IHE1. assumption.
  - (* E_IfTrue,  b evaluates to false (contradiction) *)
      rewrite H in H5. discriminate.
  - (* E_IfFalse, b evaluates to true (contradiction) *)
      rewrite H in H5. discriminate.
  - (* E_IfFalse, b evaluates to false *)
      apply IHE1. assumption.
  - (* E_WhileFalse, b evaluates to false *)
    reflexivity.
  - (* E_WhileFalse, b evaluates to true (contradiction) *)
    rewrite H in H2. discriminate.
  - (* E_WhileTrue, b evaluates to false (contradiction) *)
    rewrite H in H4. discriminate.
  - (* E_WhileTrue, b evaluates to true *)
    rewrite (IHE1_1 st'0 H3) in *.
    apply IHE1_2. assumption.  Qed.


Definition plus2 : com :=
  <{ X := X + 2 }>.
Definition XtimesYinZ : com :=
  <{ Z := X * Y }>.

Theorem plus2_spec : forall st n st',
  st X = n ->
  st =[ plus2 ]=> st' ->
  st' X = n + 2.
Proof.
  intros st n st' HX Heval.
  inversion Heval. subst. clear Heval. simpl.
  apply t_update_eq.  
Qed.

Theorem xtimesyinz_spec : forall st (nx ny : nat) st',
  st X = nx -> st Y = ny -> 
  st =[ XtimesYinZ ]=> st' ->
  st' Z = nx*ny.
Proof.
  intros st nx ny st'.
  intros H1 H2 H3.
  inversion H3.
  simpl in H6.
  rewrite -> H1, -> H2 in H6.
  rewrite -> H6.
  apply t_update_eq.
Qed.

Definition subtract_slowly_body : com :=
  <{ Z := Z - 1 ;
     X := X - 1 }>.
Definition subtract_slowly : com :=
  <{ while X <> 0 do
       subtract_slowly_body
     end }>.
Definition subtract_3_from_5_slowly : com :=
  <{ X := 3 ;
     Z := 5 ;
     subtract_slowly }>.
Definition loop : com :=
  <{ while true do
       skip
     end }>.

Theorem loop_never_stops : forall st st',
  ~(st =[ loop ]=> st').
Proof.
  intros st st' contra. unfold loop in contra.
  remember <{ while true do skip end }> as loopdef
           eqn:Heqloopdef.
  induction contra; 
  try discriminate.
  - inversion Heqloopdef.
    rewrite -> H1 in H. simpl in H.
    discriminate H.
  - apply IHcontra2 in Heqloopdef.
    exact Heqloopdef.
Qed.


Fixpoint no_whiles (c : com) : bool :=
  match c with
  | <{ skip }> =>
      true
  | <{ _ := _ }> =>
      true
  | <{ c1 ; c2 }> =>
      andb (no_whiles c1) (no_whiles c2)
  | <{ if _ then ct else cf end }> =>
      andb (no_whiles ct) (no_whiles cf)
  | <{ while _ do _ end }>  =>
      false
  end.

Inductive no_whilesR: com -> Prop :=
  | NoWSkip : no_whilesR CSkip
  | NoWAsgn (x : string) (a : aexp) : 
      no_whilesR (CAsgn x a)
  | NoWSeq (c1 c2 : com) :
      (no_whilesR c1) ->
      (no_whilesR c2) ->
      no_whilesR (CSeq c1 c2)
  | NoWIf (b : bexp) (c1 c2 : com) :
      (no_whilesR c1) ->
      (no_whilesR c2) ->
      no_whilesR (CIf b c1 c2)
.

Theorem no_whiles_eqv:
  forall c, no_whiles c = true <-> no_whilesR c.
Proof.
  intros c. split; intros H.
  - induction c.
    + apply NoWSkip.
    + apply NoWAsgn.
    + simpl in H.
      apply andb_prop in H.
      destruct H as [H1 H2].
      apply IHc1 in H1. apply IHc2 in H2.
      apply NoWSeq.
      * exact H1.
      * exact H2.
    + simpl in H.
      apply andb_prop in H.
      destruct H as [H1 H2].
      apply IHc1 in H1. apply IHc2 in H2.
      apply NoWIf.
      * exact H1.
      * exact H2.
    + simpl in H.
      discriminate H.
  - induction H.
    + reflexivity.
    + reflexivity.
    + simpl.
      rewrite -> IHno_whilesR1, -> IHno_whilesR2.
      reflexivity.
    + simpl.
      rewrite -> IHno_whilesR1, -> IHno_whilesR2.
      reflexivity.
Qed.


(* Terminating means we can calculate (find) a st'
   for whatever initial state it has *)
Theorem no_whiles_terminating :
  forall (c : com), no_whilesR c ->
  forall st : state, exists st' : state,
  st =[c]=> st'.
Proof.
  intros c H.
  induction H; intros st.
  - exists st. apply E_Skip.
  - exists (x !-> (aeval st a); st). apply E_Asgn. reflexivity.
  - destruct (IHno_whilesR1 st) as [st' IH1].
    destruct (IHno_whilesR2 st') as [st'' IH2].
    exists st''. 
    apply (E_Seq c1 c2 st st' st'' IH1 IH2).
  - destruct (beval st b) eqn:Eqb.
    + destruct (IHno_whilesR1 st) as [st' IH1].
      exists st'. apply E_IfTrue.
      { exact Eqb. } { exact IH1. }
    + destruct (IHno_whilesR2 st) as [st' IH2].
      exists st'. apply E_IfFalse.
      { exact Eqb. } { exact IH2. }
Qed.
