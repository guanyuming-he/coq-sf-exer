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


Inductive sinstr : Type :=
| SPush (n : nat)
| SLoad (x : string)
| SPlus
| SMinus
| SMult.

Fixpoint s_execute (st : state) (stack : list nat)
  (prog : list sinstr) : list nat
  :=
  match prog with
  | [] => stack 
  | h::t =>
      match h with
      | SPush n =>
          s_execute st (n::stack) t 
      | SLoad x =>
          s_execute st ((st x)::stack) t 
      | SPlus =>
          match stack with 
          | [] => s_execute st stack t 
          | top::rest =>
              match rest with
              | [] => s_execute st stack t
              | top'::rest' =>
                  s_execute st ((top'+top)::rest') t
              end
          end
      | SMinus =>
          match stack with 
          | [] => s_execute st stack t 
          | top::rest =>
              match rest with
              | [] => s_execute st stack t
              | top'::rest' =>
                  s_execute st ((top'-top)::rest') t
              end
          end
      | SMult =>
          match stack with 
          | [] => s_execute st stack t 
          | top::rest =>
              match rest with
              | [] => s_execute st stack t
              | top'::rest' =>
                  s_execute st ((top'*top)::rest') t
              end
          end
      end
  end.



Check s_execute.
Example s_execute1 :
     s_execute empty_st []
       [SPush 5; SPush 3; SPush 1; SMinus]
   = [2; 5].
Proof. reflexivity. Qed.

Example s_execute2 :
     s_execute (X !-> 3) [3;4]
       [SPush 4; SLoad X; SMult; SPlus]
   = [15; 4].
Proof. reflexivity. Qed.


(*
Inductive aexp : Type :=
  | ANum (n : nat)
  | AId (x : string) (* <--- NEW *)
  | APlus (a1 a2 : aexp)
  | AMinus (a1 a2 : aexp)
  | AMult (a1 a2 : aexp).
 *)

Fixpoint s_compile (e : aexp) : list sinstr
  :=
  match e with 
  | ANum n => [SPush n]
  | AId x => [SLoad x]
  | APlus a1 a2 =>
      (s_compile a1) ++ (s_compile a2) ++ [SPlus] 
  | AMinus a1 a2 =>
      (s_compile a1) ++ (s_compile a2) ++ [SMinus] 
  | AMult a1 a2 =>
      (s_compile a1) ++ (s_compile a2) ++ [SMult] 
  end.

Example s_compile1 :
  s_compile <{ X - (2 * Y) }>
  = [SLoad X; SPush 2; SLoad Y; SMult; SMinus].
Proof.
  reflexivity.
Qed.

Theorem execute_app : forall st p1 p2 stack,
  s_execute st stack (p1 ++ p2) =
  s_execute st (s_execute st stack p1) p2.
Proof.
  intros st. induction p1.
  - intros p2 stack.
    simpl. reflexivity.
  - intros p2 stack.
    destruct a.
    + simpl. 
      apply (IHp1 p2 (n::stack)).
    + simpl.
      apply (IHp1 p2 (st x::stack)).
      (* Don't know how to simplify the next
         three very similar ones. *)
    + simpl.
      destruct stack as [|t stack'].
      * simpl. apply IHp1.
      * destruct stack' as [|t' stack''].
        { simpl. apply IHp1. }
        { simpl. apply (IHp1 p2 (t' + t :: stack'')). }
    + simpl.
      destruct stack as [|t stack'].
      * simpl. apply IHp1.
      * destruct stack' as [|t' stack''].
        { simpl. apply IHp1. }
        { simpl. apply (IHp1 p2 (t' - t :: stack'')). }
    + simpl.
      destruct stack as [|t stack'].
      * simpl. apply IHp1.
      * destruct stack' as [|t' stack''].
        { simpl. apply IHp1. }
        { simpl. apply (IHp1 p2 (t' * t :: stack'')). }
Qed.



Lemma s_compile_correct_aux : forall st e stack,
  s_execute st stack (s_compile e) = aeval st e :: stack.
Proof.
  intros st. induction e; intros stack;
  (* The two simple SPush and SLoad *)
  try reflexivity;
  (* The three operations *)
  try (
    simpl;
    (* Use the previous thm to separate the execution of 
       s_compile e1 out *)
    rewrite (execute_app st (s_compile e1) _ stack);
    rewrite -> IHe1;
    (* Use the previous thm to separate the execution of 
       s_compile e2 out *)
    rewrite (execute_app st (s_compile e2) _ _);
    rewrite -> IHe2;
    simpl; reflexivity
  ).
Qed.

Theorem s_compile_correct : forall (st : state) (e : aexp),
  s_execute st [] (s_compile e) = [ aeval st e ].
Proof.
  intros st e.
  rewrite -> s_compile_correct_aux.
  reflexivity.
Qed.


(* Short circuit beval *)
Fixpoint beval_sc (st : state) 
               (b : bexp) : bool :=
  match b with
  | <{true}> => true
  | <{false}> => false
  | <{a1 = a2}> => (aeval st a1) =? (aeval st a2)
  | <{a1 <> a2}> => negb ((aeval st a1) =? (aeval st a2))
  | <{a1 <= a2}> => (aeval st a1) <=? (aeval st a2)
  | <{a1 > a2}> => negb ((aeval st a1) <=? (aeval st a2))
  | <{~ b1}> => negb (beval st b1)
  | <{b1 && b2}> => if (beval st b1) then (beval st b2) else false
  end.

Theorem beval_beval_sc_eq : 
  forall st b,
  beval st b = beval_sc st b.
Proof.
  intros st. destruct b;
  try reflexivity.
Qed.

Module BreakImp.

Inductive com : Type :=
  | CSkip
  | CBreak (* <--- NEW *)
  | CAsgn (x : string) (a : aexp)
  | CSeq (c1 c2 : com)
  | CIf (b : bexp) (c1 c2 : com)
  | CWhile (b : bexp) (c : com).
Notation "'break'" := CBreak (in custom com at level 0).
Notation "'skip'" :=
         CSkip (in custom com at level 0) : com_scope.
Notation "x := y" :=
         (CAsgn x y)
            (in custom com at level 0, x constr at level 0,
             y at level 85, no associativity) : com_scope.
Notation "x ; y" :=
         (CSeq x y)
           (in custom com at level 90, right associativity) : com_scope.
Notation "'if' x 'then' y 'else' z 'end'" :=
         (CIf x y z)
           (in custom com at level 89, x at level 99,
            y at level 99, z at level 99) : com_scope.
Notation "'while' x 'do' y 'end'" :=
         (CWhile x y)
            (in custom com at level 89, x at level 99, y at level 99) : com_scope.


Inductive result : Type :=
  | SContinue
  | SBreak.

Reserved Notation "st '=[' c ']=>' st' '/' s"
     (at level 40, c custom com at level 99, st' constr at next level).

Inductive ceval : com -> state -> result -> state -> Prop :=
  | E_Skip : forall st,
      st =[ CSkip ]=> st / SContinue
  | E_Break : forall st, 
      st =[ CBreak ]=> st / SBreak
  | E_Asgn : forall st x a n,
      aeval st a = n ->
      st =[ CAsgn x a ]=> (x !-> n; st) / SContinue
  | E_SeqBrk : forall c1 c2 st st',
      st  =[ c1 ]=> st' / SBreak  ->
      st  =[ c1 ; c2 ]=> st' / SBreak
  | E_SeqCont : forall c1 c2 st st' st'' s,
      st  =[ c1 ]=> st' / SContinue  ->
      st' =[ c2 ]=> st'' / s ->
      st  =[ c1 ; c2 ]=> st'' / s
  | E_IfTrue : forall st st' b c1 c2 s,
      beval st b = true ->
      st =[ c1 ]=> st' / s ->
      st =[ if b then c1 else c2 end]=> st' / s
  | E_IfFalse : forall st st' b c1 c2 s,
      beval st b = false ->
      st =[ c2 ]=> st' / s ->
      st =[ if b then c1 else c2 end]=> st' / s
  | E_WhileFalse : forall b st c,
      beval st b = false ->
      st =[ while b do c end ]=> st / SContinue
  | E_WhileTrueCont : forall st st' st'' b c s,
      beval st b = true ->
      st  =[ c ]=> st' / SContinue ->
      st' =[ while b do c end ]=> st'' / s ->
      (* Here s can only be SContinue anyway, as proven 
         later in while_continue *)
      st  =[ while b do c end ]=> st'' / SContinue
  | E_WhileTrueBrk : forall st st' b c,
      beval st b = true ->
      st  =[ c ]=> st' / SBreak ->
      st  =[ while b do c end ]=> st' / SContinue

  where "st '=[' c ']=>' st' '/' s" := (ceval c st s st').

Theorem break_ignore : forall c st st' s,
     st =[ break; c ]=> st' / s ->
     st = st'.
Proof.
  intros c st st' s H.
  inversion H.
  - inversion H5. reflexivity.
  - inversion H2. (* impossible *)
Qed.
  

Theorem while_continue : forall b c st st' s,
  st =[ while b do c end ]=> st' / s ->
  s = SContinue.
Proof.
  intros b c st st' s H.
  inversion H; reflexivity.
Qed.

Theorem while_stops_on_break : forall b c st st',
  beval st b = true ->
  st =[ c ]=> st' / SBreak ->
  st =[ while b do c end ]=> st' / SContinue.
Proof.
  intros b c st st' H1 H2.
  apply E_WhileTrueBrk.
  - exact H1.
  - exact H2.
Qed.

Theorem seq_continue : forall c1 c2 st st' st'',
  st =[ c1 ]=> st' / SContinue ->
  st' =[ c2 ]=> st'' / SContinue ->
  st =[ c1 ; c2 ]=> st'' / SContinue.
Proof.
  intros c1 c2 st st' st'' H1 H2.
  apply E_SeqCont with (st' := st').
  - exact H1.
  - exact H2.
Qed.

Theorem seq_stops_on_break : forall c1 c2 st st',
  st =[ c1 ]=> st' / SBreak ->
  st =[ c1 ; c2 ]=> st' / SBreak.
Proof.
  intros c1 c2 st st' H.
  apply E_SeqBrk.
  exact H.
Qed.


Theorem while_break_true : forall b c st st',
  st =[ while b do c end ]=> st' / SContinue ->
  beval st' b = true ->
  exists st'', st'' =[ c ]=> st' / SBreak.
Proof.
  intros b c st st' H1. 
  (* here is like what's done in loop_never_stops *)
  remember <{ while b do c end }> as loopdef eqn:Heqloopdef.
  induction H1; intros H2; try discriminate Heqloopdef.
  - inversion Heqloopdef.
    rewrite H1 in H. rewrite H in H2. discriminate H2.
  - apply (IHceval2 Heqloopdef H2).
  - inversion Heqloopdef.
    rewrite H4 in H1.
    exists st. exact H1.
Qed.

Theorem ceval_deterministic: forall (c:com) st st1 st2 s1 s2,
     st =[ c ]=> st1 / s1 ->
     st =[ c ]=> st2 / s2 ->
     st1 = st2 /\ s1 = s2.
Proof.
  intros c st st1 st2 s1 s2 H1. 
  (* Note that H1 is not dependent on st2 and s2 *)
  generalize dependent st2.
  generalize dependent s2.
  induction H1; intros s2 st2 H2.
  - inversion H2. split; reflexivity.
  - inversion H2. split; reflexivity.
  - inversion H2.
    split.
    + rewrite -> H in H6. rewrite -> H6. reflexivity.
    + reflexivity.
  - inversion H2. 
    + apply IHceval in H6.
      exact H6.
    + apply IHceval in H3.
      destruct H3 as [_ contra].
      discriminate contra.
  - inversion H2.
    + apply IHceval1 in H5.
      destruct H5 as [_ contra].
      discriminate contra.
    + apply IHceval1 in H1.
      destruct H1 as [H1 _].
      rewrite <- H1 in H6. apply IHceval2 in H6.
      exact H6.
  - inversion H2.
    + apply IHceval in H9.
      exact H9.
    + rewrite -> H in H8. discriminate H8.
  - inversion H2.
    + rewrite -> H in H8. discriminate H8.
    + apply IHceval in H9.
      exact H9.
  - inversion H2; split; 
    try reflexivity;
    try (rewrite H in H3; discriminate H3).
  - inversion H2; subst.
    + rewrite -> H in H6. discriminate H6.
    + destruct (IHceval1 _ _ H4) as [H4' _].
      rewrite <- H4' in H8.
      destruct (IHceval2 _ _ H8) as [H8' _].
      split.
      * exact H8'.
      * reflexivity.
    + destruct (IHceval1 _ _ H7) as [_ contra].
      discriminate contra.
  - inversion H2; subst.
    + rewrite -> H in H7. discriminate H7.
    + destruct (IHceval _ _ H5) as [_ contra].
      discriminate contra.
    + destruct (IHceval _ _ H8) as [H8' _].
      split.
      * exact H8'.
      * reflexivity.

  (* An attempt to induct on c, which seems to be stuck in the end 
  induction c; intros st st1 st2 s1 s2 H1 H2; split;
  try (inversion H1; inversion H2; reflexivity);
  try (
    inversion H1; inversion H2; 
    rewrite <- H4; rewrite <- H7;
    reflexivity
  ).
  - inversion H1. inversion H2.
    rewrite -> H6 in H12.
    rewrite H12. reflexivity.
  - inversion H1; inversion H2.
    + destruct (IHc1 _ _ _ _ _ H6 H12) as [HF _].
      exact HF.
    + destruct (IHc1 _ _ _ _ _ H6 H9) as [_ contra].
      discriminate contra.
    + destruct (IHc1 _ _ _ _ _ H3 H13) as [_ contra].
      discriminate contra.
    + destruct (IHc1 _ _ _ _ _ H3 H10) as [H20 _].
      rewrite <- H20 in H14.
      destruct (IHc2 _ _ _ _ _ H7 H14) as [HF _].
      exact HF.
  - inversion H1; inversion H2.
    + reflexivity.
    + destruct (IHc1 _ _ _ _ _ H6 H9) as [_ contra].
      discriminate contra.
    + destruct (IHc1 _ _ _ _ _ H3 H13) as [_ contra].
      discriminate contra.
    + destruct (IHc1 _ _ _ _ _ H3 H10) as [H20 _].
      rewrite <- H20 in H14.
      destruct (IHc2 _ _ _ _ _ H7 H14) as [_ HF].
      exact HF.
  - inversion H1; inversion H2.
    + destruct (IHc1 _ _ _ _ _ H8 H16) as [HF _].
      exact HF.
    + rewrite -> H7 in H15. 
      discriminate H15.
    + rewrite -> H7 in H15. 
      discriminate H15.
    + destruct (IHc2 _ _ _ _ _ H8 H16) as [HF _].
      exact HF.
  - inversion H1; inversion H2.
    + destruct (IHc1 _ _ _ _ _ H8 H16) as [_ HF].
      exact HF.
    + rewrite -> H7 in H15. 
      discriminate H15.
    + rewrite -> H7 in H15. 
      discriminate H15.
    + destruct (IHc2 _ _ _ _ _ H8 H16) as [_ HF].
      exact HF.
      (* Here, for while, I can't blindly invert the execution,
         as that leads me nowhere when b = true and c is not break. 
         Instead, use the previous result to always introduce a break point
       *)
  - destruct (beval st1 b) eqn:Eqb1, (beval st2 b) eqn:Eqb2.
    + (* To use while_break_true, a few conditions need to be established *)
      assert (s1 = SContinue) as H3.
      { apply while_continue in H1. exact H1. }
      assert (s2 = SContinue) as H4.
      { apply while_continue in H2. exact H2. }
      rewrite -> H3 in H1. rewrite -> H4 in H2.
      assert (H5 := (while_break_true _ _ _ _ H1 Eqb1)).
      assert (H6 := (while_break_true _ _ _ _ H2 Eqb2)).
  *)
Qed.

End BreakImp.


Module AddForLoop.

Inductive com : Type :=
  | CSkip
  | CBreak 
  | CAsgn (x : string) (a : aexp)
  | CSeq (c1 c2 : com)
  | CIf (b : bexp) (c1 c2 : com)
  | CWhile (b : bexp) (c : com)
  | CFor (b : bexp) (asgn iter c : com)
    (* It's like for (asgn i = ?; b i < ?; iter ++i) *)
.
Notation "'break'" := CBreak (in custom com at level 0).
Notation "'skip'" :=
         CSkip (in custom com at level 0) : com_scope.
Notation "x := y" :=
         (CAsgn x y)
            (in custom com at level 0, x constr at level 0,
             y at level 85, no associativity) : com_scope.
Notation "x ; y" :=
         (CSeq x y)
           (in custom com at level 90, right associativity) : com_scope.
Notation "'if' x 'then' y 'else' z 'end'" :=
         (CIf x y z)
           (in custom com at level 89, x at level 99,
            y at level 99, z at level 99) : com_scope.
Notation "'while' x 'do' y 'end'" :=
         (CWhile x y)
            (in custom com at level 89, x at level 99, y at level 99) : com_scope.
(* Why doesn't it work? *)
Notation "'for' asgn ';' b ';' iter 'do' c 'end'" :=
         (CFor b asgn iter c)
            (in custom com at level 88, 
            asgn at level 99, iter at level 99, c at level 99,
            b at level 99) : com_scope.

Inductive result : Type :=
  | SContinue
  | SBreak.

Reserved Notation "st '=[' c ']=>' st' '/' s"
     (at level 40, c custom com at level 99, st' constr at next level).

Inductive ceval : com -> state -> result -> state -> Prop :=
  | E_Skip : forall st,
      st =[ CSkip ]=> st / SContinue
  | E_Break : forall st, 
      st =[ CBreak ]=> st / SBreak
  | E_Asgn : forall st x a n,
      aeval st a = n ->
      st =[ CAsgn x a ]=> (x !-> n; st) / SContinue
  | E_SeqBrk : forall c1 c2 st st',
      st  =[ c1 ]=> st' / SBreak  ->
      st  =[ c1 ; c2 ]=> st' / SBreak
  | E_SeqCont : forall c1 c2 st st' st'' s,
      st  =[ c1 ]=> st' / SContinue  ->
      st' =[ c2 ]=> st'' / s ->
      st  =[ c1 ; c2 ]=> st'' / s
  | E_IfTrue : forall st st' b c1 c2 s,
      beval st b = true ->
      st =[ c1 ]=> st' / s ->
      st =[ if b then c1 else c2 end]=> st' / s
  | E_IfFalse : forall st st' b c1 c2 s,
      beval st b = false ->
      st =[ c2 ]=> st' / s ->
      st =[ if b then c1 else c2 end]=> st' / s
  | E_WhileFalse : forall b st c,
      beval st b = false ->
      st =[ while b do c end ]=> st / SContinue
  | E_WhileTrueCont : forall st st' st'' b c s,
      beval st b = true ->
      st  =[ c ]=> st' / SContinue ->
      st' =[ while b do c end ]=> st'' / s ->
      (* Here s can only be SContinue anyway, as proven 
         later in while_continue *)
      st  =[ while b do c end ]=> st'' / SContinue
  | E_WhileTrueBrk : forall st st' b c,
      beval st b = true ->
      st  =[ c ]=> st' / SBreak ->
      st  =[ while b do c end ]=> st' / SContinue
  (* It turns out that a for loop can be implemented with a while loop. *)
  | E_For : forall st st' s asgn b iter c,
      st =[ asgn ; while b do (c ; iter) end ]=> st' / s ->
      st =[ CFor b asgn iter c ]=> st' / s

  where "st '=[' c ']=>' st' '/' s" := (ceval c st s st').


(* It's exactly the same as the previous one without for loop,
  except the new case to handle for loop. *)
Theorem ceval_deterministic: forall (c:com) st st1 st2 s1 s2,
     st =[ c ]=> st1 / s1 ->
     st =[ c ]=> st2 / s2 ->
     st1 = st2 /\ s1 = s2.
Proof.
  intros c st st1 st2 s1 s2 H1. 
  (* Note that H1 is not dependent on st2 and s2 *)
  generalize dependent st2.
  generalize dependent s2.
  induction H1; intros s2 st2 H2.
  - inversion H2. split; reflexivity.
  - inversion H2. split; reflexivity.
  - inversion H2.
    split.
    + rewrite -> H in H6. rewrite -> H6. reflexivity.
    + reflexivity.
  - inversion H2. 
    + apply IHceval in H6.
      exact H6.
    + apply IHceval in H3.
      destruct H3 as [_ contra].
      discriminate contra.
  - inversion H2.
    + apply IHceval1 in H5.
      destruct H5 as [_ contra].
      discriminate contra.
    + apply IHceval1 in H1.
      destruct H1 as [H1 _].
      rewrite <- H1 in H6. apply IHceval2 in H6.
      exact H6.
  - inversion H2.
    + apply IHceval in H9.
      exact H9.
    + rewrite -> H in H8. discriminate H8.
  - inversion H2.
    + rewrite -> H in H8. discriminate H8.
    + apply IHceval in H9.
      exact H9.
  - inversion H2; split; 
    try reflexivity;
    try (rewrite H in H3; discriminate H3).
  - inversion H2; subst.
    + rewrite -> H in H6. discriminate H6.
    + destruct (IHceval1 _ _ H4) as [H4' _].
      rewrite <- H4' in H8.
      destruct (IHceval2 _ _ H8) as [H8' _].
      split.
      * exact H8'.
      * reflexivity.
    + destruct (IHceval1 _ _ H7) as [_ contra].
      discriminate contra.
  - inversion H2; subst.
    + rewrite -> H in H7. discriminate H7.
    + destruct (IHceval _ _ H5) as [_ contra].
      discriminate contra.
    + destruct (IHceval _ _ H8) as [H8' _].
      split.
      * exact H8'.
      * reflexivity.
  - inversion H2. subst.
    apply IHceval in H8.
    exact H8.
Qed.

End AddForLoop.
