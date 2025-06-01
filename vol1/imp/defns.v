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

Module AExp.
Inductive aexp : Type :=
  | ANum (n : nat)
  | APlus (a1 a2 : aexp)
  | AMinus (a1 a2 : aexp)
  | AMult (a1 a2 : aexp).
Inductive bexp : Type :=
  | BTrue
  | BFalse
  | BEq (a1 a2 : aexp)
  | BNeq (a1 a2 : aexp)
  | BLe (a1 a2 : aexp)
  | BGt (a1 a2 : aexp)
  | BNot (b : bexp)
  | BAnd (b1 b2 : bexp).
(* Why choose BTrue + BFalse over BBool?
   Is it unintentional or not?
   At least I tested with the ' version
    that they yield the same values *)
(*Inductive bexp' : Type :=
  | BBool (b : bool)
  | BEq' (a1 a2 : aexp)
  | BNeq' (a1 a2 : aexp)
  | BLe' (a1 a2 : aexp)
  | BGt' (a1 a2 : aexp)
  | BNot' (b : bexp')
  | BAnd' (b1 b2 : bexp').
 *)

Fixpoint aeval (a : aexp) : nat :=
  match a with
  | ANum n => n
  | APlus a1 a2 => (aeval a1) + (aeval a2)
  | AMinus a1 a2 => (aeval a1) - (aeval a2)
  | AMult a1 a2 => (aeval a1) * (aeval a2)
  end.
Example test_aeval1:
  aeval (APlus (ANum 2) (ANum 2)) = 4.
Proof. reflexivity. Qed.

Fixpoint beval (b : bexp) : bool :=
  match b with
  | BTrue => true
  | BFalse => false
  | BEq a1 a2 => (aeval a1) =? (aeval a2)
  | BNeq a1 a2 => negb ((aeval a1) =? (aeval a2))
  | BLe a1 a2 => (aeval a1) <=? (aeval a2)
  | BGt a1 a2 => negb ((aeval a1) <=? (aeval a2))
  | BNot b1 => negb (beval b1)
  | BAnd b1 b2 => andb (beval b1) (beval b2)
  end.
(*Fixpoint beval' (b : bexp') : bool :=
  match b with
  | BBool b => b
  | BEq' a1 a2 => (aeval a1) =? (aeval a2)
  | BNeq' a1 a2 => negb ((aeval a1) =? (aeval a2))
  | BLe' a1 a2 => (aeval a1) <=? (aeval a2)
  | BGt' a1 a2 => negb ((aeval a1) <=? (aeval a2))
  | BNot' b1 => negb (beval' b1)
  | BAnd' b1 b2 => andb (beval' b1) (beval' b2)
   end.*)

Example test_beval2:
  beval (BNot BTrue) = false.
Proof. reflexivity. Qed.
(*Example test_beval'2:
  beval' (BNot' (BBool true)) = false.
   Proof. reflexivity. Qed.*)


Fixpoint optimize_0plus (a:aexp) : aexp :=
  match a with
  | ANum n => ANum n
  | APlus (ANum 0) e2 => optimize_0plus e2
  | APlus e1 e2 => APlus (optimize_0plus e1) (optimize_0plus e2)
  | AMinus e1 e2 => AMinus (optimize_0plus e1) (optimize_0plus e2)
  | AMult e1 e2 => AMult (optimize_0plus e1) (optimize_0plus e2)
  end.

Example test_optimize_0plus:
  optimize_0plus (APlus (ANum 2)
                        (APlus (ANum 0)
                               (APlus (ANum 0) (ANum 1))))
  = APlus (ANum 2) (ANum 1).
Proof. reflexivity. Qed.

Theorem optimize_0plus_sound: forall a,
  aeval (optimize_0plus a) = aeval a.
Proof.
  intros a. induction a.
  - (* ANum *) reflexivity.
  - (* APlus *) destruct a1 eqn:Ea1.
    + (* a1 = ANum n *) destruct n eqn:En.
      * (* n = 0 *) simpl. apply IHa2.
      * (* n <> 0 *) simpl. rewrite IHa2. reflexivity.
    + (* a1 = APlus a1_1 a1_2 *)
      simpl. simpl in IHa1. rewrite IHa1.
      rewrite IHa2. reflexivity.
    + (* a1 = AMinus a1_1 a1_2 *)
      simpl. simpl in IHa1. rewrite IHa1.
      rewrite IHa2. reflexivity.
    + (* a1 = AMult a1_1 a1_2 *)
      simpl. simpl in IHa1. rewrite IHa1.
      rewrite IHa2. reflexivity.
  - (* AMinus *)
    simpl. rewrite IHa1. rewrite IHa2. reflexivity.
  - (* AMult *)
    simpl. rewrite IHa1. rewrite IHa2. reflexivity. Qed.


Theorem silly1 : forall (P : Prop), P -> P.
Proof.
  intros P HP.
  try reflexivity. (* Plain reflexivity would have failed. *)
  apply HP. (* We can still finish the proof in some other way. *)
Qed.
Theorem silly2 : forall ae, aeval ae = aeval ae.
Proof.
    try reflexivity. (* This just does reflexivity. *)
Qed.

Lemma foo : forall n, 0 <=? n = true.
Proof.
  intros.
  destruct n.
    (* Leaves two subgoals, which are discharged identically...  *)
    - (* n=0 *) simpl. reflexivity.
    - (* n=Sn' *) simpl. reflexivity.
Qed.

Lemma foo' : forall n, 0 <=? n = true.
Proof.
  intros.
  (* destruct the current goal *)
  destruct n;
  (* then simpl each resulting subgoal *)
  simpl;
  (* and do reflexivity on each resulting subgoal *)
  reflexivity.
Qed.

Theorem optimize_0plus_sound': forall a,
  aeval (optimize_0plus a) = aeval a.
Proof.
  intros a.
  induction a;
    (* Most cases follow directly by the IH... *)
    try (simpl; rewrite IHa1; rewrite IHa2; reflexivity).
    (* ... but the remaining cases -- ANum and APlus --
       are different: *)
  - (* ANum *) reflexivity.
  - (* APlus *)
    destruct a1 eqn:Ea1;
      (* Again, most cases follow directly by the IH: *)
      try (simpl; simpl in IHa1; rewrite IHa1;
           rewrite IHa2; reflexivity).
    (* The interesting case, on which the try...
       does nothing, is when e1 = ANum n. In this
       case, we have to destruct n (to see whether
       the optimization applies) and rewrite with the
       induction hypothesis. *)
    + (* a1 = ANum n *) destruct n eqn:En;
      simpl; rewrite IHa2; reflexivity. 
Qed.

Theorem optimize_0plus_sound'': forall a,
  aeval (optimize_0plus a) = aeval a.
Proof.
  intros a.
  induction a;
    (* Most cases follow directly by the IH *)
    try (simpl; rewrite IHa1; rewrite IHa2; reflexivity);
    (* ... or are immediate by definition *)
    try reflexivity.
  (* The interesting case is when a = APlus a1 a2. *)
  - (* APlus *)
    destruct a1; try (simpl; simpl in IHa1; rewrite IHa1;
                      rewrite IHa2; reflexivity).
    + (* a1 = ANum n *) destruct n;
      simpl; rewrite IHa2; reflexivity. Qed.

Theorem In10 : In 10 [1;2;3;4;5;6;7;8;9;10].
Proof.
  repeat (try (left; reflexivity); right).
Qed.

Theorem In10' : In 10 [1;2;3;4;5;6;7;8;9;10].
Proof.
  repeat simpl.
  repeat (left; reflexivity).
  repeat (right; try (left; reflexivity)).
Qed.

Theorem repeat_loop : forall (m n : nat),
  m + n = n + m.
Proof.
  intros m n.
  (* Uncomment the next line to see the infinite loop occur.  You will
     then need to interrupt Coq to make it listen to you again.  (In
     Proof General, C-c C-c does this.) *)
  (* repeat rewrite Nat.add_comm. *)
Admitted.

Fixpoint optimize_0plus_b (b : bexp) : bexp
  :=
  match b with 
  | BTrue => BTrue
  | BFalse => BFalse
  | BEq a1 a2 => BEq (optimize_0plus a1) (optimize_0plus a2)
  | BNeq a1 a2 => BNeq (optimize_0plus a1) (optimize_0plus a2)
  | BLe a1 a2 => BLe (optimize_0plus a1) (optimize_0plus a2)
  | BGt a1 a2 => BGt (optimize_0plus a1) (optimize_0plus a2)
  | BNot b1 => BNot (optimize_0plus_b b1)
  | BAnd b1 b2 => BAnd (optimize_0plus_b b1) (optimize_0plus_b b2)
  end.

Example optimize_0plus_b_test1:
  optimize_0plus_b (BNot (BGt (APlus (ANum 0) (ANum 4)) (ANum 8))) =
                   (BNot (BGt (ANum 4) (ANum 8))).
Proof. 
  repeat (unfold optimize_0plus_b).
  repeat (unfold optimize_0plus).
  reflexivity.
Qed.
Example optimize_0plus_b_test2:
  optimize_0plus_b (BAnd (BLe (APlus (ANum 0) (ANum 4)) (ANum 5)) BTrue) =
                   (BAnd (BLe (ANum 4) (ANum 5)) BTrue).
Proof. 
  (* For both of the two, it turns out we could simply do
  simpl. reflexivity.
  But which of course does not use what we have learned, repeat.
  I suppose simpl might use repeat or similar things in its impl.
  *)
  repeat (unfold optimize_0plus_b).
  repeat (unfold optimize_0plus).
  reflexivity.
Qed.

Theorem optimize_0plus_b_sound : forall b,
  beval (optimize_0plus_b b) = beval b.
Proof.
  induction b; simpl;
  (* May need to use the previous result multiple times *)
  repeat (rewrite optimize_0plus_sound);
  (* Some ctor has one arg : bexp *)
  try (rewrite IHb);
  (* Some ctor has two args : bexp *)
  try (rewrite IHb1; rewrite IHb2);
  try reflexivity.
  (* Boom, perhaps surprisingly, it solves all of the subgoals. *)
Qed.

(*
Design exercise: The optimization implemented by our optimize_0plus function is
   only one of many possible optimizations on arithmetic and boolean
   expressions. Write a more sophisticated optimizer and prove it correct. (You
   will probably find it easiest to start small -- add just a single, simple
   optimization and its correctness proof -- and build up incrementally to
   something more interesting.)
*)

(* I plan to add 0mult, 1mult, in addition to 0plus. *)
Fixpoint optimize_many (a:aexp) : aexp :=
  match a with
  | ANum n => ANum n
  | APlus (ANum 0) e2 => optimize_many e2
  | APlus e1 e2 => APlus (optimize_many e1) (optimize_many e2)
  | AMinus e1 e2 => AMinus (optimize_many e1) (optimize_many e2)
  | AMult (ANum 0) e2 => ANum 0
  | AMult (ANum 1) e2 => optimize_many e2
  | AMult e1 e2 => AMult (optimize_many e1) (optimize_many e2)
  end.

Theorem optimize_many_sound: forall a,
  aeval (optimize_many a) = aeval a.
Proof.
  induction a;
  simpl;
  try (rewrite IHa);
  try (rewrite IHa1; rewrite IHa2);
  try reflexivity;   
  destruct a1;
    simpl;
    simpl in IHa1;
    repeat (rewrite IHa1);
    repeat (rewrite IHa2);
    try reflexivity.
    + destruct n.
      * rewrite -> IHa2. simpl. reflexivity.
      * simpl. rewrite -> IHa2. reflexivity.
    + destruct n.
      * simpl. reflexivity.
      * simpl. 
        destruct n; simpl; rewrite -> IHa2; lia.
Qed.
End AExp.
