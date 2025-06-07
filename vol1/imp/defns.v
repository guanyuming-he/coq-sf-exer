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

Module aevalR_first_try.
Inductive aevalR : aexp -> nat -> Prop :=
  | E_ANum (n : nat) :
      aevalR (ANum n) n
  | E_APlus (e1 e2 : aexp) (n1 n2 : nat) :
      aevalR e1 n1 ->
      aevalR e2 n2 ->
      aevalR (APlus e1 e2) (n1 + n2)
  | E_AMinus (e1 e2 : aexp) (n1 n2 : nat) :
      aevalR e1 n1 ->
      aevalR e2 n2 ->
      aevalR (AMinus e1 e2) (n1 - n2)
  | E_AMult (e1 e2 : aexp) (n1 n2 : nat) :
      aevalR e1 n1 ->
      aevalR e2 n2 ->
      aevalR (AMult e1 e2) (n1 * n2).
Module HypothesisNames.

Inductive aevalR : aexp -> nat -> Prop :=
  | E_ANum (n : nat) :
      aevalR (ANum n) n
  | E_APlus (e1 e2 : aexp) (n1 n2 : nat)
      (H1 : aevalR e1 n1)
      (H2 : aevalR e2 n2) :
      aevalR (APlus e1 e2) (n1 + n2)
  | E_AMinus (e1 e2 : aexp) (n1 n2 : nat)
      (H1 : aevalR e1 n1)
      (H2 : aevalR e2 n2) :
      aevalR (AMinus e1 e2) (n1 - n2)
  | E_AMult (e1 e2 : aexp) (n1 n2 : nat)
      (H1 : aevalR e1 n1)
      (H2 : aevalR e2 n2) :
      aevalR (AMult e1 e2) (n1 * n2).

End HypothesisNames.

Notation "e '==>' n"
         := (aevalR e n)
            (at level 90, left associativity)
         : type_scope.
End aevalR_first_try.

Reserved Notation "e '==>' n" (at level 90, left associativity).
Inductive aevalR : aexp -> nat -> Prop :=
  | E_ANum (n : nat) :
      (ANum n) ==> n
  | E_APlus (e1 e2 : aexp) (n1 n2 : nat) :
      (e1 ==> n1) ->
      (e2 ==> n2) ->
      (APlus e1 e2) ==> (n1 + n2)
  | E_AMinus (e1 e2 : aexp) (n1 n2 : nat) :
      (e1 ==> n1) ->
      (e2 ==> n2) ->
      (AMinus e1 e2) ==> (n1 - n2)
  | E_AMult (e1 e2 : aexp) (n1 n2 : nat) :
      (e1 ==> n1) ->
      (e2 ==> n2) ->
      (AMult e1 e2) ==> (n1 * n2)
where "e '==>' n" := (aevalR e n) : type_scope.


(* Exercise: write bevalR in terms of inference rules.
  |- bevalR BTrue true
  |- bevalR BFalse false
   aevalR e1 a1, aevalR e2 a2 |- bevalR (BEq e1 e2) (a1 =? a2)
   aevalR e1 a1, aevalR e2 a2 |- bevalR (BNeq e1 e2) (negb (a1 =? a2))
   aevalR e1 a1, aevalR e2 a2 |- bevalR (BLe e1 e2) (a1 <=? a2)
   aevalR e1 a1, aevalR e2 a2 |- bevalR (BGt e1 e2) (negb (a1 <=? a2))
   bevalR e b |- bevalR (BNot e) (negb b)
   bevalR e1 b1, bevalR e2 b2 |- bevalR (BAnd e1 e2) (andb b1 b2)

 *)

Theorem aevalR_iff_aeval : forall a n,
  (a ==> n) <-> aeval a = n.
Proof.
  split.
  - (* -> *)
    intros H.
    induction H; simpl.
    + (* E_ANum *)
      reflexivity.
    + (* E_APlus *)
      rewrite IHaevalR1. rewrite IHaevalR2. reflexivity.
    + (* E_AMinus *)
      rewrite IHaevalR1. rewrite IHaevalR2. reflexivity.
    + (* E_AMult *)
      rewrite IHaevalR1. rewrite IHaevalR2. reflexivity.
  - (* <- *)
    generalize dependent n.
    induction a;
       simpl; intros; subst.
    + (* ANum *)
      apply E_ANum.
    + (* APlus *)
      apply E_APlus.
      * apply IHa1. reflexivity.
      * apply IHa2. reflexivity.
    + (* AMinus *)
      apply E_AMinus.
      * apply IHa1. reflexivity.
      * apply IHa2. reflexivity.
    + (* AMult *)
      apply E_AMult.
      * apply IHa1. reflexivity.
      * apply IHa2. reflexivity.
Qed.


Theorem aevalR_iff_aeval' : forall a n,
  (a ==> n) <-> aeval a = n.
Proof.
  (* WORKED IN CLASS *)
  split.
  - (* -> *)
    intros H; induction H; subst; reflexivity.
  - (* <- *)
    generalize dependent n.
    induction a; simpl; intros; subst; constructor;
       try apply IHa1; try apply IHa2; reflexivity.
Qed.


Reserved Notation "e '==>b' b" (at level 90, left associativity).
Inductive bevalR: bexp -> bool -> Prop :=
  | E_BTrue :
      bevalR BTrue true 
  | E_BFalse :
      bevalR BFalse false 
  | E_BEq (e1 e2 : aexp) (b1 b2 : nat):
      (e1 ==> b1) -> (e2 ==> b2) ->
      bevalR (BEq e1 e2) (b1 =? b2)
  | E_BNeq (e1 e2 : aexp) (b1 b2 : nat):
      (e1 ==> b1) -> (e2 ==> b2) ->
      bevalR (BNeq e1 e2) (negb (b1 =? b2))
  | E_BLe (e1 e2 : aexp) (b1 b2 : nat):
      (e1 ==> b1) -> (e2 ==> b2) ->
      bevalR (BLe e1 e2) (b1 <=? b2)
  | E_BGt (e1 e2 : aexp) (b1 b2 : nat):
      (e1 ==> b1) -> (e2 ==> b2) ->
      bevalR (BGt e1 e2) (negb (b1 <=? b2))
  | E_BNot (e : bexp) (b : bool):
      (e ==>b b) ->
      bevalR (BNot e) (negb b)
  | E_BAnd (e1 e2 : bexp) (b1 b2 : bool):
      (e1 ==>b b1) -> (e2 ==>b b2) ->
      bevalR (BAnd e1 e2) (andb b1 b2)

where "e '==>b' b" := (bevalR e b) : type_scope
.

(* I keep this original proof, and use a simplified version as 
   bevalR_iff_beval' later *)
Lemma bevalR_iff_beval : forall b bv,
  b ==>b bv <-> beval b = bv.
Proof.
  induction b.
        (* True and False, similar *)
  - intros bv. destruct bv.
    + split. 
      * intros H. reflexivity.
      * intros H. apply E_BTrue.
    + split.
      * intros contra. inversion contra.
      * intros contra. discriminate contra.
  - intros bv. destruct bv.
    + split.
      * intros contra. inversion contra.
      * intros contra. discriminate contra.
    + split. 
      * intros H. reflexivity.
      * intros H. apply E_BFalse.
        (* Eq, Neq, Le, and Gq, similar *)
  - intros bv. destruct bv;
    split;
      try ( intros H; simpl;
        inversion H;
        apply aevalR_iff_aeval in H3;
        apply aevalR_iff_aeval in H4;
        rewrite -> H3; rewrite -> H4; reflexivity);
      try ( intros H; 
        inversion H;
        apply E_BEq;
        apply aevalR_iff_aeval; reflexivity).
  - intros bv. destruct bv;
    split;
      try ( intros H; simpl;
        inversion H;
        apply aevalR_iff_aeval in H3;
        apply aevalR_iff_aeval in H4;
        rewrite -> H3; rewrite -> H4; reflexivity);
      try ( intros H; 
        inversion H;
        apply E_BNeq;
        apply aevalR_iff_aeval; reflexivity).
  - intros bv. destruct bv;
    split;
      try ( intros H; simpl;
        inversion H;
        apply aevalR_iff_aeval in H3;
        apply aevalR_iff_aeval in H4;
        rewrite -> H3; rewrite -> H4; reflexivity);
      try ( intros H; 
        inversion H;
        apply E_BLe;
        apply aevalR_iff_aeval; reflexivity).
  - intros bv. destruct bv;
    split;
      try ( intros H; simpl;
        inversion H;
        apply aevalR_iff_aeval in H3;
        apply aevalR_iff_aeval in H4;
        rewrite -> H3; rewrite -> H4; reflexivity);
      try ( intros H; 
        inversion H;
        apply E_BGt;
        apply aevalR_iff_aeval; reflexivity).
        (* These two are quite special *)
  - intros bv. split.
    + intros H. simpl.
      inversion H.
      apply IHb in H1.
      rewrite -> H1. reflexivity.
    + intros H. simpl in H. 
      assert (beval b = negb bv) as H1.
      { rewrite <- H. rewrite -> negb_involutive. reflexivity. }
      apply IHb in H1.
      rewrite <- negb_involutive.
      apply E_BNot.
      exact H1.
  - intros bv. split.
    + intros H.
      inversion H.
      simpl.
      apply IHb1 in H2. apply IHb2 in H4.
      rewrite -> H2. rewrite -> H4.
      reflexivity.
    + intros H.
      simpl in H.
      destruct (beval b1) eqn:Eq1, (beval b2) eqn:Eq2;
        rewrite <- Eq1 in IHb1; rewrite <- Eq2 in IHb2;
        apply IHb1 in Eq1; apply IHb2 in Eq2;
        rewrite <- H;
        apply E_BAnd;
        try (exact Eq1); try (exact Eq2).
Qed.

(* simplified version. *)
Lemma bevalR_iff_beval' : forall b bv,
  b ==>b bv <-> beval b = bv.
Proof.
  induction b;
  intros bv; split;
  intros H;
  (* Eq, Neq, Le, and Gq, similar *)
  try (
    simpl;
    inversion H;
    try (apply aevalR_iff_aeval in H1);
    try (apply aevalR_iff_aeval in H2);
    try (apply aevalR_iff_aeval in H3);
    try (apply aevalR_iff_aeval in H4);
    try (rewrite -> H1; rewrite -> H3); 
    try (rewrite -> H2; rewrite -> H4); 
    reflexivity);
  try ( 
    inversion H;
    try (apply E_BEq);
    try (apply E_BNeq);
    try (apply E_BLe);
    try (apply E_BGt);
    apply aevalR_iff_aeval; reflexivity).
  (* True and False, similar *)
  (* One annoying thing is that I can't 
     use destruct in try, because it affects the global context. *)
   - destruct bv.
     + apply E_BTrue.
     + discriminate H.
   - destruct bv.
     + discriminate H.
     + apply E_BFalse.
  (* Not and And. These two are quite special *)
  - simpl.
    inversion H.
    apply IHb in H1.
    rewrite -> H1. reflexivity.
  - simpl in H. 
    assert (beval b = negb bv) as H1.
    { rewrite <- H. rewrite -> negb_involutive. reflexivity. }
    apply IHb in H1.
    rewrite <- negb_involutive.
    apply E_BNot.
    exact H1.
  - inversion H.
    simpl.
    apply IHb1 in H2. apply IHb2 in H4.
    rewrite -> H2. rewrite -> H4.
    reflexivity.
  - simpl in H.
    destruct (beval b1) eqn:Eq1, (beval b2) eqn:Eq2;
      rewrite <- Eq1 in IHb1; rewrite <- Eq2 in IHb2;
      apply IHb1 in Eq1; apply IHb2 in Eq2;
      rewrite <- H;
      apply E_BAnd;
      try (exact Eq1); try (exact Eq2).
Qed.
End AExp.
