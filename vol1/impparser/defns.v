(* This chapter has no exercises.
I give myself my own exercises:
	 1. understand what's going on inside the non-trivial constructs and comment
	 them out.
	 2. Figure out each type that is not explicitly given, and add them myself as
	 type hints.
 *)

Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Strings.String.
From Coq Require Import Strings.Ascii.
From Coq Require Import Arith.
From Coq Require Import Init.Nat.
From Coq Require Import EqNat.
From Coq Require Import List. Import ListNotations.

(* These are trivial, just comparing ascii values *)
Definition isWhite (c : ascii) : bool :=
  let n := nat_of_ascii c in
  orb (orb (n =? 32) (* space *)
           (n =? 9)) (* tab *)
      (orb (n =? 10) (* linefeed *)
           (n =? 13)). (* Carriage return. *)
Notation "x '<=?' y" := (x <=? y)
  (at level 70, no associativity) : nat_scope.
Definition isLowerAlpha (c : ascii) : bool :=
  let n := nat_of_ascii c in
    andb (97 <=? n) (n <=? 122).
Definition isAlpha (c : ascii) : bool :=
  let n := nat_of_ascii c in
    orb (andb (65 <=? n) (n <=? 90))
        (andb (97 <=? n) (n <=? 122)).
Definition isDigit (c : ascii) : bool :=
  let n := nat_of_ascii c in
     andb (48 <=? n) (n <=? 57).
Inductive chartype := white | alpha | digit | other.
Definition classifyChar (c : ascii) : chartype :=
  if isWhite c then
    white
  else if isAlpha c then
    alpha
  else if isDigit c then
    digit
  else
    other.

Fixpoint list_of_string (s : string) : list ascii :=
  match s with
  | EmptyString => []
  | String c s => c :: (list_of_string s)
  end.
Definition string_of_list (xs : list ascii) : string :=
  fold_right String EmptyString xs.
Definition token := string.

From LF.maps Require Import maps.

(*
  A token is a consecutive subsequence of a string that has the
  same chartype (excluding whitespace and '(' ')' ).
  whitespaces are ignored while each of '(' and ')' is a token on its own.
  cls is the type of the current token, initially set to whitespace.
  acc is the accumulator building the current token, cleared and attached 
  to the result as tk whenever cls changes or whenever '(' or ')' is 
  encountered.

	@returns a list of tokens.
*)
Fixpoint tokenize_helper (cls : chartype) (acc xs : list ascii)
                       : list (list ascii) :=
  let tk := match acc with [] => [] | _::_ => [rev acc] end in
  match xs with
  | [] => tk
  | (x::xs') =>
    match cls, classifyChar x, x with
    | _, _, "(" =>
      tk ++ ["("]::(tokenize_helper other [] xs')
    | _, _, ")" =>
      tk ++ [")"]::(tokenize_helper other [] xs')
    | _, white, _ =>
      tk ++ (tokenize_helper white [] xs')
    | alpha,alpha,x =>
      tokenize_helper alpha (x::acc) xs'
    | digit,digit,x =>
      tokenize_helper digit (x::acc) xs'
    | other,other,x =>
      tokenize_helper other (x::acc) xs'
    | _,tp,x =>
      tk ++ (tokenize_helper tp [x] xs')
    end
  end %char.
Definition tokenize (s : string) : list string :=
  map string_of_list (tokenize_helper white [] (list_of_string s)).
Example tokenize_ex1 :
    tokenize "abc12=3 223*(3+(a+c))" %string
  = ["abc"; "12"; "="; "3"; "223";
       "*"; "("; "3"; "+"; "(";
       "a"; "+"; "c"; ")"; ")"]%string.
Proof. reflexivity. Qed.

Inductive optionE (X:Type) : Type :=
  | SomeE (x : X)
  | NoneE (s : string).
Arguments SomeE {X}.
Arguments NoneE {X}.


(* 
	This is confusing at first glance. What does it do?
	Turns out that it is used to treat optionE as much as we can like a normal
	 variable. p is the variable inside e1, and will be used as is in e2.
	For example,
	' y <-
		' x <- e1 ;; optionE (x+1)
	;; optionE (y+1)
	is to have e1's variable +1 +1.
*)
Notation "' p <- e1 ;; e2"
   := (match e1 with
       | SomeE p => e2
       | NoneE err => NoneE err
       end)
   (right associativity, p pattern, at level 60, e1 at next level).

Notation "'TRY' e1 'OR' e2"
   := (
    let result := e1 in
    match result with
       | SomeE _ => result
       | NoneE _ => e2
       end)
   (right associativity,
    at level 60, e1 at next level, e2 at next level).

Open Scope string_scope.

(* A parse seems to me is a function that parses the head token in a list
	 into type T.
 *)
Definition parser (T : Type) :=
  list token -> optionE (T * list token).

(* Seems to me to be a parsing helper that requires the parsing to be done
 * within steps and repeatedly invokes parser until
	 1. parsing terminates with NoneE, either because of a parsing error or
	 because xs becomes empty.
	 2. steps have been exhausted.

	 Its return type is unspecified, and it should be
	 optionE ( (list T) * (list token) ), where
	 list T is the parsed types and list token is the remaining ones.

	There are a few issues here:
	1. when steps is reached, all progress is lost as NoneE is returned.
	I would have to return the current progress so far.
	2. the second match clause _, NoneE _ seems to intend to capture parsing end:
	when xs = [], a parser should return NoneE. However, if the parsing fails on
	a xs != [], then the parser might return NoneE as well, and there's no way to
	tell.
 *)
Fixpoint many_helper {T} 
	(p : parser T) 
	(acc : list T)
	(steps : nat)
	(xs : list token) 
	: optionE ( (list T) * (list token) )
	:=
  match steps, p xs with
  | 0, _ =>
      NoneE "Too many recursive calls"
  | _, NoneE _ =>
      SomeE ((rev acc), xs)
  | S steps', SomeE (t, xs') =>
      many_helper p (t :: acc) steps' xs'
  end.

(* 
	This thus defines a parser that, instead of 
	parsing only the head of a list, parses ... at most steps-1 elements.	
	This is because at step NoneE is returned, as mentioned earlier.

	This makes the procedure either
	1. parses the input entirely, where len(input) < steps
	2. or fail entirely with NoneE "Too many recursive calls"
	3. or on rare cases, abort because a parsing error has occurred, which we
	 don't know about unless we check the len(output) < len(input).

	contrary to the natural idea that many parses the first steps of the tokens.
	That is not true.
*)
Definition many {T} (p : parser T) (steps : nat) : parser (list T) :=
  many_helper p [] steps.

(* First expects the first token is t.
If so, then apply p to the rest.
	 Otherwise, return NoneE *)
Definition firstExpect {T} (t : token) (p : parser T)
                     : parser T :=
  fun xs => match xs with
            | x::xs' =>
              if string_dec x t
              then p xs'
              else NoneE ("expected '" ++ t ++ "'.")
            | [] =>
              NoneE ("expected '" ++ t ++ "'.")
            end.

Definition expect (t : token) : parser unit :=
  firstExpect t (fun xs => SomeE (tt, xs)).


(* An identifier can only be lower alpha *)
Definition parseIdentifier (xs : list token)
                         : optionE (string * list token) :=
match xs with
| [] => NoneE "Expected identifier"
| x::xs' =>
    if forallb isLowerAlpha (list_of_string x) then
      SomeE (x, xs')
    else
      NoneE ("Illegal identifier:'" ++ x ++ "'")
end.

(* the digit parsing function is a common way to parse an integer *)
Definition parseNumber (xs : list token)
                     : optionE (nat * list token) :=
match xs with
| [] => NoneE "Expected number"
| x::xs' =>
    if forallb isDigit (list_of_string x) then
      SomeE (fold_left
               (fun n d =>
                  10 * n + (nat_of_ascii d -
                            nat_of_ascii "0"%char))
               (list_of_string x)
               0,
             xs')
    else
      NoneE "Expected number"
end.

From LF.imp Require Import defns.

(* either an identifier, a canonical number,
	 or a non-carnonical expression enclosed in ( ),
	 in which case that expression will be evaluated and its value will act as
	 the parsed result *)
Fixpoint parsePrimaryExp (steps:nat)
                         (xs : list token)
                       : optionE (aexp * list token) :=
  match steps with
  | 0 => NoneE "Too many recursive calls"
  | S steps' =>
      TRY ' (i, rest) <- parseIdentifier xs ;;
          SomeE (AId i, rest)
      OR
      TRY ' (n, rest) <- parseNumber xs ;;
          SomeE (ANum n, rest)
      OR
      ' (e, rest) <- firstExpect "(" (parseSumExp steps') xs ;;
      ' (u, rest') <- expect ")" rest ;;
      SomeE (e,rest')
  end

(* First checks if the first few tokens form a primary exp.
	If so, then parse its value as e.
	2. Then, see if the next token is '*'. If not, fail.
	3. If so, then parse the rest as primary exp, stored in es. 
	2 and 3 are repeated for many times until the expression is exhausted.
	All the result primary exps are stored in list es, and fold_left is done on
	 AMult es e. The order is correct, e.g., fold_left AMult [b, c] a = 
	 AMult (AMult a b) c, which is the result of parsing a*b*c
	 (left-associativity).
*)
with parseProductExp (steps:nat)
                     (xs : list token) :=
  match steps with
  | 0 => NoneE "Too many recursive calls"
  | S steps' =>
    ' (e, rest) <- parsePrimaryExp steps' xs ;;
    ' (es, rest') <- many (firstExpect "*" (parsePrimaryExp steps'))
                          steps' rest ;;
    SomeE (fold_left AMult es e, rest')
  end
(* This has the same idea of parseProductExp, but 
	 has to handle both + and - and thus has to also include a boolean to
	 indicate that. *)
with parseSumExp (steps:nat) (xs : list token) :=
  match steps with
  | 0 => NoneE "Too many recursive calls"
  | S steps' =>
    ' (e, rest) <- parseProductExp steps' xs ;;
    ' (es, rest') <-
        many (fun xs =>
                TRY ' (e,rest') <-
                    firstExpect "+"
                                (parseProductExp steps') xs ;;
                    SomeE ( (true, e), rest')
                OR
                ' (e, rest') <-
                    firstExpect "-"
                                (parseProductExp steps') xs ;;
                SomeE ( (false, e), rest'))
        steps' rest ;;
      SomeE (fold_left (fun e0 term =>
                          match term with
                          | (true, e) => APlus e0 e
                          | (false, e) => AMinus e0 e
                          end)
                       es e,
             rest')
  end.
Definition parseAExp := parseSumExp.
(* we just need to handle a lot of cases here.
The basic idea is still the same as in primary exp:
if in ( ), then parse the expr inside as the most general form.
Otherwise, proceed normally.
 *)
Fixpoint parseAtomicExp (steps:nat)
                        (xs : list token) :=
match steps with
  | 0 => NoneE "Too many recursive calls"
  | S steps' =>
     TRY ' (u,rest) <- expect "true" xs ;;
         SomeE (BTrue,rest)
     OR
     TRY ' (u,rest) <- expect "false" xs ;;
         SomeE (BFalse,rest)
     OR
     TRY ' (e,rest) <- firstExpect "~"
                                   (parseAtomicExp steps')
                                   xs ;;
         SomeE (BNot e, rest)
     OR
     TRY ' (e,rest) <- firstExpect "("
                                   (parseConjunctionExp steps')
                                   xs ;;
         ' (u,rest') <- expect ")" rest ;;
         SomeE (e, rest')
     OR
     ' (e, rest) <- parseProductExp steps' xs ;;
     TRY ' (e', rest') <- firstExpect "="
                                  (parseAExp steps') rest ;;
         SomeE (BEq e e', rest')
     OR
     TRY ' (e', rest') <- firstExpect "<="
                                      (parseAExp steps') rest ;;
         SomeE (BLe e e', rest')
     OR
     NoneE "Expected '=' or '<=' after arithmetic expression"
end

(* Similar to parseProductExp *)
with parseConjunctionExp (steps:nat)
                         (xs : list token) :=
  match steps with
  | 0 => NoneE "Too many recursive calls"
  | S steps' =>
    ' (e, rest) <- parseAtomicExp steps' xs ;;
    ' (es, rest') <- many (firstExpect "&&"
               (parseAtomicExp steps'))
            steps' rest ;;
    SomeE (fold_left BAnd es e, rest')
  end.
Definition parseBExp := parseConjunctionExp.
Check parseConjunctionExp.
Definition testParsing {X : Type}
           (p : nat ->
                list token ->
                optionE (X * list token))
           (s : string) :=
  let t := tokenize s in
  p 100 t.
(* Based on the syntax, we will be able to expect which type of expr
	 (boolean, primary, etc.) will the next be.
	 Then, proceed accordingly *)
Fixpoint parseSimpleCommand (steps:nat)
                            (xs : list token) :=
  match steps with
  | 0 => NoneE "Too many recursive calls"
  | S steps' =>
    TRY ' (u, rest) <- expect "skip" xs ;;
        SomeE (<{skip}>, rest)
    OR
    TRY ' (e,rest) <-
            firstExpect "if"
                        (parseBExp steps') xs ;;
        ' (c,rest') <-
            firstExpect "then"
                        (parseSequencedCommand steps') rest ;;
        ' (c',rest'') <-
            firstExpect "else"
                        (parseSequencedCommand steps') rest' ;;
        ' (tt,rest''') <-
            expect "end" rest'' ;;
       SomeE(<{if e then c else c' end}>, rest''')
    OR
    TRY ' (e,rest) <-
            firstExpect "while"
                        (parseBExp steps') xs ;;
        ' (c,rest') <-
            firstExpect "do"
                        (parseSequencedCommand steps') rest ;;
        ' (u,rest'') <-
            expect "end" rest' ;;
        SomeE(<{while e do c end}>, rest'')
    OR
    TRY ' (i, rest) <- parseIdentifier xs ;;
        ' (e, rest') <- firstExpect ":=" (parseAExp steps') rest ;;
        SomeE (<{i := e}>, rest')
    OR
        NoneE "Expecting a command"
end

with parseSequencedCommand (steps:nat)
                           (xs : list token) :=
  match steps with
  | 0 => NoneE "Too many recursive calls"
  | S steps' =>
    ' (c, rest) <- parseSimpleCommand steps' xs ;;
    TRY ' (c', rest') <-
            firstExpect ";"
                        (parseSequencedCommand steps') rest ;;
        SomeE (<{c ; c'}>, rest')
    OR
    SomeE (c, rest)
  end.
Definition bignumber := 1000.
Definition parse (str : string) : optionE com :=
  let tokens := tokenize str in
  match parseSequencedCommand bignumber tokens with
  | SomeE (c, []) => SomeE c
  | SomeE (_, t::_) => NoneE ("Trailing tokens remaining: " ++ t)
  | NoneE err => NoneE err
  end.

Example eg1 : parse " if x = y + 1 + 2 - y * 6 + 3 then x := x * 1; y := 0 else skip end "
=
  SomeE <{
      if ("x" = ("y" + 1 + 2 - "y" * 6 + 3)) then
        "x" := "x" * 1;
        "y" := 0
      else
        skip
      end }>.
Proof. cbv. reflexivity. Qed.
Example eg2 : parse " skip; z:=x*y*(x*x); while x=x do if (z <= z*z) && ~(x = 2) then x := z; y := z else skip end; skip end; x:=z "
=
  SomeE <{
      skip;
      "z" := "x" * "y" * ("x" * "x");
      while ("x" = "x") do
        if ("z" <= "z" * "z") && ~("x" = 2) then
          "x" := "z";
          "y" := "z"
        else
          skip
        end;
        skip
      end;
      "x" := "z" }>.
Proof. cbv. reflexivity. Qed.
