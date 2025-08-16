From Coq Require Extraction.
Extraction Language OCaml.

From Coq Require Import Arith.
From Coq Require Import Init.Nat.
From Coq Require Import EqNat.
From LF.impcevalfun Require Import defns.

Extraction "imp1.ml" ceval_step.

Extract Inductive bool => "bool" [ "true" "false" ]. 

Extract Inductive nat => "int"
  [ "0" "(fun x -> x + 1)" ]
  "(fun zero succ n -> if n=0 then zero () else succ (n-1))".

(* see coq doc 
https://rocq-prover.org/doc/V9.0.0/refman/language/core/definitions.html#term-constant
	 for what a constant is *)
Extract Constant plus => "( + )".
Extract Constant mult => "( * )".
Extract Constant eqb => "( = )".

Extraction "imp2.ml" ceval_step.

Require Import ExtrOcamlBasic.
Require Import ExtrOcamlString.

Extract Inductive sumbool => "bool" ["true" "false"].

From LF.imp Require Import defns.
From LF.impparser Require Import defns.
From LF.maps Require Import defn.

Extraction "imp.ml" empty_st ceval_step parse.


