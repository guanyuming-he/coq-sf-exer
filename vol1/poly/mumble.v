From LF Require Import basics.numbers.

Module MumbleGrumble.

Inductive mumble : Type :=
  | a
  | b (x : mumble) (y : nat)
  | c.
Inductive grumble (X:Type) : Type :=
  | d (m : mumble)
  | e (x : X).

(** 
   Which of the following are well-typed elements of grumble X for some type X? (Add YES or NO to each line.)

    d (b a 5) NO.
    d mumble (b a 5) YES.
    d bool (b a 5) YES.
    e bool true YES.
    e mumble (b c 0) YES.
    e bool (b c 0) NO.
    c NO.
*)

(* TO verify my answers *)
Check (d mumble (b a 5)) : grumble mumble.
Check (d bool (b a 5)) : grumble bool.
Check (e bool true) : grumble bool.
Check (e mumble (b c 0)) : grumble mumble.


End MumbleGrumble.
