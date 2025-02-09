From LF Require Import basics.booleans.

Theorem identity_fn_applied_twice : 
  forall (f : bool -> bool),
  (forall (x : bool), f x = x) -> forall (b : bool), f (f b) = b.
Proof.
  intros f.
  intros H.
  intros b.
  (* apply f x = x twice *)
  rewrite <- H.
  rewrite <- H.
  reflexivity.
Qed.

Theorem negation_fn_applied_twice : 
  forall (f : bool -> bool),
  (forall (x : bool), f x = negb x) -> forall (b : bool), f (f b) = b.
Proof.
  intros f.
  intros H.
  intros b.
  (* 
     apply f x = x twice, but now we need to prove that negb negb b = b
  *)
  rewrite -> H. 
  rewrite -> H.
  destruct b.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

Theorem andb_eq_orb :
  forall (b c : bool),
  (andb b c = orb b c) ->
  b = c.
Proof.
  intros b c.
  intros H.
  destruct b.
  (* simpl in H will simplify H instead of the goal. *)
  - (* orb true c = true, andb true c = c *)
    simpl in H. rewrite -> H. reflexivity.
  - (* orb false c = c, andb false c = false *)
    simpl in H. rewrite <- H. reflexivity.
Qed.
