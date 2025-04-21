
Definition and_assoc : forall P Q R : Prop,
    P /\ (Q /\ R) -> (P /\ Q) /\ R
    :=
    fun P Q R H => 
    match H with 
    | conj p qr => 
        match qr with
        | conj q r => conj (conj p q) r 
        end
    end.

Definition or_distributes_over_and : forall P Q R : Prop,
  P \/ (Q /\ R) <-> (P \/ Q) /\ (P \/ R)
  :=
  fun P Q R =>
  conj (
    (* -> *)
    fun H => 
    match H with 
    | or_introl p => 
      conj (or_introl p) (or_introl p) 
    | or_intror qr =>
        match qr with
        | conj q r => 
          conj (or_intror q) (or_intror r)
        end
    end
  ) (
    (* <- *)
    fun H =>
    match H with 
    | conj poq por =>
        match poq with 
        | or_introl p => or_introl p 
        | or_intror q =>
            match por with 
            | or_introl p => or_introl p 
            | or_intror r => or_intror (conj q r)
            end
        end
    end
  ).


Definition double_neg : forall P : Prop,
    P -> ~~P
    :=
    fun P (p : P) (NP : P -> False) =>
    NP p.

Definition contradiction_implies_anything : forall P Q : Prop,
    (P /\ ~P) -> Q
    :=
    fun P Q pnp =>
    match pnp with 
    | conj p np => match (np p) with (* false *) end 
    end.
    
Definition de_morgan_not_or : forall P Q : Prop,
    ~(P \/ Q) -> ~P /\ ~Q
    := 
    fun P Q npoq =>
    conj 
    (fun p: P => npoq (or_introl p))
    (fun q: Q => npoq (or_intror q))
    .

Definition curry : forall P Q R : Prop,
    ((P /\ Q) -> R) -> (P -> (Q -> R))
    :=
    fun P Q R H =>
      fun p : P =>
        fun q : Q =>
          H (conj p q).

Definition uncurry : forall P Q R : Prop,
    (P -> (Q -> R)) -> ((P /\ Q) -> R)
    :=
    fun P Q R H =>
      fun pq : (P /\ Q) =>
        match pq with
        | conj p q =>
            (H p) q
        end.
