From LF.indprop Require Import defns.

Module Props.

Module And.

(* Here I use a different but equivalent way to define conj,
   to reinforce my learning *)
Inductive and (P Q : Prop) : Prop :=
  | conj : forall (_ : P) (_ : Q), and P Q.
Arguments conj [P] [Q].
Notation "P /\ Q" := (and P Q) : type_scope.

Theorem proj1' : forall P Q,
  P /\ Q -> P.
Proof.
  intros P Q HPQ. 
  destruct HPQ as [HP HQ]. apply HP.
  Show Proof.
Qed.

Lemma and_comm : forall P Q : Prop, P /\ Q <-> Q /\ P.
Proof.
  intros P Q. split.
  - intros [HP HQ]. split.
    + apply HQ.
    + apply HP.
  - intros [HQ HP]. split.
    + apply HP.
    + apply HQ.
Qed.

End And.

Definition proj1'' P Q (HPQ : P /\ Q) : P :=
  match HPQ with
  | conj HP HQ => HP
  end.
Definition and_comm'_aux P Q (H : P /\ Q) : Q /\ P :=
  match H with
  | conj HP HQ => conj HQ HP
  end.
(* To understand why we can use conj to give a proof to <->,
   notice that <-> is defined as two implications connected by /\. *)
Definition and_comm' P Q : P /\ Q <-> Q /\ P :=
  conj (and_comm'_aux P Q) (and_comm'_aux Q P).

Definition conj_fact : forall P Q R, P /\ Q -> Q /\ R -> P /\ R
  :=
  (* 1. name evidences *)
  fun (P Q R : Prop) (HPQ : P /\ Q) (HQR : Q /\ R) =>
  (* 2. need a proof of P and a proof of R.
     I know I could use proj1 and define a proj2 for them,
     respectively, but I do this just to reinforce my knowledge. *)
  conj (
    (* of P *)
    match HPQ with 
    | conj HP _ => HP
    end
  ) (
    (* of R *)
    match HQR with 
    | conj _ HR => HR
    end
  ).

Module Or.

Inductive or (P Q : Prop) : Prop :=
  | or_introl : P -> or P Q
  | or_intror : Q -> or P Q.
Arguments or_introl [P] [Q].
Arguments or_intror [P] [Q].
Notation "P \/ Q" := (or P Q) : type_scope.

Theorem inj_l' : forall (P Q : Prop), P -> P \/ Q.
Proof.
  intros P Q HP. left. apply HP.
  Show Proof.
Qed.
Definition or_elim : forall (P Q R : Prop), (P \/ Q) -> (P -> R) -> (Q -> R) -> R :=
  fun P Q R HPQ HPR HQR =>
    match HPQ with
    | or_introl HP => HPR HP
    | or_intror HQ => HQR HQ
    end.
Theorem or_elim' : forall (P Q R : Prop), (P \/ Q) -> (P -> R) -> (Q -> R) -> R.
Proof.
  intros P Q R HPQ HPR HQR.
  destruct HPQ as [HP | HQ].
  - apply HPR. apply HP.
  - apply HQR. apply HQ.
Qed.

End Or.

Definition or_commut' : forall P Q, P \/ Q -> Q \/ P
  :=
  fun P Q HPQ =>
  match HPQ with
  | or_introl HP => or_intror HP 
  | or_intror HQ => or_introl HQ 
  end.

Module Ex.
Inductive ex {A : Type} (P : A -> Prop) : Prop :=
  | ex_intro : forall x : A, P x -> ex P.
Notation "'exists' x , p" :=
  (ex (fun x => p))
    (at level 200, right associativity) : type_scope.
End Ex.

Definition ex_ev_Sn : ex (fun n => ev (S n))
  :=
  (* ex_intro (P : A -> Prop) (x : A) (_ : P x) *)
  ex_intro (fun n => ev (S n)) 1 (ev_SS 0 ev_0).


Inductive True : Prop :=
  | I : True.

Definition p_implies_true : forall P, P -> True
  :=
  fun (P : Prop) (_ : P) => I.

Inductive False : Prop := .

Definition ex_falso_quodlibet:
  forall P, False -> P :=
  fun P (contra : False) =>
  match contra with end.



End Props.
