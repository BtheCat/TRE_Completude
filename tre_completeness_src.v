From Forcing Require Import Forcing. 
Require Import List.

Import ListNotations.

Inductive form :=
  | Atome : nat -> form
  | And : form -> form -> form
  | Or : form -> form -> form.

Fixpoint sem (M : nat -> Prop) (A : form) :=
  match A with
    | Atome n   => M n
    | And A1 A2 => (sem M A1) /\ (sem M A2)
    | Or A1 A2  => (sem M A1) \/ (sem M A2)
  end.

Definition context := list form.

Inductive included : context -> context -> Prop :=
  | included_nil : included nil nil
  | included_cons_no : forall A ctx ctx', included ctx ctx' -> included ctx (cons A ctx')
  | included_cons_yes : forall A ctx ctx', included ctx ctx' -> included (cons A ctx) (cons A ctx').

Fixpoint In (A : form) (ctx : context) : Prop :=
  match ctx with
  | [] => False
  | B :: ctx' => B = A \/ In A ctx' 
  end.

Inductive provable : context -> form -> Prop :=
  | Ax ctx A : In A ctx -> provable ctx A
  | AndI ctx A B : provable ctx A -> provable ctx B -> provable ctx (And A B)
  | AndE1 ctx A B : provable ctx (And A B) -> provable ctx A
  | AndE2 ctx A B : provable ctx (And A B) -> provable ctx B
  | OrI1 ctx A B : provable ctx A -> provable ctx (Or A B)
  | OrI2 ctx A B : provable ctx B -> provable ctx (Or A B)
  (*
  | OrE ctx A B : provable ctx (Or A B) -> provable 
  *).

(*Definition valid M A := forall (M : nat -> Prop) (A : form), sem M A.*)
Definition valid A := forall (M : nat -> Prop), sem M A.

Notation "p 'INCL' q" := (forall R, included p R -> included q R) (at level 70).
Notation "'forallI' q 'INCL' p , P" := (forall q, q INCL p -> P q) (at level 200).

Forcing Translate nat using context included.
Forcing Translate form using context included.
Forcing Definition sem : forall (M : nat -> Prop) (A : form), Prop using context included.
Forcing Translate valid using context included.
Forcing Definition completeness : forall A, valid A -> provable nil A using context included.