(* Require Import Forcing *)

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

(*Definition valid M A := forall (M : nat -> Prop) (A : form), sem M A.*)
Definition valid A := forall (M : nat -> Prop), sem M A.

(* Forcing Definition completeness : valid A -> provable nil A using context included *)