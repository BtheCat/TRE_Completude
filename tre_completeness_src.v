From Forcing Require Import Forcing. 
Require Import List.

Import ListNotations.

Inductive form :=
  | Atome : nat -> form
  | And : form -> form -> form
  | Or : form -> form -> form.

(*
Fixpoint sem (M : nat -> Prop) (A : form) :=
  match A with
    | Atome n   => M n
    | And A1 A2 => (sem M A1) /\ (sem M A2)
    | Or A1 A2  => (sem M A1) \/ (sem M A2)
  end.
*)

Definition context := list form.

Inductive included : context -> context -> Prop :=
  | included_nil : included nil nil
  | included_cons_no : forall A ctx ctx', included ctx ctx' -> included ctx (cons A ctx')
  | included_cons_yes : forall A ctx ctx', included ctx ctx' -> included (cons A ctx) (cons A ctx').

Inductive In (A : form) : context -> Prop :=
  | In_cons_yes : forall ctx, In A (cons A ctx)
  | In_cons_no : forall ctx, In A ctx -> forall B, In A (cons B ctx).

Inductive provable : context -> form -> Prop :=
  | Ax ctx A : In A ctx -> provable ctx A
  | AndI ctx A B : provable ctx A -> provable ctx B -> provable ctx (And A B)
  | AndE1 ctx A B : provable ctx (And A B) -> provable ctx A
  | AndE2 ctx A B : provable ctx (And A B) -> provable ctx B
  | OrI1 ctx A B : provable ctx A -> provable ctx (Or A B)
  | OrI2 ctx A B : provable ctx B -> provable ctx (Or A B)
  | OrE ctx A B : forall C, provable ctx (Or A B) -> provable (cons A ctx) C -> provable (cons B ctx) C -> provable ctx C.

(*Definition valid M A := forall (M : nat -> Prop) (A : form), sem M A.*)

Notation "p 'INCL' q" := (forall R, included p R -> included q R) (at level 70).
Notation "'forallI' q 'INCL' p , P" := (forall q, q INCL p -> P q) (at level 200).

Lemma refl_incl :
  forall p, p INCL p.
Proof.
  auto.
Qed.

Forcing Translate nat using context included.
Forcing Translate form using context included.

Forcing Definition sem : forall (M : nat -> Prop) (A : form), Prop using context included.
exact (fun p M A p0 Hincl => (* Hincl : preuve de p0 INCL p *)
    (fix sem p1 Hincl1 A := (* Hincl1 : preuve de p1 INCL p *)
      match A with
      | Atomeᶠ _ n   => M p1 Hincl1 n p1 (refl_incl p1)
      | Andᶠ _ A1 A2 => (sem p1 Hincl1 (A1 p1 (refl_incl p1))) /\ (sem p1 Hincl1 (A2 p1 (refl_incl p1)))
      | Orᶠ _ A1 A2  => (sem p1 Hincl1 (A1 p1 (refl_incl p1))) \/ (sem p1 Hincl1 (A2 p1 (refl_incl p1)))
    end) p (refl_incl p) (A p (refl_incl p)) 
  ).
Defined.

Definition valid A := forall (M : nat -> Prop), sem M A.
Forcing Translate valid using context included.

Forcing Translate list using context included.
Forcing Translate context using context included.

Forcing Translate In using context included.
Forcing Translate provable using context included.

Forcing Translate and using context included.
Forcing Definition completeness : forall A, (valid A -> provable nil A) /\ (provable nil A -> valid A) using context included.

