From Forcing Require Import Forcing. 
Require Import List.

Import ListNotations.

Inductive form :=
  | Atome : nat -> form
  | And : form -> form -> form.
  (*
  | Or : form -> form -> form.
  *)

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

Definition extend (ctx ctx' : context) := included ctx' ctx.

Inductive In (A : form) : context -> Prop :=
  | In_cons_yes : forall ctx, In A (cons A ctx)
  | In_cons_no : forall ctx, In A ctx -> forall B, In A (cons B ctx).

Inductive provable : context -> form -> Prop :=
  | Ax { ctx A } : In A ctx -> provable ctx A
  | AndI { ctx A B } : provable ctx A -> provable ctx B -> provable ctx (And A B)
  | AndE1 { ctx A B } : provable ctx (And A B) -> provable ctx A
  | AndE2 { ctx A B } : provable ctx (And A B) -> provable ctx B.
  (*
  | OrI1 ctx A B : provable ctx A -> provable ctx (Or A B)
  | OrI2 ctx A B : provable ctx B -> provable ctx (Or A B)
  | OrE ctx A B : forall C, provable ctx (Or A B) -> provable (cons A ctx) C -> provable (cons B ctx) C -> provable ctx C.
  *)

Fixpoint semK (K : context -> nat -> Prop) (ctx : context) (A : form) :=
  match A with
    | Atome n   => K ctx n 
    | And A1 A2 => ((semK K ctx A1) * (semK K ctx A2))%type
    (*| Or A1 A2  => (semK K ctx A1) \/ (semK K ctx A2)*)
  end.

(*Definition valid M A := forall (M : nat -> Prop) (A : form), sem M A.*)

Notation "p 'INCL' q" := (forall R, extend p R -> extend q R) (at level 70, q at next level).
Notation "'forallI' q 'INCL' p , P" := (forall q, q INCL p -> P q) (at level 200, q at level 69, p at level 69).

Lemma refl_incl :
  forall p, p INCL p.
Proof.
  auto.
Defined.

Lemma trans_incl :
  forall {p q r}, p INCL q -> q INCL r -> p INCL r.
Proof.
  auto.
Defined.

Forcing Translate nat using context extend.
Forcing Translate form using context extend.

Forcing Definition sem : forall (M : nat -> Prop) (A : form), Prop using context extend.
Proof.
  exact (fun p M A p0 Hincl => (* Hincl : preuve de p0 INCL p *)
    (fix sem p1 Hincl1 A := (* Hincl1 : preuve de p1 INCL p *)
      match A with
      | Atomeᶠ _ n   => M p1 Hincl1 n p1 (refl_incl p1)
      | Andᶠ _ A1 A2 => (sem p1 Hincl1 (A1 p1 (refl_incl p1))) /\ (sem p1 Hincl1 (A2 p1 (refl_incl p1)))
      (*| Orᶠ _ A1 A2  => (sem p1 Hincl1 (A1 p1 (refl_incl p1))) \/ (sem p1 Hincl1 (A2 p1 (refl_incl p1)))*)
    end) p (refl_incl p) (A p (refl_incl p)) 
  ).
Defined.

Print natᶠ.

Definition valid A := forall (M : nat -> Prop), sem M A.
Forcing Translate valid using context extend.

Forcing Translate list using context extend.
Forcing Translate context using context extend.

Forcing Translate In using context extend.
Forcing Translate provable using context extend.

Lemma psi_nat : forall { p }, (forallI p0 INCL p, natᶠ) -> nat.
Proof.
  exact (fun p n =>
    (fix psi_nat_rec n := 
      match n with 
      | Oᶠ _    => O 
      | Sᶠ _ m  => S (psi_nat_rec (m p (refl_incl p)))
      end 
    ) (n p (refl_incl p)) 
  ).
Qed.

Lemma phi_nat : forall (p : context), nat -> natᶠ p.
Proof.
  exact (fun p n =>
    (fix phi_nat_rec p n :=
      match n with 
      | O => Oᶠ p
      | S m => Sᶠ p (fun p0 Hp0 => (phi_nat_rec p0 m))
      end 
    ) p n 
  ).
Qed.

Lemma psi_form : forall { p }, formᶠ p -> form.
Proof.
  exact (fun p A =>
    (fix psi_rec A := 
      match A with 
      | Atomeᶠ _ n    => Atome (psi_nat n) 
      | Andᶠ _ A1 A2  => And (psi_rec (A1 p (refl_incl p))) (psi_rec (A2 p (refl_incl p)))
      (*| Orᶠ _ A1 A2   => Or (psi_rec (A1 p (refl_incl p))) (psi_rec (A2 p (refl_incl p)))*)
      end) A
  ).
Defined.

Lemma phi_form : forall { p }, form -> formᶠ p.
Proof.
  exact (fun p A => 
    (fix phi_form_rec p A :=
      match A with 
      | Atome n => Atomeᶠ p (fun p0 _ => phi_nat p0 n)
      | And A1 A2 => Andᶠ p (fun p0 _ => phi_form_rec p0 A1) (fun p0 _ => phi_form_rec p0 A2) 
      end) p A 
  ).
Defined.

Lemma id_form : forall { p : context } (A : formᶠ p), phi_form (psi_form A) = A.
Proof.
  refine (fun p A =>
    (fix id_rec p A : phi_form (psi_form A) = A := 
      match A with
        | Atomeᶠ _ n => _ 
        | Andᶠ _ A1 A2 => _ 
      end) p A 
  ).
  simpl.
Admitted.

Print formᶠ.

(*Lemma psi_provable : forall p M A, provableᶠ p M A -> provable (M) (psi_form (A p (refl_incl p))).
Proof.
  exact (fun p M A prov =>
    (fix psi_prov_rec prov :=
      match prov with
      | Axᶠ
    )
  ).
Admitted.*)

(* Modèle universel *)
Definition K0 ctx n := provable ctx (Atome n).

Fixpoint reify p A : semK K0 p A -> provable p A :=
  match A with 
    | Atome n   => (fun v => v)
    | And A1 A2 => (fun '(v1, v2) => AndI (reify p A1 v1) (reify p A2 v2))
  end 
with reflect p A : provable p A -> semK K0 p A :=
  match A with 
    | Atome n   => (fun t => t)
    | And A1 A2 => (fun t => (reflect p A1 (AndE1 t), reflect p A2 (AndE2 t)))
  end.

Print contextᶠ.

Lemma psi_model : forall { p : context } (M : forall p0 : context, p0 INCL p ->
  (forallI p1 INCL p0, natᶠ) -> forall p1 : context, p1 INCL p0 -> Prop), context -> nat -> Prop.
Proof.
  exact (fun p M ctx n => M p (refl_incl p) (fun p0 _ => (phi_nat p0 n)) p (refl_incl p)).
Qed.

Lemma phi_model : forall (M : context -> nat -> Prop), 
  forall { p : context }, forall p0 : context, p0 INCL p ->
    (forallI p1 INCL p0, natᶠ) -> forall p1 : context, p1 INCL p0 -> Prop.
Proof.
  exact (fun M p (p0 : context) Hinclp0 (n : forallI p INCL p0, natᶠ) p1 Hinclp1 
      => M p1 (psi_nat n) ).
Defined.

(*Axiom psi_sem : forall { p M A p0 Hinclp0 }, semᶠ p (phi_model M) (fun p1 _ => phi_form A) p0 Hinclp0 -> semK M p A.*)
Lemma psi_sem : forall { p M A p0 Hinclp0 }, semᶠ p (phi_model M) A p0 Hinclp0 -> semK M nil (psi_form A).
Proof.
  compute in *. 
Admitted.

Lemma phi_context : forall { p }, context -> contextᶠ p p (refl_incl p).
Proof.
  exact (fun p ctx =>
    (fix phi_ctx_rec p ctx : contextᶠ p p (refl_incl p) :=
      match ctx with 
      | [] => nilᶠ p _
      | A :: ctx' => consᶠ p _ (fun p1 _ => phi_form A) (fun p1 _ => phi_ctx_rec p1 ctx')
      end 
    ) p ctx
  ).
Defined.

Lemma phi_provable : forall { ctx A }, provable ctx (psi_form A) -> provableᶠ nil (fun p0 Hincl => (phi_context ctx) ) A.
Proof.
  intros. inversion_clear H.
  - apply Axᶠ. intros. induction H0.
    * simpl. Set Printing All. (*apply (In_cons_yesᶠ p0 (fun (p : context) (α0 : p INCL p0) =>
    A p (fun (R : context) (k : extend p R) => α R (α0 R k)))). *)
Admitted.


(*Forcing Translate and using context included.*)
Forcing Definition completeness : forall A, valid A -> provable nil A using context extend from nil.
Proof.
  intros. 

  specialize H with (p := nil) (α := refl_incl nil). 
  unfold validᶠ in H.
  specialize H with (M := phi_model K0). 

  apply psi_sem, reify, phi_provable in H . assumption.
Qed.
