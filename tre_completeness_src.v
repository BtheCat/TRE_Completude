From Forcing Require Import Forcing. 
Require Import List.
Require Import Program.

Import ListNotations.

Inductive form :=
  | Atom : nat -> form
  | And : form -> form -> form
  | Implies : form -> form -> form.

Definition context := list form.

Inductive extend : context -> context -> Prop :=
  | extend_nil : extend nil nil
  | extend_cons_no : forall A ctx ctx', extend ctx ctx' -> extend (cons A ctx) ctx'
  | extend_cons_yes : forall A ctx ctx', extend ctx ctx' -> extend (cons A ctx) (cons A ctx').

Inductive In (A : form) : context -> Prop :=
  | In_cons_yes : forall ctx, In A (cons A ctx)
  | In_cons_no : forall ctx, In A ctx -> forall B, In A (cons B ctx).

Inductive provable : context -> form -> Prop :=
  | Ax { ctx A } : In A ctx -> provable ctx A
  | AndI { ctx A B } : provable ctx A -> provable ctx B -> provable ctx (And A B)
  | AndE1 { ctx A B } : provable ctx (And A B) -> provable ctx A
  | AndE2 { ctx A B } : provable ctx (And A B) -> provable ctx B
  | ImpliesI { ctx A B } : provable (cons A ctx) B -> provable ctx (Implies A B)
  | ImpliesE { ctx A B } : provable ctx (Implies A B) -> provable ctx A -> provable ctx B.

Lemma compatibility_extend_in :
  forall A ctx ctx', extend ctx' ctx -> In A ctx -> In A ctx'.
Proof.
  intros A ctx ctx'. intros Hextend Hin.
  induction Hextend. 
  - assumption.
  - apply IHHextend in Hin. apply In_cons_no. assumption.
  - dependent induction Hin.
    * apply In_cons_yes.
    * apply In_cons_no. apply IHHextend. assumption. 
Qed.

Lemma compatibility_extend_provable :
  forall { A ctx ctx' }, extend ctx' ctx -> provable ctx A -> provable ctx' A.
Proof.
  intros A ctx ctx' Hextend Hprovable.
  induction Hprovable in ctx', Hextend.
  - apply Ax. apply compatibility_extend_in with (ctx:=ctx) ; assumption.
  - apply AndI. 
    * apply IHHprovable1. assumption. 
    * apply IHHprovable2. assumption. 
  - apply IHHprovable in Hextend. apply AndE1 in Hextend. assumption.
  - apply IHHprovable in Hextend. apply AndE2 in Hextend. assumption.
  - apply ImpliesI. specialize IHHprovable with (cons A ctx'). 
    apply IHHprovable. apply extend_cons_yes. assumption.
  - assert (HextendBis : extend ctx' ctx). assumption. 
    apply IHHprovable1 in Hextend. apply IHHprovable2 in HextendBis.
    apply @ImpliesE with (A:=A) ; assumption.
Qed.

Fixpoint semK (K : context -> nat -> Prop) (ctx : context) (A : form) :=
  match A with
    | Atom n   => K ctx n 
    | And A1 A2 => ((semK K ctx A1) * (semK K ctx A2))%type
    | Implies A1 A2 => forall ctx', extend ctx' ctx -> (semK K ctx' A1) -> (semK K ctx' A2)
  end.

Notation "p 'EXT' q" := (forall R, extend p R -> extend q R) (at level 70, q at next level).
Notation "'forallI' q 'EXT' p , P" := (forall q, q EXT p -> P q) (at level 200, q at level 69, p at level 69).

Lemma refl_incl :
  forall p, p EXT p.
Proof.
  auto.
Defined.

Lemma id_extend :
  forall p, extend p p.
Proof.
  intros. induction p.
  - apply extend_nil.
  - apply extend_cons_yes. assumption.
Qed.

Lemma trans_incl :
  forall {p q r}, p EXT q -> q EXT r -> p EXT r.
Proof.
  auto.
Defined.

Forcing Translate nat using context extend.
Forcing Translate form using context extend.

Forcing Definition sem : forall (M : nat -> Prop) (A : form), Prop using context extend.
Proof.
  exact (fun p M A => 
    (fix sem p1 Hincl1 A := (* Hincl1 : preuve de p1 INCL p *)
      match A with
      | Atomᶠ _ n   => M p1 Hincl1 n
      | Andᶠ _ A1 A2 => (sem p1 Hincl1 (A1 p1 (refl_incl p1))) /\ (sem p1 Hincl1 (A2 p1 (refl_incl p1)))
      | Impliesᶠ _ A1 A2 => (sem p1 Hincl1 (A1 p1 (refl_incl p1))) -> (sem p1 Hincl1 (A2 p1 (refl_incl p1)))
    end) p (refl_incl p) (A p (refl_incl p)) 
  ).
Defined.

Definition valid A := forall (M : nat -> Prop), sem M A.
Forcing Translate valid using context extend.

Forcing Translate list using context extend.
Forcing Translate context using context extend.

Forcing Translate In using context extend.
Forcing Translate provable using context extend.

Lemma psi_nat : forall { p }, (forallI p0 EXT p, natᶠ) -> nat.
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

Lemma psi_form : forall { p }, (forallI p0 EXT p, formᶠ) -> form.
Proof.
  exact (fun p A =>
    (fix psi_rec A := 
      match A with 
      | Atomᶠ _ n    => Atom (psi_nat n) 
      | Andᶠ _ A1 A2  => And (psi_rec (A1 p (refl_incl p))) (psi_rec (A2 p (refl_incl p)))
      | Impliesᶠ _ A1 A2 => Implies (psi_rec (A1 p (refl_incl p))) (psi_rec (A2 p (refl_incl p)))
      end) (A p (refl_incl p))
  ).
Defined.

Lemma phi_form : forall { p }, form -> formᶠ p.
Proof.
  exact (fun p A => 
    (fix phi_form_rec p A :=
      match A with 
      | Atom n => Atomᶠ p (fun p0 _ => phi_nat p0 n)
      | And A1 A2 => Andᶠ p (fun p0 _ => phi_form_rec p0 A1) (fun p0 _ => phi_form_rec p0 A2) 
      | Implies A1 A2 => Impliesᶠ p (fun p0 _ => phi_form_rec p0 A1) (fun p0 _ => phi_form_rec p0 A2)
      end) p A 
  ).
Defined.

(* Modèle universel *)
Definition K0 ctx n := provable ctx (Atom n).

Fixpoint reify p A : semK K0 p A -> provable p A :=
  match A with 
    | Atom n   => (fun v => v)
    | And A1 A2 => (fun '(v1, v2) => AndI (reify p A1 v1) (reify p A2 v2))
    | Implies A1 A2 => (fun v => ImpliesI (reify (A1 :: p) A2 (v (A1 :: p) (extend_cons_no A1 p p (id_extend p)) (reflect (A1 :: p) A1 (Ax (In_cons_yes A1 p))))))
  end 
with reflect p A : provable p A -> semK K0 p A :=
  match A with 
    | Atom n   => (fun t => t)
    | And A1 A2 => (fun t => (reflect p A1 (AndE1 t), reflect p A2 (AndE2 t)))
    | Implies A1 A2 => (fun t => (fun p0 Hinclp0 a => reflect p0 A2 (ImpliesE (compatibility_extend_provable Hinclp0 t) (reify p0 A1 a))))
  end.

(*
Lemma psi_model : forall { p : context } (M : forall p0 : context, p0 EXT p ->
  (forallI p1 EXT p0, natᶠ) -> Prop), context -> nat -> Prop.
Proof.
  exact (fun p M ctx n => M p (refl_incl p) (fun p0 _ => (phi_nat p0 n))).
Qed.
*)

Lemma phi_model : forall (M : context -> nat -> Prop), 
  forall { p : context }, forall p0 : context, p0 EXT p ->
    (forallI p1 EXT p0, natᶠ) -> Prop.
Proof.
  exact (fun M p (p0 : context) Hinclp0 (n : forallI p EXT p0, natᶠ) 
      => M p0 (psi_nat n) ).
Defined.

Lemma psi_sem : forall { p M A }, semᶠ p (phi_model M) A -> semK M nil (psi_form A).
Proof.
Admitted.

Lemma phi_context : forall { p }, context -> contextᶠ p.
Proof.
  exact (fun p ctx =>
    (fix phi_ctx_rec p ctx : contextᶠ p :=
      match ctx with 
      | [] => nilᶠ p _
      | A :: ctx' => consᶠ p _ (fun p1 _ => phi_form A) (fun p1 _ => phi_ctx_rec p1 ctx')
      end 
    ) p ctx
  ).
Defined.

Lemma phi_provable : forall { ctx A }, provable ctx (psi_form A) -> provableᶠ nil (fun p0 Hincl => (phi_context ctx) ) A.
Proof.
Admitted.

Forcing Definition completeness : forall A, valid A -> provable nil A using context extend from nil.
Proof.
  intros. 

  specialize H with (p := nil) (α := refl_incl nil). 
  unfold validᶠ in H.
  specialize H with (M := phi_model K0). 

  apply psi_sem, reify, phi_provable in H . assumption.
Qed.
