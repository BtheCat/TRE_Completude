From Forcing Require Import Forcing. 
Require Import List.

Import ListNotations.

Inductive form :=
  | Atome : nat -> form
  | And : form -> form -> form
  | Implies : form -> form -> form.
  (*
  | Or : form -> form -> form.
  *)

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
  (*
  | OrI1 ctx A B : provable ctx A -> provable ctx (Or A B)
  | OrI2 ctx A B : provable ctx B -> provable ctx (Or A B)
  | OrE ctx A B : forall C, provable ctx (Or A B) -> provable (cons A ctx) C -> provable (cons B ctx) C -> provable ctx C.
  *)

Lemma trans_in :
  forall A ctx ctx', extend ctx' ctx -> In A ctx -> In A ctx'.
Proof.
  intros A ctx ctx'. intros Hextend Hin.
  induction Hextend.
  - assumption.
  - apply IHHextend in Hin. apply In_cons_no. assumption.
  - apply In_cons_no. apply IHHextend. 
Admitted.

Lemma compatibility_extend_provable :
  forall { A ctx ctx' }, extend ctx' ctx -> provable ctx A -> provable ctx' A.
Proof.
  intros A ctx ctx' Hextend Hprovable.
  induction Hprovable.
  - apply Ax. apply trans_in with (ctx:=ctx) ; assumption.
  - apply AndI. 
    * apply IHHprovable1. assumption. 
    * apply IHHprovable2. assumption. 
  - apply IHHprovable in Hextend. apply AndE1 in Hextend. assumption.
  - apply IHHprovable in Hextend. apply AndE2 in Hextend. assumption.
  - apply ImpliesI. admit. 
  - assert (HextendBis : extend ctx' ctx). assumption. apply IHHprovable1 in Hextend. apply IHHprovable2 in HextendBis.
    (*apply ImpliesE with (A:=A) ; assumption.*)
Admitted.

Fixpoint semK (K : context -> nat -> Prop) (ctx : context) (A : form) :=
  match A with
    | Atome n   => K ctx n 
    | And A1 A2 => ((semK K ctx A1) * (semK K ctx A2))%type
    | Implies A1 A2 => forall ctx', extend ctx' ctx -> (semK K ctx' A1) -> (semK K ctx' A2)
    (*| Or A1 A2  => (semK K ctx A1) \/ (semK K ctx A2)*)
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
  forall { p q r }, p EXT q -> q EXT r -> p EXT r.
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
      | Atomeᶠ _ n   => M p1 Hincl1 n
      | Andᶠ _ A1 A2 => (sem p1 Hincl1 (A1 p1 (refl_incl p1))) /\ (sem p1 Hincl1 (A2 p1 (refl_incl p1)))
      (*| Orᶠ _ A1 A2  => (sem p1 Hincl1 (A1 p1 (refl_incl p1))) \/ (sem p1 Hincl1 (A2 p1 (refl_incl p1)))*)
      | Impliesᶠ _ A1 A2 => (sem p1 Hincl1 (A1 p1 (refl_incl p1))) -> (sem p1 Hincl1 (A2 p1 (refl_incl p1)))
    end) p (refl_incl p) (A p (refl_incl p)) 
  ).
Defined.

Print natᶠ.

(*Definition valid M A := forall (M : nat -> Prop) (A : form), sem M A.*)
Definition valid A := forall (M : nat -> Prop), sem M A.
Forcing Translate valid using context extend.

Forcing Translate list using context extend.
Forcing Translate context using context extend.

Forcing Translate In using context extend.
Forcing Translate provable using context extend.

Lemma psi_nat : forall { p }, natᶠ p -> nat.
Proof.
  exact (fun p n =>
    (fix psi_nat_rec n := 
      match n with 
      | Oᶠ _    => O 
      | Sᶠ _ m  => S (psi_nat_rec (m p (refl_incl p)))
      end 
    ) n
  ).
Defined.

Lemma phi_nat : forall { p : context }, nat -> natᶠ p.
Proof.
  exact (fun p n =>
    (fix phi_nat_rec p n :=
      match n with 
      | O => Oᶠ p
      | S m => Sᶠ p (fun p0 Hp0 => (phi_nat_rec p0 m))
      end 
    ) p n 
  ).
Defined.

Lemma id_nat : forall (p : context) (n : natᶠ p), phi_nat (psi_nat n) = n.
Proof.
  refine (fun p n =>
    (fix id_nat_rec p n : phi_nat (psi_nat n) = n :=
      match n with
        | Oᶠ _ => _ 
        | Sᶠ _ m => _ 
      end) p n 
  ).
  - reflexivity.
  - simpl. f_equal. 
Admitted. 

Lemma psi_form : forall { p }, formᶠ p -> form.
Proof.
  exact (fun p A =>
    (fix psi_rec A := 
      match A with 
      | Atomeᶠ _ n    => Atome (psi_nat (n p (refl_incl p))) 
      | Andᶠ _ A1 A2  => And (psi_rec (A1 p (refl_incl p))) (psi_rec (A2 p (refl_incl p)))
      (*| Orᶠ _ A1 A2   => Or (psi_rec (A1 p (refl_incl p))) (psi_rec (A2 p (refl_incl p)))*)
      | Impliesᶠ _ A1 A2 => Implies (psi_rec (A1 p (refl_incl p))) (psi_rec (A2 p (refl_incl p)))
      end) A
  ).
Defined.

Lemma phi_form : forall { p }, form -> formᶠ p.
Proof.
  exact (fun p A => 
    (fix phi_form_rec p A :=
      match A with 
      | Atome n => Atomeᶠ p (fun p0 _ => phi_nat n)
      | And A1 A2 => Andᶠ p (fun p0 _ => phi_form_rec p0 A1) (fun p0 _ => phi_form_rec p0 A2) 
      | Implies A1 A2 => Impliesᶠ p (fun p0 _ => phi_form_rec p0 A1) (fun p0 _ => phi_form_rec p0 A2)
      end) p A 
  ).
Defined.

Axiom extensionality : forall (A : Type) (B : A -> Type), ( forall { f g : forall a : A, B a }, ( forall x : A, f x = g x ) -> f = g ).

Lemma id_form : forall { p : context } A, ( fun p' Hincl => phi_form (p:=p') (psi_form (A p (refl_incl p))) ) = A.
Proof.
  (*intros. apply extensionality. intro ctx. apply extensionality.
  refine (fun p A =>
    (fix id_rec p A : phi_form (psi_form (A _ _)) = A _ _ := 
      match A with
        | Atomeᶠ _ n => _ 
        | Andᶠ _ A1 A2 => _ 
        | Impliesᶠ _ A1 A2 => _
      end) p A 
  ).
  - simpl. f_equal. (* apply id_nat. *)*)
Admitted.

Print formᶠ.
Print listᶠ.

(* Modèle universel *)
Definition K0 ctx n := provable ctx (Atome n).

Fixpoint reify p A : semK K0 p A -> provable p A :=
  match A with 
    | Atome n   => (fun v => v)
    | And A1 A2 => (fun '(v1, v2) => AndI (reify p A1 v1) (reify p A2 v2))
    | Implies A1 A2 => (fun v => ImpliesI (reify (A1 :: p) A2 (v (A1 :: p) (extend_cons_no A1 p p (id_extend p)) (reflect (A1 :: p) A1 (Ax (In_cons_yes A1 p))))))
  end 
with reflect p A : provable p A -> semK K0 p A :=
  match A with 
    | Atome n   => (fun t => t)
    | And A1 A2 => (fun t => (reflect p A1 (AndE1 t), reflect p A2 (AndE2 t)))
    | Implies A1 A2 => (fun t => (fun p0 Hinclp0 a => reflect p0 A2 (ImpliesE (compatibility_extend_provable Hinclp0 t) (reify p0 A1 a))))
  end.

Print contextᶠ.

Lemma psi_model : forall { p : context } (M : forall p0 : context, p0 EXT p ->
  (forallI p1 EXT p0, natᶠ) -> Prop), context -> nat -> Prop.
Proof.
  exact (fun p M ctx n => M p (refl_incl p) (fun p0 _ => (phi_nat n))).
Qed.

Lemma phi_model : forall (M : context -> nat -> Prop), 
  forall { p : context }, forall p0 : context, p0 EXT p ->
    (forallI p1 EXT p0, natᶠ) -> Prop.
Proof.
  exact (fun M p (p0 : context) Hinclp0 (n : forallI p EXT p0, natᶠ)
      => M p0 (psi_nat (n p0 (refl_incl p0))) ).
Defined.

Lemma psi_sem : forall { p M A }, semᶠ p (phi_model M) A -> semK M nil (psi_form (A p (refl_incl p))).
Proof.
  compute in *. 
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

Lemma phi_provable : forall { ctx A }, provable ctx (psi_form A) -> provableᶠ nil (fun p0 Hincl => (phi_context ctx) ) ( fun p0 Hincl => phi_form (psi_form (p:=ctx) A) ).
Proof.
  intros. inversion_clear H.
  - apply Axᶠ. intros. (*induction H0.
    * simpl. Set Printing All.*) (*apply (In_cons_yesᶠ p0 (fun (p : context) (α0 : p INCL p0) =>
    A p (fun (R : context) (k : extend p R) => α R (α0 R k)))). *)
Admitted.

Forcing Definition completeness : forall A, valid A -> provable nil A using context extend from nil.
Proof.
  intros. 

  specialize H with (p := nil) (α := refl_incl nil). 
  unfold validᶠ in H.
  specialize H with (M := phi_model K0). 

  apply psi_sem, reify, phi_provable in H. simpl. unfold refl_incl in H. assumption.
Qed.
