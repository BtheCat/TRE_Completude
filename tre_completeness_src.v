Inductive form :=
  | Atome : nat -> form
  | And : form -> form -> form
  | Or : form -> form -> form.

Fixpoint sem (M : nat -> Prop) (A : form) :=
  match A with
    | Atome n => M n
    | And A1 A2 => (sem M A1) /\ (sem M A2)
    | Or A1 A2 => (sem M A1) \/ (sem M A2)
  end.

Definition ctx := list form.