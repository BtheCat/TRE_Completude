Inductive form :=
  | Atome : nat -> form
  | And : form -> form -> form
  | Or : form -> form -> form.