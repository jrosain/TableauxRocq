(** * Prelude.Utils: some utility functions / lemmas *)

Definition option_get {A : Type} (def : A) (x : option A) : A :=
  match x with
  | None => def
  | Some x => x
  end.

Definition bind {A B : Type} (x : option A) (f : A -> option B) : option B :=
  match x with
  | Some x => f x
  | None => None
  end.
