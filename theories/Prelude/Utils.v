(** * Prelude.Utils: some utility functions / lemmas *)

From Tableaux Require Import Init.

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

Fixpoint forallb2 {A : Type} (P : A -> A -> bool) (l1 l2 : list A) : bool :=
  match l1, l2 with
  | [], [] => true
  | x :: xs, y :: ys => P x y && forallb2 P xs ys
  | _, _ => false
  end.
