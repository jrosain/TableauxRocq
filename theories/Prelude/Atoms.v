(** * Prelude.Atoms: the types that are suitable to make free variables *)

From Tableaux Require Import Prelude.Init.
From Tableaux Require Import Prelude.Classes.
From Tableaux Require Import Prelude.Sets.

(** ** The typeclass of atoms *)

Class isAtom (A : Type) :=
  { eqb_atom :: EqBool A
  ; set_atom :: set A }.
Arguments eqb_atom {_ _}.
Arguments set_atom _ {_}.

(** Some instanciations can be found in [AtomInstances.v]. *)
