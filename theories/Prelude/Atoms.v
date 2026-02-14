(** * Prelude.Atoms: the types that are suitable to make free variables *)

From Tableaux Require Import Prelude.Init.
From Tableaux Require Import Prelude.Classes.
From Tableaux Require Import Prelude.Sets.

(** ** The typeclass of atoms *)

Record Atom :=
  { atom :> Type
  ; eqb_atom :: EqBool atom
  ; set_atom : set atom }.
Arguments set_atom : clear implicits.

(** ** Some usual instantiations, hidden under an importable module. *)

Module AtomComputationalInstances.
  Export SetComputationalInstances.

  #[global] Canonical Structure nat_atom : Atom :=
    {| atom := nat
    ;  eqb_atom := eq_bool_nat
    ;  set_atom := SetOfNat |}.

  #[global] Canonical Structure string_atom : Atom :=
    {| atom := string
    ;  eqb_atom := eq_bool_string
    ;  set_atom := SetOfString |}.
End AtomComputationalInstances.
