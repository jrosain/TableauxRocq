(** * Prelude.Atoms: the types that are suitable to make free variables *)

From Tableaux Require Import Prelude.Init.
From Tableaux Require Import Prelude.Classes.
From Tableaux Require Import Prelude.Sets.

(** ** The typeclass of atoms *)

Class Atom :=
  { atom :> Type
  ; eqb_atom : EqBool atom
  ; set_atom : set atom
  ; isFresh : atom -> set_atom -> bool }.
Arguments set_atom : clear implicits.

(** ** Some usual instantiations, hidden under an importable module. *)

Module AtomComputationalInstances.
  Export SetComputationalInstances.

  #[global] Canonical Structure nat_atom : Atom :=
    {| atom := nat
    ;  eqb_atom := eq_bool_nat
    ;  set_atom := SetOfNat
    ;  isFresh := fun (x : nat) (S : SetOfNat) => negb (mem x S) |}.

  #[global] Canonical Structure string_atom : Atom :=
    {| atom := string
    ;  eqb_atom := eq_bool_string
    ;  set_atom := SetOfString
    ;  isFresh := fun (x : string) (S : SetOfString) => negb (mem x S) |}.
End AtomComputationalInstances.
