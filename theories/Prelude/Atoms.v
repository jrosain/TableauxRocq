(** * Prelude.Atoms: the types that are suitable to make free variables *)

From Tableaux Require Import Prelude.Init.
From Tableaux Require Import Prelude.Classes.
From Tableaux Require Import Prelude.Sets.

(** ** The typeclass of atoms *)

Class Atom :=
  { atom :> Type
  ; eq_dec_atom : EqDec atom
  ; set_atom : set atom
  ; isFresh : atom -> set_atom -> Prop }.
Arguments set_atom : clear implicits.

(** ** Some usual instantiations, hidden under an importable module. *)

Module AtomComputationalInstances.
  Export SetComputationalInstances.

  #[global] Canonical Structure nat_atom : Atom :=
    {| atom := nat
    ;  eq_dec_atom := eq_dec_nat
    ;  set_atom := SetOfNat
    ;  isFresh := fun (x : nat) (S : SetOfNat) => ~(mem x S) |}.

  #[global] Canonical Structure string_atom : Atom :=
    {| atom := string
    ;  eq_dec_atom := eq_dec_string
    ;  set_atom := SetOfString
    ;  isFresh := fun (x : string) (S : SetOfString) => ~(mem x S) |}.
End AtomComputationalInstances.
