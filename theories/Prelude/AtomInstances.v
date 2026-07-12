From Tableaux Require Import Prelude.Init.
From Tableaux Require Import Prelude.Classes.
From Tableaux Require Export Prelude.Atoms.
From Tableaux Require Export Prelude.SetInstances.

#[global] Instance nat_atom : isAtom nat :=
  {| eqb_atom := eq_bool_nat
  ;  set_atom := nat_set |}.

#[global] Instance string_atom : isAtom string :=
  {| eqb_atom := eq_bool_string
  ;  set_atom := string_set |}.

