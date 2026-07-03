From Tableaux Require Import Prelude.All.
From Tableaux Require Export Skolemization.

Definition Skolemization := Skolemization_ string string string.

Definition OuterSkolemization : Skolemization := @OuterSkolemization string string string _ _ _ _.
Definition InnerSkolemization : Skolemization := @InnerSkolemization string string string _ _ _ _.
