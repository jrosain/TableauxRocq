(** * Skolemization: a generic class for Skolemization *)

From Tableaux Require Import Prelude.
From Tableaux Require Import Syntax.

(** In this file, we implement first-order Skolemization in the framework of Cantone
    and Nicolosi-Asmundo (in their paper _A Sound Framework for δ-Rule Variants
    in Free-Variable Semantic Tableaux_). The goal is to be able to be
    Skolemization-independent in the definition of tableaux and make it work seamlessly
    for different instances of this class. *)
Section SkolemizationDef.
  Context (pred func var : Atom).

  #[local] Definition set_var := set_atom var.
  #[local] Definition set_func := set_atom func.

  Class Skolemization_ :=
    { sko :> Form_ pred func var -> set_var -> set_func -> Term_ func var
    ; symbol : Form_ pred func var -> set_var -> set_func -> func

    ; symbol_is_sko : forall F S Sf, get_symbol (sko F S Sf) = Some (symbol F S Sf) }.
End SkolemizationDef.

Arguments sko {_ _ _} _ _ _.
Arguments symbol {_ _ _} _ _ _.
Arguments symbol_is_sko {_ _ _} _ _ _.

Definition Skolemization := Skolemization_ string string nat.
