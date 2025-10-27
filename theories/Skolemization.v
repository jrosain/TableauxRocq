(** * Skolemization: a generic class for Skolemization *)

From Tableaux Require Import Prelude.
From Tableaux Require Import Syntax.

(** In this file, we implement first-order Skolemization in the framework of Cantone
    and Nicolosi-Asmundo (in their paper _A Sound Framework for δ-Rule Variants
    in Free-Variable Semantic Tableaux_). The goal is to be able to be
    Skolemization-independent in the definition of tableaux and make it work seamlessly
    for different instances of this class.

    Link to the article:
      https://sci-hub.st/https://doi.org/10.1007/s10817-006-9045-y *)
Section SkolemizationDef.
  Context {pred func var : Atom}.

  Let set_var := set_atom var.
  Let set_func := set_atom func.

  Class Skolemization_ :=
    { is_sko :> Term_ func var -> Form_ pred func var -> set_var -> set_func -> Prop
    ; symbol :
        forall (t : Term_ func var) (F : Form_ pred func var) (S : set_var) (Sf : set_func),
          is_sko t F S Sf -> func }.
End SkolemizationDef.

Arguments Skolemization_ : clear implicits.
Arguments is_sko {_ _ _ _} _ _ _ _.
Arguments symbol {_ _ _} _ _ {_ _ _} _.

Definition Skolemization := Skolemization_ string string string.

(** ** Some classic instances *)
Section SkolemizationInstances.
  Context {pred func var : Atom} `{set_term : set (Term_ func var)}.

  Let set_var := set_atom var.
  Let set_func := set_atom func.

  Definition gen_is_sko (t : Term_ func var) (P : func -> list (Term_ func var) -> Prop) : Prop :=
    match t with
    | Bound _ | Free _ => False
    | Fun f l => P f l
    end.

  Definition gen_symbol (t : Term_ func var) {P : func -> list (Term_ func var) -> Prop}
    (hsko : gen_is_sko t P) : func.
    refine
      (match t as t0 return t = t0 -> func with
       | Bound _ | Free _ => fun e => False_rect func _
       | Fun f _ => fun _ => f
       end eq_refl).
    all: now rewrite e in hsko.
  Defined.

  Instance OuterSkolemization : Skolemization_ pred func var :=
    {| is_sko :=
        fun t _ S Sf =>
          gen_is_sko t (fun f l => (forall (x : var), mem (Free x) (from_list l) <-> mem x S) /\
                                  isFresh f Sf)

    ;  symbol := fun t _ _ _ hsko => gen_symbol t hsko |}.

  Instance InnerSkolemization : Skolemization_ pred func var :=
    {| is_sko :=
        fun t F _ Sf =>
          gen_is_sko t (fun f l => (forall (x : var), mem (Free x) (from_list l) <-> mem x (fv F)) /\
                                  isFresh f Sf)

    ;  symbol := fun t _ _ _ hsko => gen_symbol t hsko |}.
End SkolemizationInstances.
