(** * Proofs: definition of free-variable tableaux proofs. *)

From Tableaux Require Import Syntax.

Section TableauxProofs.
  Context {set_nat : set nat} {pred func var : Atom} {con : Con_ pred func var}.

  Definition set_var := set_atom var.
  Definition set_func := set_atom func.

  Inductive hasTableau_
    : con -> set_var -> set_func -> Substitution var (Term_ func var) -> Prop :=

  (** Axioms *)
  | hasTableauBot :
    forall (Gamma : con) (S : set_var) (Sf : set_func) (sigma : Substitution var (Term_ func var)),
      (Bot \in Gamma) -> hasTableau_ Gamma S Sf sigma
  | hasTableauContr :
    forall (Gamma : con) (S : set_var) (Sf : set_func) (sigma : Substitution var (Term_ func var))
      (P : Form_ pred func var), (P@[sigma] \in Gamma) -> (Neg P@[sigma] \in Gamma) -> hasTableau_ Gamma S Sf sigma

  (** Alpha rules *)
  | hasTableauNegNeg :
    forall (Gamma : con) (S : set_var) (Sf : set_func) (sigma : Substitution var (Term_ func var))
      (F : Form_ pred func var), Neg (Neg F) \in Gamma -> hasTableau_ (Gamma ,, F) S Sf sigma -> hasTableau_ Gamma S Sf sigma
  | hasTableauNegOr :
    forall (Gamma : con) (S : set_var) (Sf : set_func) (sigma : Substitution var (Term_ func var))
      (F1 F2 : Form_ pred func var),
      Neg (Or F1 F2) \in Gamma -> hasTableau_ (Gamma ,, Neg F1 ,, Neg F2) S Sf sigma -> hasTableau_ Gamma S Sf sigma

  (** Beta rule *)
  | hasTableauOr :
    forall (Gamma : con) (S1 S2 : set_var) (Sf1 Sf2 : set_func) (sigma : Substitution var (Term_ func var))
      (F1 F2 : Form_ pred func var),
      (Or F1 F2) \in Gamma -> hasTableau_ (Gamma ,, F1) S1 Sf1 sigma -> hasTableau_ (Gamma ,, F2) S2 Sf2 sigma ->
      disjoint S1 S2 -> disjoint Sf1 Sf2 -> hasTableau_ Gamma (S1 \union S2) (Sf1 \union Sf2) sigma

  (** Gamma rule *)
  | hasTableauAll :
    forall (Gamma : con) (S : set_var) (Sf : set_func) (sigma : Substitution var (Term_ func var))
      (x : var) (F : Form_ pred func var),
      (All F) \in Gamma -> isFresh x S -> hasTableau_ (Gamma ,, F{0 \to x}) S Sf sigma ->
      hasTableau_ Gamma (add x S) Sf sigma.

   (** Delta rule *)
  (* | hasTableauNegAll : *)
  (*   forall (Gamma : con) (S : set_var) (Sf : set_func) (sigma : Substitution var (Term_ func var)) *)
  (*     (f : func) (F : Form_ pred func var), *)
  (*     (Neg (All F)) \in Gamma -> isFresh f Sf -> hasTableau_ (Gamma ,, Neg F{0 \to sko f foo}) S Sf sigma -> *)
  (*     hasTableau_ Gamma S (add f Sf) sigma. *)

  Definition hasTableau (Gamma : con) (sigma : Substitution var (Term_ func var)) : Prop :=
    exists (S : set_var) (Sf : set_func), hasTableau_ Gamma S Sf sigma.
End TableauxProofs.
