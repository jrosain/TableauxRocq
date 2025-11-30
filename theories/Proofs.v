(** * Proofs: definition of free-variable tableaux proofs. *)

From Tableaux Require Import Semantics.
From Tableaux Require Import Skolemization.
From Tableaux Require Import Syntax.

Section TableauxProofs.
  Context `{set_nat : set nat} {pred func var : Atom} (sko : Skolemization_ pred func var).

  Existing Instance fv_ctx.

  Let set_var := set_atom var.
  Let set_func := set_atom func.
  Let Con := Con_ pred func var.
  Let Term := Term_ func var.
  Let Form := Form_ pred func var.
  Let sko_record := sko_record sko.

  Inductive hasTableau_
    : Con -> set_var -> sko_record -> Substitution var Term -> Prop :=

  (** Axioms *)
  | hasTableauBot :
    forall (Gamma : Con) (S : set_var) (Sf : sko_record) (sigma : Substitution var Term),
      (Bot \in Gamma) -> hasTableau_ Gamma S Sf sigma
  | hasTableauContr :
    forall (Gamma : Con) (S : set_var) (Sf : sko_record) (sigma : Substitution var Term)
      (P P' : Form), (P \in Gamma) -> (P' \in Gamma) -> Neg P@[sigma] = P'@[sigma] -> hasTableau_ Gamma S Sf sigma

  (** Alpha rules *)
  | hasTableauNegNeg :
    forall (Gamma : Con) (S : set_var) (Sf : sko_record) (sigma : Substitution var Term)
      (F : Form), Neg (Neg F) \in Gamma -> hasTableau_ (Gamma ,, F) S Sf sigma -> hasTableau_ Gamma S Sf sigma
  | hasTableauNegOr :
    forall (Gamma : Con) (S : set_var) (Sf : sko_record) (sigma : Substitution var Term)
      (F1 F2 : Form),
      Neg (Or F1 F2) \in Gamma -> hasTableau_ (Gamma ,, Neg F1 ,, Neg F2) S Sf sigma -> hasTableau_ Gamma S Sf sigma

  (** Beta rule *) (* TODO: JOIN CONDITION IN SKOLEMIZATION *)
  | hasTableauOr :
    forall (Gamma : Con) (S1 S2 : set_var) (Sf1 Sf2 : sko_record) (sigma : Substitution var Term)
      (F1 F2 : Form),
      (Or F1 F2) \in Gamma -> hasTableau_ (Gamma ,, F1) S1 Sf1 sigma -> hasTableau_ (Gamma ,, F2) S2 Sf2 sigma ->
      disjoint S1 S2 -> hasTableau_ Gamma (S1 \union S2) (join Sf1 Sf2) sigma

  (** Gamma rule *)
  | hasTableauAll :
    forall (Gamma : Con) (S : set_var) (Sf : sko_record) (sigma : Substitution var Term)
      (x : var) (F : Form),
      (All F) \in Gamma -> isFresh x S -> hasTableau_ (Gamma ,, F{0 \to Free x}) S Sf sigma ->
      hasTableau_ Gamma (add x S) Sf sigma

   (** Delta rule *)
  | hasTableauNegAll :
    forall (Gamma : Con) (S : set_var) (Sf : sko_record) (sigma : Substitution var Term)
      (F : Form) (t : Term) (Hsko : is_sko t (Neg F) (fv Gamma) Sf),
      (Neg (All F)) \in Gamma -> hasTableau_ (Gamma ,, Neg F{0 \to t}) S Sf sigma ->
      hasTableau_ Gamma S (add_symbol (symbol sko t Hsko) F Sf) sigma.

  Definition hasTableau (Gamma : Con) (sigma : Substitution var Term) : Prop :=
    exists (S : set_var) (Sf : sko_record), hasTableau_ Gamma S Sf sigma.
End TableauxProofs.

(* TODO: structural lemmas, e.g., strengthening, exchange law, (need something else?) *)

Section TableauxSoundness.
  Context `{set_nat : set nat} {pred func var : Atom} (sko : Skolemization_ pred func var).

  Theorem hasTableau_sound :
    forall (F : Form_ pred func var) (sigma : Substitution var (Term_ func var)),
      hasTableau sko {{ Neg F }} sigma -> \models F.
  Proof.
    Admitted.

(* Theorem hasTableau_sound : *)
(*     forall (Gamma : Con_ pred func var) (sigma : Substitution var (Term_ func var)), *)
(*       hasTableau sko Gamma sigma -> is_countersat (con_to_formula Gamma). *)
(*   Proof. *)
(*     intros ?? (S & Sf & htab). induction htab. *)
(*     Admitted. *)
End TableauxSoundness.
