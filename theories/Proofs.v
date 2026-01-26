(** * Proofs: definition of free-variable tableaux proofs. *)

From Stdlib Require Import Classical.

From Tableaux Require Import Semantics.
From Tableaux Require Import Skolemization.
From Tableaux Require Import Syntax.

(** ** Contexts *)

(** As we want to keep a [sko_record] in the contexts, contexts get parameterized by
    skolemization instances. *)
Section Contexts.
  Context `{set_nat : set nat} {pred func var : Atom} {sko : Skolemization_ pred func var}.

  Record Con_ :=
    { forms : list (Form_ pred func var)
    ; con_sko_record : sko_record sko }.

  Definition empty_ctx : Con_ :=
    {| forms := []
    ;  con_sko_record := empty_record |}.

  Definition in_ctx (F : Form_ pred func var) (Gamma : Con_) : Prop :=
    List.In F (forms Gamma).

  Definition extend_ctx (Gamma : Con_) (A : Form_ pred func var) : Con_ :=
    {| forms := A :: forms Gamma
    ;  con_sko_record := con_sko_record Gamma |}.

  Fixpoint fv_ctx_ (Gamma : list (Form_ pred func var)) : set_atom var :=
    match Gamma with
    | [] => empty_set
    | F :: Fs => fv F \union fv_ctx_ Fs
    end.

  #[global] Instance fv_ctx : @FV var Con_ :=
    fun Gamma => fv_ctx_ (forms Gamma).

  Fixpoint subst_ctx_ (Gamma : list (Form_ pred func var)) (sigma : Substitution var (Term_ func var))
    : list (Form_ pred func var) :=
    match Gamma with
    | [] => []
    | F :: Fs => F@[sigma] :: subst_ctx_ Fs sigma
    end.

  #[global] Instance subst_ctx : Subst Con_ (Term_ func var) :=
    fun Gamma sigma =>
      {| forms := subst_ctx_ (forms Gamma) sigma
      ;  con_sko_record := con_sko_record Gamma |}. (* TODO: we probably want to subst this *)

  Definition set_con_sko_record (record : sko_record sko) (Gamma : Con_) : Con_ :=
    {| forms := forms Gamma
    ;  con_sko_record := record |}.
End Contexts.

Arguments Con_ {_} _ _ _.

Notation "Gamma ,, A" := (extend_ctx Gamma A) (at level 20).
Notation "A \in Gamma" := (in_ctx A Gamma) (at level 30).
Notation "{{ }}" := (empty_ctx).
Notation "{{ F }}" := (empty_ctx ,, F).
Notation "{{ F1 ;; F2 ;; .. ;; Fk }}" :=
  (extend_ctx .. (extend_ctx (extend_ctx empty_ctx F1) F2) .. Fk).

(** ** Definition of tableaux *)
Section TableauxProofs.
  Context `{set_nat : set nat} {pred func var : Atom} (sko : Skolemization_ pred func var).

  Existing Instance fv_ctx.

  Let set_var := set_atom var.
  Let set_func := set_atom func.
  Let Con := Con_ pred func var sko.
  Let Term := Term_ func var.
  Let Form := Form_ pred func var.
  Let sko_record := sko_record sko.

  (** We unset the automatic generation of elimination schemes to get a dependent elimination
      for the predicate [hasTableau_]. *)
  Unset Elimination Schemes.
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

  (** Beta rule *)
  | hasTableauOr :
    forall (Gamma : Con) (S1 S2 : set_var) (Sf1 Sf2 : sko_record) (sigma : Substitution var Term)
      (F1 F2 : Form),
      (Or F1 F2) \in Gamma -> hasTableau_ (Gamma ,, F1) S1 Sf1 sigma -> hasTableau_ (Gamma ,, F2) S2 Sf2 sigma ->
      are_disjoint S1 S2 -> hasTableau_ Gamma (S1 \union S2) (join Sf1 Sf2) sigma

  (** Gamma rule *)
  | hasTableauAll :
    forall (Gamma : Con) (S : set_var) (Sf : sko_record) (sigma : Substitution var Term)
      (x : var) (F : Form),
      (All F) \in Gamma -> isFresh x (fv Gamma) = true -> hasTableau_ (Gamma ,, F{0 \to Free x}) S Sf sigma ->
      hasTableau_ Gamma (add x S) Sf sigma

   (** Delta rule *)
  | hasTableauNegAll :
    forall (Gamma : Con) (S : set_var) (Sf : sko_record) (sigma : Substitution var Term)
      (F : Form) (t : Term) (Hsko : is_sko t (Neg F) (fv Gamma) (con_sko_record Gamma) = true),
      (Neg (All F)) \in Gamma -> hasTableau_ (set_con_sko_record
                                       (add_symbol (symbol sko t Hsko) F (con_sko_record Gamma))
                                       (Gamma ,, Neg F{0 \to t})) S Sf sigma ->
      hasTableau_ Gamma S (add_symbol (symbol sko t Hsko) F Sf) sigma.
  Set Elimination Schemes.
  Scheme hasTableau__ind := Induction for hasTableau_ Sort Prop.

  Definition hasTableau (Gamma : Con) (sigma : Substitution var Term) : Prop :=
    exists (S : set_var) (Sf : sko_record), hasTableau_ Gamma S Sf sigma.

  (** *** Satisfiability of a tableau *)

  (** A tableau is said satisfiable if there exists a branch such that all the formulas of
      a branch are satisfiable. We can define it as an inductive predicate. *)
  Inductive is_tableau_satisfiable (M : Model pred func) (mu : env M var) :
    forall {Gamma : Con} {S : set_var} {Sf : sko_record} {sigma : Substitution var Term},
      hasTableau_ Gamma S Sf sigma -> Prop :=

  | satisfiable_hasTableauContr :
    forall (Gamma : Con) (S : set_var) (Sf : sko_record) (sigma : Substitution var Term)
      (P P' : Form) (hin : P \in Gamma) (hin' : P' \in Gamma) (e : Neg P@[sigma] = P'@[sigma]),
      [[ M # [] # mu |- ls_to_form (forms Gamma) ]] ->
      is_tableau_satisfiable M mu (hasTableauContr Gamma S Sf sigma P P' hin hin' e)

  | satisfiable_hasTableauNegNeg :
    forall (Gamma : Con) (S : set_var) (Sf : sko_record) (sigma : Substitution var Term)
      (F : Form) (hin : Neg (Neg F) \in Gamma) (htab : hasTableau_ (Gamma ,, F) S Sf sigma),
      is_tableau_satisfiable M mu htab ->
      is_tableau_satisfiable M mu (hasTableauNegNeg Gamma S Sf sigma F hin htab)

  | satisfiable_hasTableauNegOr :
    forall (Gamma : Con) (S : set_var) (Sf : sko_record) (sigma : Substitution var Term)
      (F1 F2 : Form) (hin : Neg (Or F1 F2) \in Gamma) (htab : hasTableau_ (Gamma ,, Neg F1 ,, Neg F2) S Sf sigma),
      is_tableau_satisfiable M mu htab ->
      is_tableau_satisfiable M mu (hasTableauNegOr Gamma S Sf sigma F1 F2 hin htab)

  | satisfiable_hasTableauOr1 :
    forall (Gamma : Con) (S1 S2 : set_var) (Sf1 Sf2 : sko_record) (sigma : Substitution var Term)
      (F1 F2 : Form) (hin : (Or F1 F2) \in Gamma) (htab1 : hasTableau_ (Gamma ,, F1) S1 Sf1 sigma)
      (htab2 : hasTableau_ (Gamma ,, F2) S2 Sf2 sigma) (hdisj : are_disjoint S1 S2),
      is_tableau_satisfiable M mu htab1 ->
      is_tableau_satisfiable M mu (hasTableauOr Gamma S1 S2 Sf1 Sf2 sigma F1 F2 hin htab1 htab2 hdisj)

  | satisfiable_hasTableauOr2 :
    forall (Gamma : Con) (S1 S2 : set_var) (Sf1 Sf2 : sko_record) (sigma : Substitution var Term)
      (F1 F2 : Form) (hin : (Or F1 F2) \in Gamma) (htab1 : hasTableau_ (Gamma ,, F1) S1 Sf1 sigma)
      (htab2 : hasTableau_ (Gamma ,, F2) S2 Sf2 sigma) (hdisj : are_disjoint S1 S2),
      is_tableau_satisfiable M mu htab2 ->
      is_tableau_satisfiable M mu (hasTableauOr Gamma S1 S2 Sf1 Sf2 sigma F1 F2 hin htab1 htab2 hdisj)

  | satisfiable_hasTableauAll :
    forall (Gamma : Con) (S : set_var) (Sf : sko_record) (sigma : Substitution var Term)
      (x : var) (F : Form) (hin : (All F) \in Gamma) (hfresh : isFresh x (fv Gamma) = true)
      (htab : hasTableau_ (Gamma ,, F{0 \to Free x}) S Sf sigma),
      is_tableau_satisfiable M mu htab ->
      is_tableau_satisfiable M mu (hasTableauAll Gamma S Sf sigma x F hin hfresh htab)

  | satisfiable_hasTableauNegAll :
    forall (Gamma : Con) (S : set_var) (Sf : sko_record) (sigma : Substitution var Term)
      (F : Form) (t : Term) (Hsko : is_sko t (Neg F) (fv Gamma) (con_sko_record Gamma) = true)
      (hin : (Neg (All F)) \in Gamma)
      (htab : hasTableau_ (set_con_sko_record
                             (add_symbol (symbol sko t Hsko) F (con_sko_record Gamma))
                             (Gamma ,, Neg F{0 \to t})) S Sf sigma),
      is_tableau_satisfiable M mu htab ->
      is_tableau_satisfiable M mu (hasTableauNegAll Gamma S Sf sigma F t Hsko hin htab).
End TableauxProofs.
Arguments is_tableau_satisfiable {_ _ _ _ _} _ _ {_ _ _ _} _.

(* TODO: structural lemmas, e.g., strengthening, exchange law, (need something else?) *)

Section TableauxSoundness.
  Context `{set_nat : set nat} {pred func var : Atom} (sko : Skolemization_ pred func var).

  Let Con := Con_ pred func var sko.
  Let Form := Form_ pred func var.
  Let Term := Term_ func var.

  (** Of course, no tableau is satisfiable *)
  (* TODO: subst to env *)
  Lemma hasTableau_not_satisfiable :
    forall (M : Model pred func)
      {Gamma : Con} {S : set_atom var} {Sf : sko_record sko} {sigma : Substitution var Term}
      (T : hasTableau_ sko Gamma S Sf sigma), is_tableau_satisfiable M sigma T -> False.
  Proof.
    intros ??????? H. induction H.
    Admitted.

  Theorem hasTableau_sound :
    forall (sigma : Substitution var Term) (Gamma : Con) (F : Form),
      isClosed (forms (Gamma ,, Neg F)) ->
      hasTableau sko (Gamma ,, Neg F) sigma -> (forms Gamma \models F).
  Proof using Type.
    intros ??? hclosedGamma (S & Sf & htab).
    rewrite models_iff. intros M. left. intro hsat.
  Admitted.
End TableauxSoundness.

Module ConcreteProofInstances.
  Export ConcreteSkolemizationInstances.

  Definition Con := Con_ string string string.
End ConcreteProofInstances.
