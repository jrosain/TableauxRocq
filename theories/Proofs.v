(** * Proofs: definition of free-variable tableaux proofs. *)

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

Arguments Con_ : clear implicits.

Notation "Gamma ,, A" := (extend_ctx Gamma A) (at level 20).
Notation "A \in Gamma" := (in_ctx A Gamma) (at level 30).
Notation "{{ }}" := (empty_ctx).
Notation "{{ F }}" := (empty_ctx ,, F).
Notation "{{ F1 ;; F2 ;; .. ;; Fk }}" :=
  (extend_ctx .. (extend_ctx (extend_ctx empty_ctx F1) F2) .. Fk).

Section TableauxProofs.
  Context `{set_nat : set nat} {pred func var : Atom} (sko : Skolemization_ pred func var).

  Existing Instance fv_ctx.

  Let set_var := set_atom var.
  Let set_func := set_atom func.
  Let Con := Con_ pred func var sko.
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
      are_disjoint S1 S2 -> hasTableau_ Gamma (S1 \union S2) (join Sf1 Sf2) sigma

  (** Gamma rule *)
  | hasTableauAll :
    forall (Gamma : Con) (S : set_var) (Sf : sko_record) (sigma : Substitution var Term)
      (x : var) (F : Form),
      (All F) \in Gamma -> isFresh x (fv Gamma) -> hasTableau_ (Gamma ,, F{0 \to Free x}) S Sf sigma ->
      hasTableau_ Gamma (add x S) Sf sigma

   (** Delta rule *)
  | hasTableauNegAll :
    forall (Gamma : Con) (S : set_var) (Sf : sko_record) (sigma : Substitution var Term)
      (F : Form) (t : Term) (Hsko : is_sko t (Neg F) (fv Gamma) (con_sko_record Gamma)),
      (Neg (All F)) \in Gamma -> hasTableau_ (set_con_sko_record
                                       (add_symbol (symbol sko t Hsko) F (con_sko_record Gamma))
                                       (Gamma ,, Neg F{0 \to t})) S Sf sigma ->
      hasTableau_ Gamma S (add_symbol (symbol sko t Hsko) F Sf) sigma.

  Definition hasTableau (Gamma : Con) (sigma : Substitution var Term) : Prop :=
    exists (S : set_var) (Sf : sko_record), hasTableau_ Gamma S Sf sigma.
End TableauxProofs.

(* TODO: structural lemmas, e.g., strengthening, exchange law, (need something else?) *)

Section TableauxSoundness.
  Context `{set_nat : set nat} {pred func var : Atom} (sko : Skolemization_ pred func var).

  Let Con := Con_ pred func var sko.
  Let Form := Form_ pred func var.
  Let Term := Term_ func var.

  Lemma subst_ctx_subst_list :
    forall (Gamma : Con) (sigma : Substitution var Term),
      (forms Gamma)@[sigma] = forms (Gamma@[sigma]).
  Proof using Type.
    intros [l sko_] sigma; cbn. clear sko_; induction l as [|F Fs IHFs]; auto.
    cbn. f_equal. apply IHFs.
  Qed.

  Lemma in_ctx_in_substituted_ctx :
    forall (Gamma : Con) (F : Form) (sigma : Substitution var Term),
      F \in Gamma -> F@[sigma] \in Gamma@[sigma].
  Proof using Type.
    intros ???. destruct Gamma as [l sko_]; cbn. clear sko_.
    induction l as [|G Gs IHGs]; intros Hin; inversion Hin.
    - rewrite H. cbn. now left.
    - right. now apply IHGs.
  Qed.

  Theorem hasTableau_sound :
    forall (sigma : Substitution var Term) (Gamma : Con) (F : Form),
      hasTableau sko (Gamma ,, Neg F) sigma -> ((forms Gamma)@[sigma] \models F@[sigma]).
  Proof.
    intros ??? (S & Sf & htab).
    rewrite models_iff. replace (Neg F@[sigma] :: (forms Gamma)@[sigma]) with (forms (Gamma ,, Neg F)@[sigma]).
    2: { rewrite subst_ctx_subst_list. now cbn. }
    induction htab.
    - apply in_form_list_models.
      apply in_ctx_in_substituted_ctx with (sigma := sigma) in H.
      now cbn in H.
    - apply in_ctx_in_substituted_ctx with (sigma := sigma) in H0, H.
      apply models_P_neg_P with (F := P@[sigma]).
      + now apply in_form_list_models.
      + apply in_form_list_models. now rewrite H1.
    - apply extend_with_equiv_form with (F := F0@[sigma]) (G := Neg (Neg F0@[sigma])); auto.
      + apply neg_neg_equiv.
      + now apply in_ctx_in_substituted_ctx with (sigma := sigma) in H.
    - apply extend_with_double_equiv_form with (F1 := Neg F2@[sigma]) (F2 := Neg F1@[sigma])
                                               (G := Neg (Or F1 F2)@[sigma]); auto.
      + apply neg_equiv. cbn.
        rewrite or_comm. apply or_equiv.
        all: symmetry; apply neg_neg_equiv.
      + now apply in_ctx_in_substituted_ctx with (sigma := sigma) in H.
    - apply double_extend_with_equiv_form with (F1 := F1@[sigma]) (F2 := F2@[sigma]) (G := (Or F1 F2)@[sigma]);
        auto.
      + reflexivity.
      + now apply in_ctx_in_substituted_ctx with (sigma := sigma) in H.
    - apply extend_with_equiv_form' with (F := F0 {0 \to Free x}@[sigma]) (G := (All F0)@[sigma]); auto.
      + cbn. rewrite form_subst_opening.
        apply instantiate_imply_all, isLocallyClosed_isLocallyClosed_subst.
        red. now cbn.
      + now apply in_ctx_in_substituted_ctx with (sigma := sigma) in H.
  Admitted.
End TableauxSoundness.

Module ConcreteProofInstances.
  Export ConcreteSkolemizationInstances.

  Definition Con := Con_ string string string.
End ConcreteProofInstances.
