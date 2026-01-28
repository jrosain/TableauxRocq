(** * Proofs: definition of free-variable tableaux proofs. *)

From Stdlib Require Import Classical.

From Tableaux Require Import Semantics.
From Tableaux Require Import Skolemization.
From Tableaux Require Import Syntax.

(** ** Contexts *)

(** As we want to keep a [sko_record] in the contexts, contexts get parameterized by
    skolemization instances. *)
Section Context.
  Context `{set_nat : set nat} {pred func var : Atom}.

  Let Form := Form_ pred func var.

  Definition Con_ := list (Form_ pred func var).

  Definition empty_ctx : Con_ := [].
  Definition in_ctx (F : Form) (Gamma : Con_) : Prop := List.In F Gamma.
  Definition extend_ctx (Gamma : Con_) (F : Form) : Con_ := F :: Gamma.

  #[global] Instance fv_ctx : @FV var Con_ := ltac:(typeclasses eauto).

  Fixpoint subst_ctx_ (Gamma : Con_) (sigma : Substitution var (Term_ func var)) : Con_ :=
    match Gamma with
    | [] => []
    | F :: Fs => F@[sigma] :: subst_ctx_ Fs sigma
    end.

  #[global] Instance subst_ctx : Subst Con_ (Term_ func var) :=
    subst_ctx_.

  Definition ctx_to_form (Gamma : Con_) := ls_to_form Gamma.
End Context.

Arguments Con_ : clear implicits.

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
  Let Con := Con_ pred func var.
  Let Term := Term_ func var.
  Let Form := Form_ pred func var.
  Let sko_record := sko_record sko.

  (** We unset the automatic generation of elimination schemes to get a dependent elimination
      for the predicate [hasTableau_]. *)
  Unset Elimination Schemes.
  Inductive hasTableau_
    : Con -> sko_record -> Substitution var Term -> Prop :=

  (** Axioms *)
  | hasTableauBot :
    forall (Gamma : Con) (symbs : sko_record) (sigma : Substitution var Term),
      (Bot \in Gamma) -> hasTableau_ Gamma symbs sigma
  | hasTableauContr :
    forall (Gamma : Con) (symbs : sko_record) (sigma : Substitution var Term)
      (P P' : Form),
      P \in Gamma -> P' \in Gamma -> Neg P@[sigma] = P'@[sigma] -> hasTableau_ Gamma symbs sigma

  (** Alpha rules *)
  | hasTableauNegNeg :
    forall (Gamma : Con) (symbs : sko_record) (sigma : Substitution var Term) (F : Form),
      Neg (Neg F) \in Gamma -> hasTableau_ (Gamma ,, F) symbs sigma -> hasTableau_ Gamma symbs sigma
  | hasTableauNegOr :
    forall (Gamma : Con) (symbs : sko_record) (sigma : Substitution var Term) (F1 F2 : Form),
      Neg (Or F1 F2) \in Gamma -> hasTableau_ (Gamma ,, Neg F1 ,, Neg F2) symbs sigma -> hasTableau_ Gamma symbs sigma

  (** Beta rule *)
  | hasTableauOr :
    forall (Gamma : Con) (symbs : sko_record) (sigma : Substitution var Term) (F1 F2 : Form),
      (Or F1 F2) \in Gamma -> hasTableau_ (Gamma ,, F1) symbs sigma -> hasTableau_ (Gamma ,, F2) symbs sigma ->
      hasTableau_ Gamma symbs sigma

  (** Gamma rule *)
  | hasTableauAll :
    forall (Gamma : Con) (symbs : sko_record) (sigma : Substitution var Term) (x : var) (F : Form),
      (All F) \in Gamma -> hasTableau_ (Gamma ,, F{0 \to Free x}) symbs sigma ->
      hasTableau_ Gamma symbs sigma

   (** Delta rule *)
  | hasTableauNegAll :
    forall (Gamma : Con) (symbs : sko_record) (sigma : Substitution var Term)
      (F : Form) (t : Term) (Hsko : is_sko t (Neg F) (fv Gamma) symbs = true),
      (Neg (All F)) \in Gamma ->
      hasTableau_ (Gamma ,, Neg F{0 \to t}) (add_symbol (symbol sko t Hsko) F symbs) sigma ->
      hasTableau_ Gamma symbs sigma.
  Set Elimination Schemes.
  Scheme hasTableau__ind := Induction for hasTableau_ Sort Prop.

  Definition hasTableau (Gamma : Con) (sigma : Substitution var Term) : Prop :=
    hasTableau_ Gamma empty_record sigma.

  (** *** Satisfiability of a tableau *)

  (** A tableau is said satisfiable if there exists a branch such that all the formulas of
      a branch are satisfiable. We can define it as an inductive predicate. *)
  Inductive is_tableau_satisfiable (M : Model pred func) (mu : env M var)
    {Gamma : Con} {symbs : sko_record} {sigma : Substitution var Term} :
    hasTableau_ Gamma symbs sigma -> Prop :=

  | satisfiable_hasTableauContr :
    forall (P P' : Form) (hin : P \in Gamma) (hin' : P' \in Gamma) (e : Neg P@[sigma] = P'@[sigma]),
      [[ M # [] # mu |- ctx_to_form Gamma ]] ->
      is_tableau_satisfiable M mu (hasTableauContr Gamma symbs sigma P P' hin hin' e)

  | satisfiable_hasTableauNegNeg :
    forall (F : Form) (hin : Neg (Neg F) \in Gamma) (htab : hasTableau_ (Gamma ,, F) symbs sigma),
      is_tableau_satisfiable M mu htab ->
      is_tableau_satisfiable M mu (hasTableauNegNeg Gamma symbs sigma F hin htab)

  | satisfiable_hasTableauNegOr :
    forall (F1 F2 : Form) (hin : Neg (Or F1 F2) \in Gamma) (htab : hasTableau_ (Gamma ,, Neg F1 ,, Neg F2) symbs sigma),
      is_tableau_satisfiable M mu htab ->
      is_tableau_satisfiable M mu (hasTableauNegOr Gamma symbs sigma F1 F2 hin htab)

  | satisfiable_hasTableauOr1 :
    forall (F1 F2 : Form) (hin : (Or F1 F2) \in Gamma) (htab1 : hasTableau_ (Gamma ,, F1) symbs sigma)
      (htab2 : hasTableau_ (Gamma ,, F2) symbs sigma),
      is_tableau_satisfiable M mu htab1 ->
      is_tableau_satisfiable M mu (hasTableauOr Gamma symbs sigma F1 F2 hin htab1 htab2)

  | satisfiable_hasTableauOr2 :
    forall (F1 F2 : Form) (hin : (Or F1 F2) \in Gamma) (htab1 : hasTableau_ (Gamma ,, F1) symbs sigma)
      (htab2 : hasTableau_ (Gamma ,, F2) symbs sigma),
      is_tableau_satisfiable M mu htab2 ->
      is_tableau_satisfiable M mu (hasTableauOr Gamma symbs sigma F1 F2 hin htab1 htab2)

  | satisfiable_hasTableauAll :
    forall (x : var) (F : Form) (hin : (All F) \in Gamma) (htab : hasTableau_ (Gamma ,, F{0 \to Free x}) symbs sigma),
      is_tableau_satisfiable M mu htab ->
      is_tableau_satisfiable M mu (hasTableauAll Gamma symbs sigma x F hin htab)

  | satisfiable_hasTableauNegAll :
    forall (F : Form) (t : Term) (Hsko : is_sko t (Neg F) (fv Gamma) symbs = true)
      (hin : (Neg (All F)) \in Gamma)
      (htab : hasTableau_ (Gamma ,, Neg F{0 \to t}) (add_symbol (symbol sko t Hsko) F symbs) sigma),
      is_tableau_satisfiable M mu htab ->
      is_tableau_satisfiable M mu (hasTableauNegAll Gamma symbs sigma F t Hsko hin htab).
End TableauxProofs.
Arguments is_tableau_satisfiable {_ _ _ _ _} _ _ {_ _ _} _.

(* TODO: structural lemmas, e.g., strengthening, exchange law, (need something else?) *)

Section TableauxSoundness.
  Context `{set_nat : set nat} {pred func var : Atom} (sko : Skolemization_ pred func var).

  Let Con := Con_ pred func var.
  Let Form := Form_ pred func var.
  Let Term := Term_ func var.

  (** We start by showing that if the root formula of a tableau is satisfiable, then this
      tableau is also satisfiable.

      Note that [Gamma] must be a closed context. *)
  Lemma hasTableau_satisfiable :
    forall (M : Model pred func) {Gamma : Con} {symbs : sko_record sko}
      {sigma : Substitution var Term} (T : hasTableau_ sko Gamma symbs sigma) (mu : env M var),
      [[ M # [] # mu |- ctx_to_form Gamma ]] ->
      is_tableau_satisfiable M mu T.
  Proof.
    intros ?????? hinterp. induction T.
    - exfalso. have contra := in_form_list_interp i hinterp.
      now cbn in contra.
    - now apply satisfiable_hasTableauContr.
    - constructor. apply IHT. eapply extend_with_equiv_form; eauto. apply neg_neg_equiv.
    - constructor. apply IHT. apply interp_list_commute.
      eapply extend_with_equiv_form; eauto.
      apply neg_equiv. etransitivity.
      + apply or_comm.
      + apply or_equiv; symmetry; apply neg_neg_equiv.
    - have hinterp' := in_form_list_interp i hinterp.
      destruct hinterp'.
      + apply satisfiable_hasTableauOr1. apply IHT1.
        cbn. intros [hnF1 | hnG]; auto.
      + apply satisfiable_hasTableauOr2. apply IHT2.
        cbn. intros [hnF2 | hnG]; auto.
    - constructor. apply IHT.
      eapply extend_with_imply_form; eauto.
      apply instantiate_imply_all. now cbn.
    - constructor. apply IHT. eapply extend_with_imply_form'.
      3: apply i.
      all: auto.
      exists M, mu. intros hF. apply NNPP in hF.
      change ([[ M # [] # mu |- F { 0 \to t } ]]) in hF; split.
      + intros hnAll; apply hnAll. intro c.
        change [[M # [c] # mu |- F]]. admit.
      + admit.
  Admitted.

  (** Of course, no tableau is satisfiable. We start by showing 2 small lemmas: *)
  Lemma in_ctx_in_substituted_ctx :
    forall (Gamma : Con) (F : Form) (sigma : Substitution var Term),
      F \in Gamma -> F@[sigma] \in Gamma@[sigma].
  Proof using Type.
    intros ???. induction Gamma as [|G Gs IHGs]; intros Hin; inversion Hin.
    - rewrite H. cbn. now left.
    - right. now apply IHGs.
  Qed.

  Lemma subst_ctx_subst_list :
    forall (Gamma : Con) (sigma : Substitution var Term),
      (ls_to_form Gamma)@[sigma] = ls_to_form (Gamma@[sigma]).
  Proof using Type.
    intros; cbn. induction Gamma as [|F Fs IHFs]; auto.
    cbn. do 3 f_equal. apply IHFs.
  Qed.

  Lemma hasTableau_not_satisfiable :
    forall (M : Model pred func)
      {Gamma : Con} {symbs : sko_record sko} {sigma : Substitution var Term}
      (T : hasTableau_ sko Gamma symbs sigma), is_tableau_satisfiable M (subst_to_env M sigma) T -> False.
  Proof using Type.
    intros ????? hsat. remember (subst_to_env M sigma) as mu. induction hsat.
    2-7: now apply IHhsat.
    subst. rewrite -subst_commutes_with_env_forms in H.
    have h1 : interpret_form_ M [] (empty_env M var) P@[sigma].
    { eapply in_form_list_interp.
      - apply in_ctx_in_substituted_ctx; eauto.
      - rewrite -subst_ctx_subst_list //. }
    have h2 : interpret_form_ M [] (empty_env M var) (Neg P)@[sigma].
    { eapply in_form_list_interp.
      - cbn; rewrite e. apply in_ctx_in_substituted_ctx; eauto.
      - rewrite -subst_ctx_subst_list //. }
    cbn in h2. now apply h2.
  Qed.

  Theorem hasTableau_sound :
    forall (sigma : Substitution var Term) (Gamma : Con) (F : Form),
      isClosed (Gamma ,, Neg F) ->
      hasTableau sko (Gamma ,, Neg F) sigma -> Gamma \models F.
  Proof using Type.
    intros ??? hclosedGamma htab.
    rewrite models_iff. intros M. left. intro hsat.
    have hsat' : interpret_form_ M [] (subst_to_env M sigma) (ls_to_form (Neg F :: Gamma)).
    { change [[ M # [] # subst_to_env M sigma |- ls_to_form (Neg F :: Gamma) ]].
      rewrite -subst_commutes_with_env_forms.
      rewrite isClosed_subst_form; auto.
      rewrite isClosedList_isClosedFormList //. }
    clear hsat. eapply hasTableau_satisfiable with (sigma := sigma) (T := htab) in hsat'.
    eapply hasTableau_not_satisfiable; eauto.
  Qed.
End TableauxSoundness.

Module ConcreteProofInstances.
  Export ConcreteSkolemizationInstances.

  Definition Con := Con_ string string string.
End ConcreteProofInstances.
