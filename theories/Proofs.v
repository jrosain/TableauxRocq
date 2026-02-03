(** * Proofs: definition of free-variable tableaux proofs. *)

From Stdlib Require Import Classical.
From Stdlib Require Import Lia.

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
  Fixpoint mem_ctx (F : Form) (Gamma : Con_) : bool :=
    match Gamma with
    | [] => false
    | G :: Gamma => eqb F G || mem_ctx F Gamma
    end.

  Lemma mem_ctx_in_ctx :
    forall (Gamma : Con_) (F : Form), mem_ctx F Gamma = true <-> in_ctx F Gamma.
  Proof using Type.
    intros ??; induction Gamma as [|G Gs IHGs].
    - now cbn.
    - cbn; split.
      + intros h%Bool.orb_true_elim. destruct h.
        * rewrite eqbIsEq in e. now left.
        * rewrite IHGs in e. now right.
      + intros [e | hin].
        * rewrite e EqBool_refl. now cbn.
        * apply Bool.orb_true_intro. right. rewrite IHGs //.
  Qed.

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

  Definition sub_ctx (Gamma Gamma' : Con_) :=
    forall (F : Form), in_ctx F Gamma -> in_ctx F Gamma'.

  Definition is_sub_ctx (Gamma Gamma' : Con_) : bool :=
    forallb (fun F => mem_ctx F Gamma') Gamma.

  Lemma is_sub_ctx_sound :
    forall (Gamma Gamma' : Con_),
      is_sub_ctx Gamma Gamma' = true -> sub_ctx Gamma Gamma'.
  Proof using Type.
    intros ?? e. unfold is_sub_ctx in e. induction Gamma as [|F Gamma IHGamma].
    - now intros F contra.
    - cbn in e |- *. apply andb_prop in e. intros G [e' | hin].
      + subst. rewrite -mem_ctx_in_ctx. apply e.
      + apply IHGamma.
        * apply e.
        * apply hin.
  Qed.

  Lemma is_sub_ctx_complete :
    forall (Gamma Gamma' : Con_),
      sub_ctx Gamma Gamma' -> is_sub_ctx Gamma Gamma' = true.
  Proof using Type.
    intros ?? hsub. induction Gamma as [|F Gamma IHGamma]; cbn; auto.
    apply andb_true_intro; split.
    - rewrite mem_ctx_in_ctx. apply hsub. now left.
    - apply IHGamma. intros G hin. apply hsub. now right.
  Qed.

  Lemma extend_sub_ctx :
    forall (Gamma Gamma' : Con_) (F : Form),
      sub_ctx Gamma Gamma' -> sub_ctx (F :: Gamma) (F :: Gamma').
  Proof using Type.
    intros ??? hsub; unfold sub_ctx in hsub |- *.
    intros G [-> | hG].
    - now left.
    - right; now apply hsub.
  Qed.

  Lemma cons_sub_ctx :
    forall (Gamma Gamma' : Con_) (F : Form),
      sub_ctx Gamma Gamma' -> sub_ctx Gamma (F :: Gamma').
  Proof using Type.
    intros ??? hsub. unfold sub_ctx in hsub |- *; cbn.
    intros G hin; right. now apply hsub.
  Qed.

  Lemma sub_ctx_cong :
    forall (Gamma Gamma' : Con_) (F G : Form),
      sub_ctx Gamma (F :: Gamma') -> sub_ctx (G :: Gamma) (F :: G :: Gamma').
  Proof using Type.
    intros ???? hsub H hin. cbn in hin |- *. destruct hin; auto.
    apply hsub in H0; cbn in H0; destruct H0 as [e | hin]; auto.
  Qed.

  Lemma sub_ctx_refl :
    forall (Gamma : Con_), sub_ctx Gamma Gamma.
  Proof using Type. do 2 intro. tauto. Qed.
End Context.

Arguments Con_ : clear implicits.

Notation "Gamma ,, A" := (extend_ctx Gamma A) (at level 20).
Notation "A \in Gamma" := (in_ctx A Gamma) (at level 30).
Notation "A \subseteq Gamma" := (sub_ctx A Gamma) (at level 30).
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
      (F : Form) (t : Term) (Hsko : sko t (Neg (All F)) symbs Gamma = true),
      (Neg (All F)) \in Gamma ->
      hasTableau_ (Gamma ,, Neg F{0 \to t}) (add_symbol (symbol sko Hsko) (Neg (All F)) symbs) sigma ->
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
      [[ M # [] # mu '|= ctx_to_form Gamma ]] ->
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
    forall (F : Form) (t : Term) (Hsko : sko t (Neg (All F)) symbs Gamma = true)
      (hin : (Neg (All F)) \in Gamma)
      (htab : hasTableau_ (Gamma ,, Neg F{0 \to t}) (add_symbol (symbol sko Hsko) (Neg (All F)) symbs) sigma),
      is_tableau_satisfiable M mu htab ->
      is_tableau_satisfiable M mu (hasTableauNegAll Gamma symbs sigma F t Hsko hin htab).
End TableauxProofs.
Arguments is_tableau_satisfiable {_ _ _ _ _} _ _ {_ _ _} _.

(** ** Some usual properties of tableaux *)
Section TableauxProperties.
  Context `{set_nat : set nat} {pred func var : Atom} (sko : Skolemization_ pred func var).

  Let Con := Con_ pred func var.
  Let Form := Form_ pred func var.
  Let Term := Term_ func var.

  (** If [Gamma \subseteq Gamma'], then as long as [fv Gamma = fv Gamma'], weakening holds for tableau proofs. *)
  Lemma weakening :
    forall (Gamma Gamma' : Con) (symbs : sko_record sko) (sigma : Substitution var Term),
      fv Gamma = fv Gamma' -> Gamma \subseteq Gamma' ->
      hasTableau_ sko Gamma symbs sigma ->
      hasTableau_ sko Gamma' symbs sigma.
  Proof using Type.
    intros ????? hsubset htab. generalize dependent Gamma'. induction htab;
      intros Gamma' efv hsubset.
    - apply hsubset in i. now apply hasTableauBot.
    - apply hsubset in i, i0. eapply hasTableauContr.
      + apply i.
      + apply i0.
      + apply e.
    - apply hsubset in i. eapply hasTableauNegNeg; eauto.
      apply IHhtab; auto.
      + cbn. now rewrite efv.
      + now apply extend_sub_ctx.
    - apply hsubset in i. eapply hasTableauNegOr; eauto.
      apply IHhtab; auto.
      + cbn. rewrite -!union_assoc efv //.
      + now do 2 apply extend_sub_ctx.
    - apply hsubset in i. eapply hasTableauOr; eauto.
      + apply IHhtab1.
        * cbn. now rewrite efv.
        * now apply extend_sub_ctx.
      + apply IHhtab2.
        * cbn. now rewrite efv.
        * now apply extend_sub_ctx.
    - apply hsubset in i. eapply hasTableauAll; eauto.
      apply IHhtab.
      2: now apply extend_sub_ctx.
      cbn. now rewrite efv.
    - apply hsubset in i.
      have Hsko' := Hsko. rewrite (sko_con_fv _ Gamma') in Hsko'; auto.
      apply hasTableauNegAll with (t := t) (Hsko := Hsko'); eauto.
      have esym : symbol sko Hsko = symbol sko Hsko'.
      { have e0 : get_symbol t = Some (symbol sko Hsko) by apply symbol_sound.
        have e1 : get_symbol t = Some (symbol sko Hsko') by apply symbol_sound.
        destruct t; try inversion e0.
        cbn in e0, e1; injection e0 => e0'; injection e1 => e1'. now destruct e0', e1'. }
      rewrite -esym. apply IHhtab.
      + cbn. now rewrite efv.
      + now apply extend_sub_ctx.
  Qed.
End TableauxProperties.

(** ** Tableaux using expansion *)

(** In this section, we develop the expansion of tableaux. Instead of defining them as inductive
    trees, we define trees with sequence of expansions corresponding to the rules defined in
    [hasTableau_]. Then, we can show that having a closed sequence of tableaux expansion is
    the same as having an [hasTableau_]. Moreover, the satisfiability of a sequence of tableaux
    is equivalent to the satisfiability of an [hasTableau_], which allow to show e.g. soundness
    of the [hasTableau_] inductive. *)

Reserved Notation "T |> T'" (at level 99, right associativity).
Section TableauxExpansion.
  Context `{set_nat : set nat} {pred func var : Atom} (sko : Skolemization_ pred func var).

  Let Con := Con_ pred func var.
  Let Form := Form_ pred func var.
  Let Term := Term_ func var.

  (** *** [ExpansionTableau] *)
  Section Def.
    (** We define an [ExpansionTableau] as a simple list of contexts. *)
    (* TODO: add a [sko_record] in the definition. *)
    Definition ExpansionTableau := list Con.

    (** Make an [ExpansionTableau] from a single [Con]. *)
    Definition mkExpansionTableau (Gamma : Con) : ExpansionTableau := [Gamma].

    (** Then, a [Branch] is simply a [Con]. *)
    Definition Branch := Con.

    (** We say that [B] is the [nth_branch_of T] if [T.(i)] is [B]. *)
    Definition nth_branch_of (T : ExpansionTableau) (i : nat) : option Branch := T.(i).

    (** A branch [B] contains [F] is [F \in B]. *)
    Definition branch_contains (B : Branch) (F : Form) : Prop := F \in B.

    (** To add [F] in a branch [B] in an [ExpansionTableau] [T], it suffices to replace
        [B] by by [F :: B]. *)
    Definition add_in_branch
      (T : ExpansionTableau) (i : nat) (F : Form) : ExpansionTableau :=
      match nth_branch_of T i with
      | None => T
      | Some B => replace_nth i (B ,, F) T
      end.

    Definition add_branch (T : ExpansionTableau) (F : Form) (B : Branch) : ExpansionTableau :=
      (B ,, F) :: T.

    Definition branch_to_con (B : Branch) : Con := B.

    (** An [ExpansionTableau] is said [satisfiable] if one of its branches is satisfiable. *)
    Definition is_satisfiable_ExpansionTableau (T : ExpansionTableau) : Prop :=
      exists (M : Model pred func), forall (mu : env M var),
        exists (B : Branch), List.In B T /\ [[ M # [] # mu '|= ctx_to_form (branch_to_con B) ]].

    (** An [ExpansionTableau] is said [closed] if there exists a substitution [sigma] such that
        every branch of [T] has a contradiction. *)
    Definition is_closed_ExpansionTableau (T : ExpansionTableau) :=
      exists (sigma : Substitution var Term),
        List.Forall
          (fun B => branch_contains B Bot \/
                   exists (P P' : Form),
                     branch_contains B P /\ branch_contains B P' /\
                       (Neg P')@[sigma] = P@[sigma]) T.

    (** If a context is satisfiable, then so is its associated [ExpansionTableau]. *)
    Lemma ctx_satisfiable_ExpansionTableau_satisfiable :
      forall (Gamma : Con),
        is_satisfiable (ctx_to_form Gamma) ->
        is_satisfiable_ExpansionTableau (mkExpansionTableau Gamma).
    Proof using Type.
      intros ? (M & hinterp). exists M; intro mu; exists Gamma; split.
      - now left.
      - apply hinterp.
    Qed.

    Lemma is_satisfiable_is_satisfiable_add_in_branch :
      forall (T : ExpansionTableau) (B : Branch) (F G : Form) (i : nat),
        nth_branch_of T i = Some B ->
        is_satisfiable_ExpansionTableau T -> branch_contains B F -> imply F G ->
        is_satisfiable_ExpansionTableau (add_in_branch T i G).
    Proof using Type.
      intros ????? ei (M & hsat) hcontains himp. exists M; intro mu. specialize (hsat mu).
      destruct hsat as (B0 & hin & hinterp). apply In_nth_error in hin; destruct hin as (j & ej).
      destruct (i == j); subst.
      - unfold nth_branch_of in ei; rewrite ei in ej; injection ej => eB; clear ej; subst.
        exists (B0 ,, G); split.
        + unfold add_in_branch, nth_branch_of. rewrite ei.
          eapply In_replace_nth; eauto.
        + eapply extend_with_imply_form; eauto.
      - exists B0; split; auto.
        unfold add_in_branch; rewrite ei. eapply In_replace_nth'; eauto.
    Qed.

    Lemma is_satisfiable_is_satisfiable_or :
      forall (T : ExpansionTableau) (B : Branch) (F G : Form) (i : nat),
        nth_branch_of T i = Some B -> branch_contains B (Or F G) ->
        is_satisfiable_ExpansionTableau T ->
        is_satisfiable_ExpansionTableau (add_branch (add_in_branch T i F) G B).
    Proof using Type.
      intros ????? ei hcontains (M & hsat). exists M; intro mu. specialize (hsat mu).
      destruct hsat as (B0 & hin & hinterp). apply In_nth_error in hin; destruct hin as (j & ej).
      destruct (i == j); subst.
      - unfold nth_branch_of in ei; rewrite ei in ej; injection ej => eB; clear ej; subst.
        have hinterpOr := in_form_list_interp hcontains hinterp.
        cbn in hinterpOr. destruct hinterpOr as [hF | hG].
        + exists (B0 ,, F); split.
          * right. unfold add_in_branch, nth_branch_of. rewrite ei.
            eapply In_replace_nth; eauto.
          * cbn; intros [hnF | hnB0]; auto.
        + exists (B0 ,, G); split.
          * now left.
          * cbn; intros [hnG | hnB0]; auto.
      - exists B0; split; auto. right. unfold add_in_branch. rewrite ei.
        eapply In_replace_nth'; eauto.
    Qed.

    Lemma add_in_branch_get :
      forall (T : ExpansionTableau) (B : Branch) (i : nat) (F : Form),
        nth_branch_of T i = Some B ->
        nth_branch_of (add_in_branch T i F) i = Some (B ,, F).
    Proof using Type.
      intros ???? e; unfold nth_branch_of in e |- *.
      unfold add_in_branch, nth_branch_of; rewrite e.
      erewrite get_replace_nth; eauto.
    Qed.

    Lemma branch_contains_add :
      forall (B : Branch) (F G : Form),
        branch_contains B F -> branch_contains (B ,, G) F.
    Proof using Type. intros. now right. Qed.
  End Def.
  (* We make these opaque as we provide everything needed in the API. *)
  #[global] Opaque ExpansionTableau.
  #[global] Opaque Branch.

  (** *** Expansion Sequence *)

  (** We give a relation between [ExpansionTableau] that mirrors the rules of
      [hasTableau_] *)
  Inductive ExpansionStep : ExpansionTableau -> ExpansionTableau -> Prop :=
  | expansion_NegNeg :
    forall (T : ExpansionTableau) (B : Branch) (F : Form) (i : nat),
      nth_branch_of T i = Some B -> branch_contains B (Neg (Neg F)) ->
      T |> (add_in_branch T i F)
  | expansion_NegOr :
    forall (T : ExpansionTableau) (B : Branch) (F1 F2 : Form) (i : nat),
      nth_branch_of T i = Some B -> branch_contains B (Neg (Or F1 F2)) ->
      T |> (add_in_branch (add_in_branch T i (Neg F1)) i (Neg F2))
  | expansion_Or :
    forall (T : ExpansionTableau) (B : Branch) (F1 F2 : Form) (i : nat),
      nth_branch_of T i = Some B -> branch_contains B (Or F1 F2) ->
      T |> (add_branch (add_in_branch T i F1) F2 B)
  | expansion_All :
    forall (T : ExpansionTableau) (B : Branch) (F : Form) (i : nat) (x : var),
      nth_branch_of T i = Some B -> branch_contains B (All F) ->
      T |> (add_in_branch T i (F {0 \to Free x}))
  | expansion_NegAll :
    forall (T : ExpansionTableau) (B : Branch) (F : Form) (i : nat) (t : Term)
      (symbs : sko_record sko),
      sko t (Neg (All F)) symbs (branch_to_con B) = true ->
      nth_branch_of T i = Some B -> branch_contains B (Neg (All F)) ->
      T |> (add_in_branch T i (Neg F {0 \to t}))
  where "T |> T'" := (ExpansionStep T T').

  (** An [ExpansionSequence] is a list of [ExpansionTableau] where each element is related
      to another w.r.t. [ExpansionStep]. *)
  Record ExpansionSequence :=
    { seq :> list ExpansionTableau
    ; isSequence :
      forall (i : nat) (T T' : ExpansionTableau),
        nth_error seq i = Some T -> nth_error seq (S i) = Some T' -> T |> T' }.

  (** An [ExpansionSequence] that has its first tableau satisfiable has all its
      [ExpansionTableaux] satisfiable. *)
  Lemma satisfiable_ExpansionSequence :
    forall (seq : ExpansionSequence) (T : ExpansionTableau),
      hd_error seq = Some T -> is_satisfiable_ExpansionTableau T ->
      forall (i : nat) (T' : ExpansionTableau), nth_error seq i = Some T' ->
                                         is_satisfiable_ExpansionTableau T'.
  Proof using set_nat.
    intros (seq & hisSeq) T e hsat i; cbn in *. induction i as [|j IHj]; intros T' e'.
    - rewrite nth_error_0 e in e'. injection e' => <- //.
    - have h : exists (T0 : ExpansionTableau), seq.(j) = Some T0.
      { have hlt := nth_error_Some' _ _ _ e'.
        exists (nth j seq T). apply nth_error_nth'. lia. }
      destruct h as (T0 & eT0); specialize (IHj T0 eT0).
      specialize (hisSeq j T0 T' eT0 e'). destruct hisSeq.

      (* Case: [Neg (Neg F)] *)
      + eapply is_satisfiable_is_satisfiable_add_in_branch; eauto.
        apply equiv_imply. symmetry; apply neg_neg_equiv.

      (* Case: [Neg (Or F1 F2)] *)
      + eapply is_satisfiable_is_satisfiable_add_in_branch with
          (F := Neg (Or F1 F2)) (T := add_in_branch T0 i (Neg F1)).
        * eapply add_in_branch_get; eauto.
        * eapply is_satisfiable_is_satisfiable_add_in_branch; eauto.
          intros M sigma hinterp hF1. apply hinterp. now left.
        * now apply branch_contains_add.
        * intros M sigma hinterp hF2. apply hinterp. now right.

      (* Case: [Or F1 F2] *)
      + apply is_satisfiable_is_satisfiable_or; auto.

      (* Case: [All F] *)
      + eapply is_satisfiable_is_satisfiable_add_in_branch; eauto.
        apply instantiate_imply_all. unfold isLocallyClosed; now cbn.

      (* Case: [Neg (All F)] *)
      + destruct IHj as (M & hsat0).
        destruct (is_sko_sound H M) as (interp & hinterpsko & hinterp).
        exists (ReplacementModel M interp); intro mu.
        specialize (hsat0 mu). destruct hsat0 as (B0 & hin & hinterp0).
        apply In_nth_error in hin; destruct hin as (k & ek).
        destruct (i == k); subst.
        * exists (B ,, Neg F {0 \to t}); split.
          -- unfold add_in_branch. rewrite H0.
             eapply In_replace_nth; eauto.
          -- have eB0 : B = B0.
             { unfold nth_branch_of in H0; rewrite H0 in ek; now injection ek. }
             intros [hnF | hB].
             ++ apply hnF, hinterpsko.
                eapply in_form_list_interp; eauto.
                now rewrite eB0.
             ++ rewrite eB0 in hB; now apply hB, hinterp.
        * exists B0; split.
          -- unfold add_in_branch. rewrite H0.
             eapply In_replace_nth'; eauto.
          -- now apply hinterp.
  Qed.

  Lemma isSequence_singleton :
    forall (i : nat) (T T' : ExpansionTableau) (Gamma : Con),
      [mkExpansionTableau Gamma].(i) = Some T ->
      [mkExpansionTableau Gamma].(S i) = Some T' -> T |> T'.
  Proof using Type.
    intros ????? contra. cbn in contra; rewrite nth_error_nil in contra.
    inversion contra.
  Qed.

  Lemma isSequence_cons :
    forall (i : nat) (T0 T T' : ExpansionTableau) (Gamma : Con) (seq : ExpansionSequence),
      hd_error seq = Some T0 ->
      (mkExpansionTableau Gamma |> T0) ->
      (mkExpansionTableau Gamma :: seq).(i) = Some T ->
      (mkExpansionTableau Gamma :: seq).(S i) = Some T' -> T |> T'.
  Proof using Type.
    intros ?????? e hexpand eT eT'.
    destruct i as [|j].
    - cbn in eT. rewrite nth_error_cons_succ nth_error_0 in eT'.
      rewrite e in eT'; injection eT => <-; injection eT' => <- //.
    - have h := isSequence seq0; eapply h; eauto.
  Qed.

  Lemma expand_NegNeg :
    forall (Gamma : Con) (F : Form),
      Neg (Neg F) \in Gamma ->
      mkExpansionTableau Gamma |> mkExpansionTableau (Gamma,, F).
  Proof using Type.
    intros ?? hin. apply (expansion_NegNeg (mkExpansionTableau Gamma) Gamma F 0); auto.
  Qed.

  Lemma expand_NegOr :
    forall (Gamma : Con) (F1 F2 : Form),
      Neg (Or F1 F2) \in Gamma ->
      mkExpansionTableau Gamma |> mkExpansionTableau ((Gamma,, Neg F1),, Neg F2).
  Proof using Type.
    intros ??? hin. apply (expansion_NegOr (mkExpansionTableau Gamma) Gamma F1 F2 0); auto.
  Qed.

  Lemma expand_All :
    forall (Gamma : Con) (F : Form) (x : var),
      All F \in Gamma ->
      mkExpansionTableau Gamma |> mkExpansionTableau (Gamma ,, F{0 \to Free x}).
  Proof using Type.
    intros ??? hin. apply (expansion_All (mkExpansionTableau Gamma) Gamma F 0 x); auto.
  Qed.

  Lemma expand_NegAll :
    forall (Gamma : Con) (F : Form) (t : Term) (symbs : sko_record sko),
      sko t (Neg (All F)) symbs Gamma = true -> Neg (All F) \in Gamma ->
      mkExpansionTableau Gamma |> mkExpansionTableau (Gamma ,, Neg F{0 \to t}).
  Proof using Type.
    intros ???? hsko hin. apply (expansion_NegAll (mkExpansionTableau Gamma) Gamma F 0 t symbs hsko); auto.
  Qed.

  (** An [ExpansionSequence] that has a [closed] [ExpansionTableau] as its last element
      is actually a tableau proof. *)
  Lemma hasTableau_has_ExpansionSequence :
    forall (Gamma : Con),
      (exists (sigma : Substitution var Term), hasTableau sko Gamma sigma) ->
        (exists (seq : ExpansionSequence),
            hd_error seq = Some (mkExpansionTableau Gamma) /\
              is_closed_ExpansionTableau (List.last seq [])).
  Proof.
    intros Gamma (sigma & htab); induction htab.

    (* Case: [Bot] *)
    - unshelve eexists.
      + unshelve econstructor.
        * exact [mkExpansionTableau Gamma].
        * intros ???; eapply isSequence_singleton; eauto.
      + split; cbn; auto.
        exists sigma. apply ListDef.Forall_cons.
        * now left.
        * apply ListDef.Forall_nil.

    (* Case: contradiction *)
    - unshelve eexists.
      + unshelve econstructor.
        * exact [mkExpansionTableau Gamma].
        * intros ???; eapply isSequence_singleton; eauto.
      + split; cbn; auto.
        exists sigma. apply ListDef.Forall_cons.
        * right. exists P', P; repeat split; auto.
        * apply ListDef.Forall_nil.

    (* Case: [Neg (Neg F)] *)
    - destruct IHhtab as (seq & hhd & hclosed).
      unshelve eexists.
      + unshelve econstructor.
        * exact (mkExpansionTableau Gamma :: seq).
        * intros; eapply isSequence_cons; eauto. now apply expand_NegNeg.
      + split; auto; cbn.
        have h : exists l, TableauxExpansion.seq seq = mkExpansionTableau (Gamma,, F) :: l.
        { exists (List.tl seq). rewrite -hd_error_tl_repr; split; auto. }
        destruct h as (l & el); rewrite el -el //.

    (* Case: [Neg (Or F1 F2)] *)
    - destruct IHhtab as (seq & hhd & hclosed).
      unshelve eexists.
      + unshelve econstructor.
        * exact (mkExpansionTableau Gamma :: seq).
        * intros; eapply isSequence_cons; eauto. now apply expand_NegOr.
      + split; auto; cbn.
        have h : exists l, TableauxExpansion.seq seq = mkExpansionTableau ((Gamma ,, Neg F1) ,, Neg F2) :: l.
        { exists (List.tl seq). rewrite -hd_error_tl_repr; split; auto. }
        destruct h as (l & el); rewrite el -el //.

    (* Case: [Or F1 F2] *)
    - destruct IHhtab1 as (seq1 & hhd1 & hclosed1),
          IHhtab2 as (seq2 & hhd2 & hclosed2).
      (* This is true: we can merge the two sequences as one and apply the expansion rule
         on the relevant branch that (i) comes from either [seq1] or [seq2] if it's not on
         the branch [Gamma ,, F1] & [Gamma ,, F2], or (ii) that comes from [seq1] if it's applied
         on the branch [Gamma ,, F1] and comes from [seq2] if applied on the branch [Gamma ,, F2]. *)
      admit.

    (* Case: [All F] *)
    - destruct IHhtab as (seq & hhd & hclosed).
      unshelve eexists.
      + unshelve econstructor.
        * exact (mkExpansionTableau Gamma :: seq).
        * intros; eapply isSequence_cons; eauto. now apply expand_All.
      + split; auto; cbn.
        have h : exists l, TableauxExpansion.seq seq = mkExpansionTableau (Gamma ,, F{0 \to Free x}) :: l.
        { exists (List.tl seq). rewrite -hd_error_tl_repr; split; auto. }
        destruct h as (l & el); rewrite el -el //.

    (* Case: [Neg (All F)] *)
    - destruct IHhtab as (seq & hhd & hclosed).
      unshelve eexists.
      + unshelve econstructor.
        * exact (mkExpansionTableau Gamma :: seq).
        * intros; eapply isSequence_cons; eauto. eapply expand_NegAll; eauto.
      + split; auto; cbn.
        have h : exists l, TableauxExpansion.seq seq = mkExpansionTableau (Gamma ,, Neg F{0 \to t}) :: l.
        { exists (List.tl seq). rewrite -hd_error_tl_repr; split; auto. }
        destruct h as (l & el); rewrite el -el //.
    Admitted.

  (* Actually, the above sequence needs to really be defined w.r.t. [T]..
     Or we should do both at the same time? *)
  Lemma satisfiable_ExpansionSequence_hasTableau_satisfiable :
    forall (Gamma : Con) (seq : ExpansionSequence) (sigma : Substitution var Term) (T : hasTableau sko Gamma sigma),
      hd_error seq = Some (mkExpansionTableau Gamma) ->
      is_satisfiable (ctx_to_form Gamma) ->
      exists (M : Model pred func), forall (mu : env M var),
        is_tableau_satisfiable M mu T.
  Proof.
    intros ???? eseq hsat.
    have hsatT : is_satisfiable_ExpansionTableau (mkExpansionTableau Gamma).
    { destruct hsat as (M & hsat). exists M. intro mu. exists Gamma; split; auto.
      - now left.
      - apply hsat. }
    have hsatseq := satisfiable_ExpansionSequence seq0 (mkExpansionTableau Gamma) eseq hsatT.
    clear hsat hsatT. have ehead : seq0.(0) = Some (mkExpansionTableau Gamma).
    { rewrite -eseq nth_error_0 //. } clear eseq. generalize dependent seq0.
    induction T; intros seq0 hsatseq ehead.
    - specialize (hsatseq 0 (mkExpansionTableau Gamma) ehead).
      destruct hsatseq as (M & hsat0). exists M. intro mu.
      specialize (hsat0 mu). destruct hsat0 as (B & hB & h).
      inversion hB.
      + rewrite -H in h. have hbot := in_form_list_interp i h. now cbn in hbot.
      + inversion H.
    - specialize (hsatseq 0 (mkExpansionTableau Gamma) ehead).
      destruct hsatseq as (M & hsat0). exists M. intro mu.
      specialize (hsat0 mu). destruct hsat0 as (B & hB & h).
      inversion hB.
      + rewrite -H in h. now apply satisfiable_hasTableauContr.
      + inversion H.
    - (* Good, feed the tail of [seq0] to the IHT *) admit.
    - (* Good, feed the tail of [seq0] to the IHT *) admit.
    - admit.
    - (* Good, feed the tail of [seq0] to the IHT *) admit.
    - (* Good, feed the tail of [seq0] to the IHT *) admit.
    Admitted.
End TableauxExpansion.

Section TableauxSoundness.
  Context `{set_nat : set nat} {pred func var : Atom} (sko : Skolemization_ pred func var).

  Let Con := Con_ pred func var.
  Let Form := Form_ pred func var.
  Let Term := Term_ func var.

  (** We start by showing that if the root formula of a tableau is satisfiable, then this
      tableau is also satisfiable.

      Note that [Gamma] must be a closed context. *)
  Lemma hasTableau_satisfiable :
    forall {Gamma : Con} {sigma : Substitution var Term} (T : hasTableau sko Gamma sigma)
      (M : Model pred func),
      (forall  (mu : env M var), [[ M # [] # mu '|= ctx_to_form Gamma ]]) ->
      exists (M' : Model pred func), forall (mu' : env M' var),
        is_tableau_satisfiable M' mu' T.
  Proof using Type.
    intros ???? hinterp.

    have htab : exists (sigma : Substitution var Term), hasTableau sko Gamma sigma by exists sigma.
    apply hasTableau_has_ExpansionSequence in htab.
    destruct htab as (seq & e & _).
    have h0 : is_satisfiable (ctx_to_form Gamma) by now exists M.
    eapply satisfiable_ExpansionSequence_hasTableau_satisfiable; eauto.
  Qed.

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
      hasTableau sko (Gamma ,, Neg F) sigma -> Gamma |= F.
  Proof using Type.
    intros ??? hclosedGamma htab.
    rewrite models_iff. intros M. left. intro hsat.
    have hsat' : forall (mu : env M var),
        interpret_form_ M [] mu (ls_to_form (Neg F :: Gamma)).
    { intro mu; change [[ M # [] # mu '|= ls_to_form (Neg F :: Gamma) ]].
      rewrite (isClosed_interp_form_env_eq _ _ _ _ (empty_env M var)); auto.
      rewrite isClosedList_isClosedFormList //. }
    eapply hasTableau_satisfiable with (T := htab) in hsat'.
    destruct hsat' as (M' & hsat'). specialize (hsat' (subst_to_env M' sigma)).
    eapply hasTableau_not_satisfiable; eauto.
  Qed.
End TableauxSoundness.

Module ConcreteProofInstances.
  Export ConcreteSkolemizationInstances.

  Definition Con := Con_ string string string.
End ConcreteProofInstances.
