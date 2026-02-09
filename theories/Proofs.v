(** * Proofs: definition of free-variable tableaux proofs. *)

(** In this file, we define the free-variable tableau method as an "expansion" method,
    i.e., we define a [Tableau] as a proof tree, and a [TableauProof] is a [Sequence] of
    [Tableau]x such that an [ExpansionRule] is applied between every [Tableau] of the
    [Sequence]. We define what it means for a [TableauProof] to be closed, and show that,
    list of formulas [Neg F :: Gamma], if this context has a tableau proof, then [Gamma |= F]. *)

From Stdlib Require Import Classical.
From Stdlib Require Import Lia.

From Tableaux Require Import Semantics.
From Tableaux Require Import Skolemization.
From Tableaux Require Import Syntax.

Notation "x \in l" := (List.In x l) (at level 30).

(** ** Tableaux *)
Section Tableaux.
  Context `{set_nat : set nat} {pred func var : Atom} (sko : Skolemization_ pred func var).

  Let Form := Form_ pred func var.

  Inductive TableauTree : Type :=
  | Leaf
  | Node (T1 : TableauTree) (Gamma : list Form) (T2 : TableauTree) : TableauTree.

  Inductive BranchingStep : Type := Left | Right.

  #[global] Instance EqDec_BranchingStep : EqDec BranchingStep.
  Proof using Type.
    intros [] [].
    - now left.
    - now right.
    - now right.
    - now left.
  Qed.

  (** A [Branch] of a tableau is a succession of [BranchingStep]s. *)
  Definition Branch := list BranchingStep.

  (** A [Branch] [is_branch_of] a [TableauTree] whenever the list of branching steps describes
      a path from the root of the [TableauTree] to a node without children. *)
  Inductive is_branch_of : Branch -> TableauTree -> Prop :=
  | is_branch_of_nil : forall (Gamma : list Form), is_branch_of [] (Node Leaf Gamma Leaf)
  | is_branch_of_left :
    forall (T1 T2 : TableauTree) (Gamma : list Form) (B : Branch),
      is_branch_of B T1 -> is_branch_of (Left :: B) (Node T1 Gamma T2)
  | is_branch_of_right :
    forall (T1 T2 : TableauTree) (Gamma : list Form) (B : Branch),
      is_branch_of B T2 -> is_branch_of (Right :: B) (Node T1 Gamma T2).

  (** A [Form]ula [F] [is_on_branch] [B] if it appears in any one of the nodes along [B]. *)
  Inductive is_on_branch (F : Form) : Branch -> TableauTree -> Prop :=
  | is_on_branch_node :
    forall (T1 T2 : TableauTree) (Gamma : list Form) (B : Branch),
      F \in Gamma -> is_on_branch F B (Node T1 Gamma T2)
  | is_on_branch_left :
    forall (T1 T2 : TableauTree) (Gamma : list Form) (B : Branch),
      is_on_branch F B T1 -> is_on_branch F (Left :: B) (Node T1 Gamma T2)
  | is_on_branch_right :
    forall (T1 T2 : TableauTree) (Gamma : list Form) (B : Branch),
      is_on_branch F B T2 -> is_on_branch F (Right :: B) (Node T1 Gamma T2).

  Definition mkOptionalNode (Gamma : option (list Form)) :=
    match Gamma with
    | Some Gamma => Node Leaf Gamma Leaf
    | None => Leaf
    end.

  Fixpoint expand_tableau_branch__aux (left_forms right_forms : option (list Form))
    (B : Branch) (T : TableauTree) : option TableauTree :=
    match B with
    | [] =>
        match T with
        | Node Leaf Gamma Leaf => Some (Node (mkOptionalNode left_forms) Gamma (mkOptionalNode right_forms))
        | _ => None
        end
    | b :: B =>
        match T with
        | Leaf => None
        | Node T1 Gamma T2 =>
            match b with
            | Left => expand_tableau_branch__aux left_forms right_forms B T1 >>=
                       (fun T1 => Some (Node T1 Gamma T2))
            | Right => expand_tableau_branch__aux left_forms right_forms B T2 >>=
                        (fun T2 => Some (Node T1 Gamma T2))
            end
        end
    end.

  (** The [context] of a branch is the list of all the formulas of a branch. *)
  Fixpoint get_context (B : Branch) (T : TableauTree) : list Form :=
    match T with
    | Leaf => []
    | Node T1 Gamma T2 => Gamma ++ (match B with
                           | [] => []
                           | Left :: B => get_context B T1
                           | Right :: B => get_context B T2
                           end)%list
    end.

  (** Actually, a [Tableau_] also keeps in memory the Skolem symbols introduced. *)
  Record Tableau_ :=
    { tree :> TableauTree
    ; symbols : sko_record sko }.

  Definition expand_tableau_branch (left_forms right_forms : option (list Form))
    (B : Branch) (T : Tableau_) : option Tableau_ :=
    expand_tableau_branch__aux left_forms right_forms B T >>=
      (fun tree => Some {| tree := tree; symbols := symbols T |}).

  (** A [Sequence] is a list of tableaux. *)
  Definition Sequence := list Tableau_.

  (** A [Tableau_] is said closed under a substitution if every branch has a contradiction. *)
  Definition is_tableau_closed (T : Tableau_) (sigma : Substitution var (Term_ func var)) : Prop :=
    forall (B : Branch),
      is_branch_of B T ->
      Bot \in get_context B T \/
        (exists (F G : Form),
            F \in get_context B T /\ G \in get_context B T /\
              F@[sigma] = Neg G@[sigma]).

  (** A [Branch] of a [Tableau_] is satisfied if its context is satisfied. *)
  Definition exists_satisfied_branch (M : Model pred func) (mu : env M var) (T : Tableau_) : Prop :=
    exists (B : Branch),
      is_branch_of B T /\ [[ M # [] # mu '|= ls_to_form (get_context B T) ]].

  (** A [Tableau_] is said satisfiable if there exists a model such that for every free-variable
      environment, there is a branch that is satisfied. *)
  Definition is_tableau_satisfiable (T : Tableau_) :=
    exists (M : Model pred func), forall (mu : env M var), exists_satisfied_branch M mu T.

  Definition mkTableau (Gamma : list Form) : Tableau_ :=
    {| tree := Node Leaf Gamma Leaf
    ;  symbols := empty_record |}.

  Definition mkLeaf : Tableau_ := {| tree := Leaf; symbols := empty_record |}.

  Lemma is_branch_of_extend_left :
    forall (T T' : TableauTree) (B : Branch) (l : list Form) (l' : option (list Form)),
      is_branch_of B T -> expand_tableau_branch__aux (Some l) l' B T = Some T' ->
      is_branch_of (B ++ [Left])%list T'.
  Proof using Type.
    intros ????? hbranchof e. generalize dependent T'; induction hbranchof; intros T' e; cbn in *.
    - injection e => <-; cbn. apply is_branch_of_left; constructor.
    - destruct (expand_tableau_branch__aux (Some l) l' B T1) eqn:eT'.
      + injection e => <-; cbn. apply is_branch_of_left; auto.
      + inversion e.
    - destruct (expand_tableau_branch__aux (Some l) l' B T2) eqn:eT'.
      + injection e => <-; cbn. apply is_branch_of_right; auto.
      + inversion e.
  Qed.

  Lemma is_branch_of_extend_right :
    forall (T T' : TableauTree) (B : Branch) (l : option (list Form)) (l' : list Form),
      is_branch_of B T -> expand_tableau_branch__aux l (Some l') B T = Some T' ->
      is_branch_of (B ++ [Right])%list T'.
  Proof using Type.
    intros ????? hbranchof e. generalize dependent T'; induction hbranchof; intros T' e; cbn in *.
    - injection e => <-; cbn. apply is_branch_of_right; constructor.
    - destruct (expand_tableau_branch__aux l (Some l') B T1) eqn:eT'.
      + injection e => <-; cbn. apply is_branch_of_left; auto.
      + inversion e.
    - destruct (expand_tableau_branch__aux l (Some l') B T2) eqn:eT'.
      + injection e => <-; cbn. apply is_branch_of_right; auto.
      + inversion e.
  Qed.

  Lemma is_branch_of_extend_None :
    forall (T T' : TableauTree) (B : Branch),
      is_branch_of B T -> expand_tableau_branch__aux None None B T = Some T' ->
      is_branch_of B T'.
  Proof using Type.
    intros ??? hbranchof e. generalize dependent T'; induction hbranchof; intros T' e; cbn in *.
    - injection e => <-; cbn. apply is_branch_of_nil.
    - destruct (expand_tableau_branch__aux None None B T1) eqn:eT'.
      + injection e => <-; cbn. apply is_branch_of_left; auto.
      + inversion e.
    - destruct (expand_tableau_branch__aux None None B T2) eqn:eT'.
      + injection e => <-; cbn. apply is_branch_of_right; auto.
      + inversion e.
  Qed.

  Lemma get_context_extend_left :
    forall (T T' : TableauTree) (B : Branch) (Gamma l : list Form) (l' : option (list Form)),
      is_branch_of B T -> expand_tableau_branch__aux (Some l) l' B T = Some T' ->
      get_context B T = Gamma -> get_context (B ++ [Left])%list T' = (Gamma ++ l)%list.
  Proof using Type.
    intro T. induction T; intros ????? hbranchof e eT; destruct B.
    - inversion e.
    - inversion e.
    - inversion hbranchof; subst. cbn in e.
      injection e => <-; cbn. now rewrite !app_nil_r.
    - destruct b; cbn.
      + inversion hbranchof; subst.
        cbn in e. destruct (expand_tableau_branch__aux (Some l) l' B T1) eqn:eT1.
        * injection e => <-; cbn in *. erewrite IHT1; eauto.
          rewrite app_assoc //.
        * inversion e.
      + inversion hbranchof; subst.
        cbn in e. destruct (expand_tableau_branch__aux (Some l) l' B T2) eqn:eT2.
        * injection e => <-; cbn in *. erewrite IHT2; eauto.
          rewrite app_assoc //.
        * inversion e.
  Qed.

  Lemma get_context_extend_right :
    forall (T T' : TableauTree) (B : Branch) (Gamma l' : list Form) (l : option (list Form)),
      is_branch_of B T -> expand_tableau_branch__aux l (Some l') B T = Some T' ->
      get_context B T = Gamma -> get_context (B ++ [Right])%list T' = (Gamma ++ l')%list.
  Proof using Type.
    intro T. induction T; intros ????? hbranchof e eT; destruct B.
    - inversion e.
    - inversion e.
    - inversion hbranchof; subst. cbn in e.
      injection e => <-; cbn. now rewrite !app_nil_r.
    - destruct b; cbn.
      + inversion hbranchof; subst.
        cbn in e. destruct (expand_tableau_branch__aux l (Some l') B T1) eqn:eT1.
        * injection e => <-; cbn in *. erewrite IHT1; eauto.
          rewrite app_assoc //.
        * inversion e.
      + inversion hbranchof; subst.
        cbn in e. destruct (expand_tableau_branch__aux l (Some l') B T2) eqn:eT2.
        * injection e => <-; cbn in *. erewrite IHT2; eauto.
          rewrite app_assoc //.
        * inversion e.
  Qed.

  (** An optional list of formulas is satisfied either if it is none or if the list is
      satisfied. *)
  Definition is_optional_satisfied
    (M : Model pred func) (mu : env M var) (l : option (list Form)) :=
    match l with
    | None => False
    | Some l => [[ M # [] # mu '|= ls_to_form l ]]
    end.

  (** If a satisfiable tableau is extended with lists of formulas of which one of them is also
      satisfied by the same model, then the extended tableau is also satisfiable. *)
  Lemma is_satisfiable_extend :
    forall (M : Model pred func) (mu : env M var) (T T' : Tableau_) (B : Branch)
      (l l' : option (list Form)),
      is_branch_of B T -> expand_tableau_branch l l' B T = Some T' ->
      is_optional_satisfied M mu l \/ is_optional_satisfied M mu l' ->
      exists_satisfied_branch M mu T -> exists_satisfied_branch M mu T'.
  Proof.
    intros ?? [T symbs] [T' symbs'] ??? hbranchof e [hsatl | hsatl'] (B & hbranchB & hsatB);
      cbn in e.

    (* Case: the extension with the formulas on the left is satisfied. *)
    - destruct (B == B0).

      (* Case: the branch that was satisfied is, in fact, [B0]. *)
      + destruct l.
        * exists (List.app B [Left]); split; cbn.
          -- rewrite e0. destruct (expand_tableau_branch__aux (Some l) l' B0 T) eqn:eT.
             ++ eapply is_branch_of_extend_left; eauto.
                injection e => ? <-; eauto.
             ++ inversion e.
          -- rewrite -e0 in e. destruct (expand_tableau_branch__aux (Some l) l' B T) eqn:eT.
             ++ injection e => _ eT'. rewrite eT' in eT. erewrite get_context_extend_left; eauto.
                cbn. unfold interpret; rewrite (ls_to_form_app (get_context B T) l M [] mu).
                cbn. intros [hnB | hl]; auto.
             ++ inversion e.
        * now cbn in hsatl.

      (* Case: the branch that was satisfied is not [B0]. *)
      + exists B; split; admit.

    (* Case: the extension with the formulas on the right is satisfied. *)
    - destruct (B == B0).

      (* Case: the branch that was satisfied is, in fact, [B0]. *)
      + destruct l'.
        * exists (B ++ [Right])%list; split; cbn.
          -- rewrite e0. destruct (expand_tableau_branch__aux l (Some l0) B0 T) eqn:eT.
             ++ eapply is_branch_of_extend_right; eauto.
                injection e => ? <-; eauto.
             ++ inversion e.
          -- rewrite -e0 in e. destruct (expand_tableau_branch__aux l (Some l0) B T) eqn:eT.
             ++ injection e => _ eT'; rewrite eT' in eT.
                erewrite get_context_extend_right; eauto.
                cbn; unfold interpret. rewrite (ls_to_form_app (get_context B T) l0 M [] mu).
                cbn. intros [hnB | hl0]; auto.
             ++ inversion e.

        * inversion hsatl'.

      (* Case: the branch that was satisfied is not [B0]. *)
      + exists B; split; admit.
  Admitted.
End Tableaux.

Arguments tree {_ _ _ _}.
Arguments symbols {_ _ _ _}.
Arguments is_tableau_closed {_ _ _ _ _} _ _.
Arguments exists_satisfied_branch {_ _ _ _} _ _ _.

(** ** Expansion rules *)

(** We denote [T |> T'] when a [Tableau] [T] can be expanded to a tableau [T']. *)
Reserved Notation "T |> T'" (at level 30, right associativity).
Section ExpansionRules.
  Context `{set_nat : set nat} {pred func var : Atom} (sko : Skolemization_ pred func var).

  Let Term := Term_ func var.
  Let Form := Form_ pred func var.
  Let Tableau := Tableau_ sko.

  (** By convention, we expand a tableau on the left side for unary rules. *)
  Inductive ExpansionStep : Tableau -> Tableau -> Prop :=
  | expansion_NegNeg :
    forall (T T' : Tableau) (B : Branch) (F : Form),
      is_branch_of B T -> is_on_branch (Neg (Neg F)) B T ->
      expand_tableau_branch sko (Some [F]) None B T = Some T' -> T |> T'

  | expansion_NegOr :
    forall (T T' : Tableau) (B : Branch) (F1 F2 : Form),
      is_branch_of B T -> is_on_branch (Neg (Or F1 F2)) B T ->
      expand_tableau_branch sko (Some [Neg F1 ; Neg F2]) None B T = Some T' -> T |> T'

  | expansion_Or :
    forall (T T' : Tableau) (B : Branch) (F1 F2 : Form),
      is_branch_of B T -> is_on_branch (Or F1 F2) B T ->
      expand_tableau_branch sko (Some [F1]) (Some [F2]) B T = Some T' -> T |> T'

  | expansion_All :
    forall (T T' : Tableau) (B : Branch) (F : Form) (x : var),
      is_branch_of B T -> is_on_branch (All F) B T ->
      expand_tableau_branch sko (Some [F{0 \to Free x}]) None B T = Some T' -> T |> T'

  | expansion_NegAll :
    forall (T T' : Tableau) (B : Branch) (F : Form) (t : Term)
      (hsko : sko t (Neg (All F)) (symbols T) (get_context B T) = true),
      is_branch_of B T -> is_on_branch (Neg (All F)) B T ->
      expand_tableau_branch__aux (Some [F{0 \to t}]) None B T = Some (tree T') ->
      symbols T' = add_symbol (symbol sko hsko) (Neg (All F)) (symbols T) ->
      T |> T'
  where "T |> T'" := (ExpansionStep T T').

  (** A [Sequence] is an [ExpansionSequence] if every neighbouring [Tableau] are related
      by an [ExpansionStep]. *)
  Definition is_expansion_sequence (s : Sequence sko) : Prop :=
    forall (i : nat) (T T' : Tableau),
      s.(i) = Some T -> s.(S i) = Some T' -> T |> T'.

  (** A sequence is a tableau proof if there it is an expansion sequence s.t. the first
      tableau of the sequence has a simple node labelled by this list of formulas and the
      last is closed under a substitution [sigma]. *)
  Definition is_tableau_proof (Gamma : list Form) (sigma : Substitution var Term) (s : Sequence sko) : Prop :=
    is_expansion_sequence s /\
      hd_error s = Some (mkTableau sko Gamma) /\
      is_tableau_closed (last s (mkLeaf sko)) sigma.

  (** A list of formulas have a tableau if there exists a sequence that is a tableau proof *)
  Definition hasTableau (Gamma : list Form) (sigma : Substitution var Term) : Prop :=
    exists (s : Sequence sko), is_tableau_proof Gamma sigma s.
End ExpansionRules.

Arguments ExpansionStep {_ _ _ _} _ _.
Notation "T |> T'" := (ExpansionStep T T').

(** ** Soundness *)

(** In this section, we show that this definition of tableaux is sound, i.e., if list of formulas
    [Neg F :: Gamma] has a tableau, then [Gamma |= F]. *)
Section Soundness.
  Context `{set_nat : set nat} {pred func var : Atom} (sko : Skolemization_ pred func var).

  Let Term := Term_ func var.
  Let Form := Form_ pred func var.
  Let Tableau := Tableau_ sko.

  (** First, we show that the last tableau of a proof cannot be satisfiable. *)
  Lemma hasTableau_not_satisfiable :
    forall (M : Model pred func) (Gamma : list Form) (sigma : Substitution var Term) (s : Sequence sko),
      is_tableau_proof sko Gamma sigma s ->
      (forall (B : Branch),
          is_branch_of B (last s (mkLeaf sko)) ->
          ~ [[ M # [] # subst_to_env M sigma '|= ls_to_form (get_context B (last s (mkLeaf sko))) ]]).
  Proof using Type.
    intros ???? (_ & _ & hclosed) ? hB hsat.
    destruct (hclosed B hB) as [ htrivial | [ F [ G  [ hinF [ hinG e ] ] ] ] ].
    - have [] := in_form_list_interp htrivial hsat.
    - have hF := in_form_list_interp hinF hsat.
      have hG := in_form_list_interp hinG hsat.
      rewrite -!subst_commutes_with_env_forms in hF, hG.
      rewrite e in hF. now apply hF.
  Qed.

  (** Then, we show that every expansion sequence starting from a satisfiable tableau is
      satisfiable. We even show that there exists one model that satisfies every element
      of the sequence. *)

  (** We start by showing that applying an [ExpansionStep] on a satisfiable tableau keeps
      satisfiability. *)
  Lemma subject_reduction :
    forall (T T' : Tableau),
      is_tableau_satisfiable sko T -> (T |> T') ->
      is_tableau_satisfiable sko T'.
  Proof using set_nat.
    intros T T' hsat hred. destruct hred as
      [ T T' B F hbranchof hcontains e |
        T T' B F1 F2 hbranchof hcontains e |
        T T' B F1 F2 hbranchof hcontains e |
        T T' B F x hbranchof hcontains e |
        T T' B F t hsko hbranchof hcontains etree esymbs ].

    (* Case: [Neg (Neg F)] *)
    - destruct hsat as (M & hsat). exists M; intro mu. specialize (hsat mu).
      eapply is_satisfiable_extend; eauto. left.
      intros [hnF | contra]; firstorder.
      (* easy *)

eapply is_satisfiable_is_satisfiable_add_in_branch; eauto.
      apply equiv_imply. symmetry; apply neg_neg_equiv.

    (* Case: [Neg (Or F1 F2)] *)
    - eapply is_satisfiable_is_satisfiable_add_in_branch with
        (F := Neg (Or F1 F2)) (T := add_in_branch T i (Neg F1)).
      + eapply add_in_branch_get; eauto.
      + eapply is_satisfiable_is_satisfiable_add_in_branch; eauto.
        intros M sigma hinterp hF1. apply hinterp. now left.
      + now apply branch_contains_add.
      + intros M sigma hinterp hF2. apply hinterp. now right.

    (* Case: [Or F1 F2] *)
    - apply is_satisfiable_is_satisfiable_or; auto.

    (* Case: [All F] *)
    - eapply is_satisfiable_is_satisfiable_add_in_branch; eauto.
      apply instantiate_imply_all. unfold isLocallyClosed; now cbn.

    (* Case: [Neg (All F)] *)
    - destruct hsat as (M & hsat0).
      destruct (is_sko_sound H M) as (interp & hinterpsko & hinterp).
      exists (ReplacementModel M interp); intro mu.
      specialize (hsat0 mu). destruct hsat0 as (B0 & hin & hinterp0).
      apply In_nth_error in hin; destruct hin as (k & ek).
      destruct (i == k); subst.
      + exists (B ,, Neg F {0 \to t}); split.
        * unfold add_in_branch. rewrite H0.
          eapply In_replace_nth; eauto.
        * have eB0 : B = B0.
          { unfold nth_branch_of in H0; rewrite H0 in ek; now injection ek. }
          intros [hnF | hB].
          -- apply hnF, hinterpsko.
             eapply in_form_list_interp; eauto.
             now rewrite eB0.
          -- rewrite eB0 in hB; now apply hB, hinterp.
      + exists B0; split.
        * unfold add_in_branch. rewrite H0.
          eapply In_replace_nth'; eauto.
        * now apply hinterp.
  Qed.

End Soundness.

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
    : Con -> sko_record -> Substitution var Term -> Type :=

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
  Scheme hasTableau__ind := Induction for hasTableau_ Sort Prop.
  Scheme hasTableau__rect := Induction for hasTableau_ Sort Type.
  Set Elimination Schemes.

  Definition hasTableau (Gamma : Con) (sigma : Substitution var Term) : Type :=
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

Reserved Notation "T |> T'" (at level 90, right associativity).
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

    Definition has_satisfiable_branch
      (T : ExpansionTableau) (M : Model pred func) (mu : env M var) :=
      exists (B : Branch), List.In B T /\ [[ M # [] # mu '|= ctx_to_form (branch_to_con B) ]].

    (** An [ExpansionTableau] is said [satisfiable] if one of its branches is satisfiable. *)
    Definition is_satisfiable_ExpansionTableau (T : ExpansionTableau) : Prop :=
      exists (M : Model pred func), forall (mu : env M var), has_satisfiable_branch T M mu.

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

    Lemma add_in_branch_get' :
      forall (T : ExpansionTableau) (B : Branch) (i j : nat) (F : Form),
        nth_branch_of T i = Some B -> i <> j ->
        nth_branch_of (add_in_branch T j F) i = Some B.
    Proof using Type.
      intros ????? e ne; unfold nth_branch_of in e |- *.
      unfold add_in_branch, nth_branch_of.
      destruct (T.(j)) eqn:ej; auto.
      apply get_replace_nth'; auto.
    Qed.

    Lemma add_in_branch_get_inv' :
      forall (T : ExpansionTableau) (B : Branch) (i j : nat) (F : Form),
        nth_branch_of (add_in_branch T j F) i = Some B -> i <> j ->
         nth_branch_of T i = Some B.
    Proof using Type.
      intros ????? e ne; unfold nth_branch_of in e |- *.
      unfold add_in_branch, nth_branch_of in e.
      destruct (T.(j)) eqn:ej; auto.
      eapply get_replace_nth_inv'; eauto.
    Qed.

    Lemma add_branch_get :
      forall (T : ExpansionTableau) (B B' : Branch) (i : nat) (F : Form),
        nth_branch_of T i = Some B ->
        nth_branch_of (add_branch T F B') (S i) = Some B.
    Proof using Type.
      intros ????? e. unfold nth_branch_of in e |- *.
      unfold add_branch; now cbn.
    Qed.

    (* Lemma add_branch_get_inv' : *)
    (*   forall (T : ExpansionTableau) (B B' : Branch) (i j : nat) (F : Form), *)
    (*     nth_branch_of (add_branch T F B') i = Some B -> j <> Nat.pred i -> *)
    (*     nth_branch_of T i = Some B. *)

    Lemma branch_contains_add :
      forall (B : Branch) (F G : Form),
        branch_contains B F -> branch_contains (B ,, G) F.
    Proof using Type. intros. now right. Qed.

    Definition swap (i j : nat) (T : ExpansionTableau) : ExpansionTableau :=
      match nth_branch_of T i, nth_branch_of T j with
      | Some Bi, Some Bj =>
          replace_nth i Bj (replace_nth j Bi T)
      | _, _ => T
      end.

    Lemma in_tableau_in_swap :
      forall (T : ExpansionTableau) (B : Branch) (i j : nat),
        List.In B T <-> List.In B (swap i j T).
    Proof using Type.
      intros ????. split; intro hin.
      - unfold swap, nth_branch_of.
        destruct (T.(i)) eqn:ei, (T.(j)) eqn:ej; cbn in *; auto.
        destruct (c0 == B).
        + destruct (replace_nth_Some i j c c T ei).
          subst; eapply In_replace_nth; eauto.
        + destruct (c == B); subst.
          * destruct (i == j); subst.
            -- rewrite ei in ej; congruence.
            -- rewrite replace_nth_replace_nth; auto.
               destruct (replace_nth_Some j i c0 c0 T ej).
               subst; eapply In_replace_nth; eauto.
          * apply In_nth_error in hin. destruct hin as (k & ek).
            have h0 : k <> i.
            { intro e. rewrite -e ek in ei. congruence. }
            have h1 : k <> j.
            { intro e. rewrite -e ek in ej. congruence. }
            apply In_replace_nth' with (n := k); auto.
            apply get_replace_nth'; auto.
      - unfold swap, nth_branch_of in hin.
        destruct (T.(i)) eqn:ei, (T.(j)) eqn:ej; cbn in *; auto.
        destruct (B == c0).
        + rewrite -e in ej. eapply nth_error_In; eauto.
        + destruct (B == c).
          * rewrite -e in ei. eapply nth_error_In; eauto.
          * do 2 (apply In_In_replace_nth in hin; auto).
    Qed.
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

  (** Expanding an [ExpansionTableau] keeps satisfiability. *)
  Lemma satisfiable_Expansion :
    forall (T T' : ExpansionTableau),
      is_satisfiable_ExpansionTableau T -> (T |> T') ->
      is_satisfiable_ExpansionTableau T'.
  Proof using set_nat.
    intros T T' hsat hred. induction hred.

    (* Case: [Neg (Neg F)] *)
    - eapply is_satisfiable_is_satisfiable_add_in_branch; eauto.
      apply equiv_imply. symmetry; apply neg_neg_equiv.

    (* Case: [Neg (Or F1 F2)] *)
    - eapply is_satisfiable_is_satisfiable_add_in_branch with
        (F := Neg (Or F1 F2)) (T := add_in_branch T i (Neg F1)).
      + eapply add_in_branch_get; eauto.
      + eapply is_satisfiable_is_satisfiable_add_in_branch; eauto.
        intros M sigma hinterp hF1. apply hinterp. now left.
      + now apply branch_contains_add.
      + intros M sigma hinterp hF2. apply hinterp. now right.

    (* Case: [Or F1 F2] *)
    - apply is_satisfiable_is_satisfiable_or; auto.

    (* Case: [All F] *)
    - eapply is_satisfiable_is_satisfiable_add_in_branch; eauto.
      apply instantiate_imply_all. unfold isLocallyClosed; now cbn.

    (* Case: [Neg (All F)] *)
    - destruct hsat as (M & hsat0).
      destruct (is_sko_sound H M) as (interp & hinterpsko & hinterp).
      exists (ReplacementModel M interp); intro mu.
      specialize (hsat0 mu). destruct hsat0 as (B0 & hin & hinterp0).
      apply In_nth_error in hin; destruct hin as (k & ek).
      destruct (i == k); subst.
      + exists (B ,, Neg F {0 \to t}); split.
        * unfold add_in_branch. rewrite H0.
          eapply In_replace_nth; eauto.
        * have eB0 : B = B0.
          { unfold nth_branch_of in H0; rewrite H0 in ek; now injection ek. }
          intros [hnF | hB].
          -- apply hnF, hinterpsko.
             eapply in_form_list_interp; eauto.
             now rewrite eB0.
          -- rewrite eB0 in hB; now apply hB, hinterp.
      + exists B0; split.
        * unfold add_in_branch. rewrite H0.
          eapply In_replace_nth'; eauto.
        * now apply hinterp.
  Qed.

  (** Actually, two tableaux linked via an expansion are equisatisfiable. Even more important:
      the model of the second tableau is also a model of the first tableau. *)
  Lemma satisfiable_rev_Expansion :
    forall (T T' : ExpansionTableau) (M : Model pred func) (mu : env M var),
      has_satisfiable_branch T' M mu -> (T |> T') ->
      has_satisfiable_branch T M mu.
  Proof using Type.
    intros ???? (B & hin & hinterp) hred; destruct hred.

    (* TODO: factorize boilerplate code *)

    (* Case: [Neg [Neg F]] *)
    - destruct (In_nth_error _ _ hin) as (k & ek).
      destruct (i == k).
      + rewrite e in ek, H.
        change (nth_branch_of (add_in_branch T k F) k = Some B) in ek.
        erewrite add_in_branch_get in ek; eauto.
        exists B0; split.
        * eapply nth_error_In; eauto.
        * injection ek => ek'. rewrite -ek' in hinterp; cbn in hinterp |- *.
          apply NNPP => save; apply hinterp; now right.
      + exists B; split; auto.
        eapply add_in_branch_get_inv' in ek; eauto.
        now apply nth_error_In in ek.

    (* Case: [Neg [Or F1 F2]] *)
    - destruct (In_nth_error _ _ hin) as (k & ek).
      destruct (i == k).
      + rewrite e in ek, H.
        change (nth_branch_of (add_in_branch (add_in_branch T k (Neg F1)) k (Neg F2)) k = Some B)
          in ek.
        unshelve erewrite add_in_branch_get in ek.
        * exact (B0 ,, Neg F1).
        * exists B0; split.
          -- eapply nth_error_In; eauto.
          -- injection ek => ek'. rewrite -ek' in hinterp; cbn in hinterp |- *.
             apply NNPP => save; apply hinterp. right; intro h; apply h; now right.
        * now apply add_in_branch_get.
      + exists B; split; auto.
        do 2 eapply add_in_branch_get_inv' in ek; eauto.
        now apply nth_error_In in ek.

    (* Case: [Or F1 F2] *)
    - destruct (In_nth_error _ _ hin) as (k & ek).
      destruct (i == Nat.pred k).
      + destruct k.
        * cbn in ek. exists B0; split.
          -- eapply nth_error_In; eauto.
          -- injection ek => ek'; rewrite -ek' in hinterp; cbn in hinterp |- *.
             apply NNPP => save; apply hinterp; now right.
        * cbn in e; subst.
          change (nth_branch_of (add_branch (add_in_branch T k F1) F2 B0) (S k) = Some B)
            in ek.
          unshelve erewrite add_branch_get in ek.
          -- exact (B0 ,, F1).
          -- exists B0; split.
             ++ eapply nth_error_In; eauto.
             ++ injection ek => ek'; rewrite -ek' in hinterp; cbn in hinterp |- *.
                apply NNPP => save; apply hinterp; now right.
          -- erewrite add_in_branch_get; eauto.
      + destruct k.
        * exists B0; split.
          ++ eapply nth_error_In; eauto.
          ++ injection ek => ek'; rewrite -ek' in hinterp; cbn in hinterp |- *.
             apply NNPP => save; apply hinterp; now right.
        * cbn in n, ek. exists B; split; auto.
          eapply add_in_branch_get_inv' in ek; eauto.
          now apply nth_error_In in ek.

    (* Case: [All F] *)
    - destruct (In_nth_error _ _ hin) as (k & ek).
      destruct (i == k).
      + rewrite e in ek, H.
        change (nth_branch_of (add_in_branch T k (F {0 \to Free x})) k = Some B) in ek.
        erewrite add_in_branch_get in ek; eauto.
        exists B0; split.
        * eapply nth_error_In; eauto.
        * injection ek => ek'. rewrite -ek' in hinterp; cbn in hinterp |- *.
          apply NNPP => save; apply hinterp; now right.
      + exists B; split; auto.
        eapply add_in_branch_get_inv' in ek; eauto.
        now apply nth_error_In in ek.

    (* Case: [Neg (All F)] *)
    - destruct (In_nth_error _ _ hin) as (k & ek).
      destruct (i == k).
      + rewrite e in ek, H.
        change (nth_branch_of (add_in_branch T k (Neg F {0 \to t})) k = Some B) in ek.
        rewrite (add_in_branch_get _ B0) in ek; auto.
        * now rewrite -e.
        * exists B0; split.
          --  eapply nth_error_In; eauto.
          -- injection ek => ek'. rewrite -ek' in hinterp; cbn in hinterp |- *.
             apply NNPP => save; apply hinterp; now right.
      + exists B; split; auto.
        eapply add_in_branch_get_inv' in ek; eauto.
        now apply nth_error_In in ek.
  Qed.

  Lemma isSequence_nil :
    forall (i : nat) (T T' : ExpansionTableau),
      [].(i) = Some T ->
      [].(S i) = Some T' -> T |> T'.
  Proof using Type. intros ??? contra. rewrite nth_error_nil in contra; inversion contra. Qed.

  Lemma isSequence_tail :
    forall (s : ExpansionSequence) (T0 : ExpansionTableau) (s' : list ExpansionTableau)
      (i : nat) (T T' : ExpansionTableau),
      seq s = T0 :: s' -> s'.(i) = Some T -> s'.(S i) = Some T' -> T |> T'.
  Proof using Type.
    intros ?????? es eT eT'. apply (isSequence s (S i)); rewrite !es; cbn; auto.
  Qed.

  Lemma isSequence_singleton :
    forall (T0 : ExpansionTableau) (i : nat) (T T' : ExpansionTableau) (Gamma : Con),
      [T0].(i) = Some T ->
      [T0].(S i) = Some T' -> T |> T'.
  Proof using Type.
    intros ?????? contra. cbn in contra; rewrite nth_error_nil in contra.
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
    intros ???? hsko hin. apply (expansion_NegAll (mkExpansionTableau Gamma) Gamma F 0 t symbs hsko);
      auto.
  Qed.

  (** Every [ExpansionTableau] of a sequence is satisfiable as long as its first tableau is
      satisfiable. *)
  Lemma satisfiable_ExpansionSequence :
    forall (seq : ExpansionSequence) (T : ExpansionTableau),
      hd_error seq = Some T -> is_satisfiable_ExpansionTableau T ->
      forall (i : nat) (T' : ExpansionTableau),
        seq.(i) = Some T' ->
        is_satisfiable_ExpansionTableau T'.
  Proof using set_nat.
    intros seq T e hsat i. induction i as [|i' IHi']; intros T' e'.
    - rewrite nth_error_0 e in e'. injection e' => <- //.
    - have [T0 eT0] : exists (T0 : ExpansionTableau), seq.(i') = Some T0.
      { have hlt := nth_error_Some' _ _ _ e'.
        exists (nth i' seq T). apply nth_error_nth'. lia. }
      specialize (IHi' T0 eT0). eapply satisfiable_Expansion; eauto.
      apply (isSequence seq i' T0 T'); auto.
  Qed.

  (** In fact, there exists a model that satisfies every tableau of an [ExpansionSequence]:
      the model of the last [ExpansionTableau] of the sequence. *)
  Lemma model_ExpansionSequence :
    forall (seq : ExpansionSequence) (T : ExpansionTableau),
      hd_error seq = Some T -> is_satisfiable_ExpansionTableau T ->
      exists (M : Model pred func), forall (mu : env M var) (i : nat) (T' : ExpansionTableau),
        seq.(i) = Some T' ->
        has_satisfiable_branch T' M mu.
  Proof using set_nat.
    intros seq ? eseq hsat.
    have hsat' := satisfiable_ExpansionSequence seq T eseq hsat (#|seq| - 1).
    have [T' eT'] : exists T', seq.(#|seq| - 1) = Some T'.
    { have esome := nth_error_Some seq (#|seq| - 1).
      have hlt : #|seq| - 1 < #|seq|.
      { rewrite PeanoNat.Nat.sub_1_r. destruct seq, seq0.
        - cbn in eseq. inversion eseq.
        - cbn. lia. }
      rewrite -esome in hlt.
      destruct (seq.(#|seq| - 1)).
      - exists e; auto.
      - exfalso; now apply hlt. }
    specialize (hsat' T' eT'). destruct hsat' as (M & hsat'). exists M; intro mu; specialize (hsat' mu).
    clear hsat.

    enough (h : forall (i : nat) (T0 : ExpansionTableau),
               seq.(#|seq| - (S i)) = Some T0 -> has_satisfiable_branch T0 M mu).
    { intros ? T0 e. specialize (h (#|seq| - 1 - i)).
      have e0 : #| seq | - S (#| seq | - 1 - i) = i.
      { rewrite PeanoNat.Nat.sub_1_r Arith_base.minus_Sn_m_stt.
        - apply nth_error_Some' in e; lia.
        - rewrite PeanoNat.Nat.sub_sub_distr.
          + apply nth_error_Some' in e; lia.
          + have hseq : #|seq| > 0.
            { apply nth_error_Some' in e; destruct i; lia. }
            lia.
          + rewrite PeanoNat.Nat.succ_pred.
            * intro; apply nth_error_Some' in e; lia.
            * rewrite PeanoNat.Nat.sub_diag //. }
      rewrite e0 in h; eapply h; eauto. }

    intro i; induction i as [|i' IHi'].
    - now intros T0 e0; rewrite e0 in eT'; injection eT' => ->.
    - intros T0 eT0.
      have [T0' eT0'] : exists T0', seq.(#|seq| - S i') = Some T0'.
      { have h0 : #|seq| > 0 by apply nth_error_Some' in eT'; lia.
        have h : #|seq| - S i' < #|seq| by lia.
        destruct (seq.(#|seq| - S i')) eqn:T0'.
        - exists e; auto.
        - rewrite nth_error_None in T0'; lia. }
      specialize (IHi' T0' eT0').
      destruct (Compare_dec.dec_le (S (S i')) #|seq|).
      + have hred : T0 |> T0'.
        { apply (isSequence seq) with (i := #|seq| - S (S i')); auto.
          rewrite Arith_base.minus_Sn_m_stt //. }
        eapply satisfiable_rev_Expansion; eauto.
      + apply Compare_dec.not_le in H. unfold gt, lt in H.
        have hle' := le_S_n _ _ H.
        have hle : #|seq| <= S (S i') by apply le_S.
        rewrite -!PeanoNat.Nat.sub_0_le in hle, hle'.
        rewrite hle in eT0; rewrite hle' in eT0'.
        rewrite eT0 in eT0'; injection eT0' => -> //.
  Qed.

  Lemma satisfiable_ExpansionSequence_hasTableau_satisfiable :
    forall (Gamma : Con) (sigma : Substitution var Term) (T : hasTableau sko Gamma sigma),
      is_satisfiable (ctx_to_form Gamma) ->
      exists (M : Model pred func), forall (mu : env M var),
        is_tableau_satisfiable M mu T.
  Proof.
    intros ??? hsat.

    have hsat0 : is_satisfiable_ExpansionTableau (mkExpansionTableau Gamma).
    { destruct hsat as (M & hsat); exists M; intro mu. specialize (hsat mu).
      exists Gamma; split; auto. now left. }

    set seq := hasTableau_has_ExpansionSequence T.

    have [M hseq] := model_ExpansionSequence (proj1_sig seq) (mkExpansionTableau Gamma)
                       (proj2_sig seq) hsat0.
    exists M; intro mu. specialize (hseq mu).

    (* This is the nice hypothesis for [Or]. *)
    have hinterpGamma : interpret_form_ M [] mu (ctx_to_form Gamma).
    { destruct (hseq 0 (mkExpansionTableau Gamma) (proj2_sig seq)) as (B & hin & hinterp);
        destruct hin as [e | contra]; [|inversion contra].
      rewrite e //. }
    change [[ M # [] # mu '|= ctx_to_form Gamma ]] in hinterpGamma.

    (* TODO: find the nice hypothesis for [Neg (All F)]. *)

    (* have hinterpCanonical : *)
    (*   forall (F : Form) (t : Term) (symbs : sko_record sko), *)
    (*     (proj1_sig seq).(1) = Some (mkExpansionTableau (Gamma ,, Neg F{0 \to t})) -> *)
    (*     sko t (Neg (All F)) symbs Gamma = true -> Neg (All F) \in Gamma -> *)
    (*     interpret_form_ M [] mu (Neg F{0 \to t}). *)
    (* { intros; induction T; try inversion H. *)
    (*   - have e := proj2_sig (hasTableau_has_ExpansionSequence T). *)
    (*     unfold hd_error in e. rewrite e in H3; injection H3 => contra. *)

    clear hsat hsat0; induction T.

    (* Case: [Bot] *)
    - have [] := in_form_list_interp i hinterpGamma.

    (* Case: contradiction *)
    - now constructor.

    (* Case: [Neg (Neg F)]. *)
    - constructor; apply IHT.
      + intros k T'. rewrite -hasTableau_has_ExpansionSequence_NegNeg -nth_error_S; intro.
        eapply hseq; eauto.
      + eapply extend_with_equiv_form; eauto; apply neg_neg_equiv.

    (* Case: [Neg (Or F1 F2)] *)
    - constructor; apply IHT.
      + intros k T'. rewrite -hasTableau_has_ExpansionSequence_NegOr -nth_error_S; intro.
        eapply hseq; eauto.
      + apply interp_list_commute; eapply extend_with_equiv_form; eauto.
        apply neg_equiv; etransitivity; [apply or_comm|]; apply or_equiv; symmetry;
          apply neg_neg_equiv.

    (* Case: [Or F1 F2] *)
    - have hor := in_form_list_interp i hinterpGamma; cbn in hor; destruct hor as [hF1 | hF2].
      + constructor; apply IHT1.
        * admit.
        * cbn; now intros [].
      + constructor; apply IHT2.
        * admit.
        * cbn; now intros [].

    (* Case: [All F] *)
    - constructor; apply IHT. eapply extend_with_imply_form; eauto; apply instantiate_imply_all.
      now cbn.

    (* Case: [Neg (All F)] *)
    - constructor; apply IHT.
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
