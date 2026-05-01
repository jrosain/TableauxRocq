(** * Proofs: definition of free-variable tableaux proofs. *)

(** In this file, we define the free-variable tableau method as an "expansion" method,
    i.e., we define a [Tableau] as a proof tree, and a [TableauProof] is a [Sequence] of
    [Tableau]x such that an [ExpansionRule] is applied between every [Tableau] of the
    [Sequence]. We define what it means for a [TableauProof] to be closed, and show that,
    list of formulas [Neg F :: Gamma], if this context has a tableau proof, then [Gamma |= F]. *)

From Stdlib Require Import Lia.

From Tableaux Require Import Semantics.
From Tableaux Require Import Skolemization.
From Tableaux Require Import Syntax.

(** We start by specifying the operations required by a context.

    A [Module Type] is used in order to provide a programming abstraction.
    Implementation(s) are given below.

    We export this module as [Ctx]. Note that no operations of [Ctx] simplify. This allows to
    easily change the implementation without affecting any proof. *)
Module Type ICtx.
  Section Def.
    Context {pred func var : Atom}.

    Let Form := Form pred func var.

    Parameter t : Atom -> Atom -> Atom -> Type.

    Let t := t pred func var.

    Parameter empty : t.
    Parameter eq  : t -> t -> Prop.
    Parameter mk : list Form -> t.
    Parameter fv : t -> set_atom var.
    Parameter existsb : (Form -> bool) -> t -> bool.
    Parameter mem : Form -> t -> bool.
    Parameter In : Form -> t -> Prop.
    Parameter singleton : Form -> t.
    Parameter add : Form -> t -> t.
    Parameter elements : t -> list Form.
    Parameter union : t -> t -> t.
    Parameter pr : t -> string.
    Parameter to_form : t -> Form.
    Parameter GetFunctSymbols : @GetFunctSymbols func t.
    Existing Instance GetFunctSymbols.

    Parameter mem_spec : forall (F : Form) (Gamma : t), mem F Gamma = true <-> In F Gamma.
    Parameter existsb_exists :
      forall (P : Form -> bool) (Gamma : t),
        existsb P Gamma = true <-> (exists F : Form, In F Gamma /\ P F = true).
    Parameter in_or_union :
      forall (F : Form) (Gamma1 Gamma2 : t),
        In F (union Gamma1 Gamma2) <-> In F Gamma1 \/ In F Gamma2.
    Parameter union_emptyr :
      forall (Gamma : t), union Gamma empty = Gamma.
    Parameter union_emptyl :
      forall (Gamma : t), union empty Gamma = Gamma.
    Parameter union_assoc :
      forall (Gamma1 Gamma2 Gamma3 : t),
        union (union Gamma1 Gamma2) Gamma3 =
          union Gamma1 (union Gamma2 Gamma3).
    Parameter funct_symbols_union :
      forall (Gamma1 Gamma2 : t),
        function_symbols (union Gamma1 Gamma2) =
          function_symbols Gamma1 \union function_symbols Gamma2.
    Parameter to_form_union :
      forall (Gamma1 Gamma2 : t),
        to_form (union Gamma1 Gamma2) \equiv Neg (Or (Neg (to_form Gamma1)) (Neg (to_form Gamma2))).
    Parameter interp_form :
      forall (Gamma : t) (M : Model pred func) (rho : list M) (sigma : env M var),
        (forall F : Form, In F Gamma -> [[M # rho # sigma '|= F]]) ->
        [[M # rho # sigma '|= to_form Gamma]].
    Parameter in_interp :
      forall {Gamma : t} {M : Model pred func} {rho : list M} {sigma : env M var} {F : Form},
        [[M # rho # sigma '|= to_form Gamma]] -> In F Gamma -> [[M # rho # sigma '|= F]].
  End Def.
End ICtx.

Module ListCtx <: ICtx.
  Section Def.
    Context {pred func var : Atom}.

    Let Form := Form pred func var.

    (** We box the list in order to make list notations not work for contexts. *)
    Record t_ := Mk { obj : list Form }.
    Definition t := t_.
    Definition empty := Mk [].
    Definition eq : t -> t -> Prop := eq.
    Definition mk (l : list Form) : t := Mk l.

    Definition elements (Gamma : t) : list Form :=
      let 'Mk obj := Gamma in obj.

    Definition fv (Gamma : t) : set_atom var := fv (elements Gamma).
    Definition existsb (pred : Form -> bool) (Gamma : t) : bool := List.existsb pred (elements Gamma).
    Definition mem (F : Form) (Gamma : t) : bool := list_mem F (elements Gamma).
    Definition In (F : Form) (Gamma : t) : Prop := List.In F (elements Gamma).
    Definition singleton (F : Form) : t := mk [F].
    Definition add (F : Form) (Gamma : t) : t := mk (F :: elements Gamma).
    Definition union (Gamma1 Gamma2 : t) : t :=
      mk (elements Gamma1 ++ elements Gamma2).
    #[local] Open Scope string_scope.
    Definition pr : t -> string := fun _ => "Not yet implemented".
    Definition to_form (Gamma : t) := ls_to_form (elements Gamma).
    Definition GetFunctSymbols : @GetFunctSymbols func t :=
      fun Gamma => function_symbols (elements Gamma).

    Lemma mem_spec :
      forall (F : Form) (Gamma : t),
        mem F Gamma = true <-> In F Gamma.
    Proof using Type. intros F []; cbn; apply list_mem_spec. Qed.

    Lemma existsb_exists :
      forall (P : Form -> bool) (Gamma : t),
        existsb P Gamma = true <-> (exists F : Form, In F Gamma /\ P F = true).
    Proof using Type. intros P []; cbn; apply existsb_exists. Qed.

    Lemma in_or_union :
      forall (F : Form) (Gamma1 Gamma2 : t),
        In F (union Gamma1 Gamma2) <-> In F Gamma1 \/ In F Gamma2.
    Proof using Type.
      intros ? [] []; cbn; split; intro h.
      - by apply in_app_or.
      - by apply in_or_app.
    Qed.

    Lemma union_emptyr :
      forall (Gamma : t), union Gamma empty = Gamma.
    Proof using Type.
      intros []; unfold empty; destruct empty; unfold union, mk; cbn; f_equal;
        apply app_nil_r.
    Qed.

    Lemma union_emptyl :
      forall (Gamma : t), union empty Gamma = Gamma.
    Proof using Type.
      intros []; unfold empty; destruct empty; unfold union, mk; cbn; f_equal;
        apply app_nil_l.
    Qed.

    Lemma union_assoc :
      forall (Gamma1 Gamma2 Gamma3 : t),
        union (union Gamma1 Gamma2) Gamma3 =
          union Gamma1 (union Gamma2 Gamma3).
    Proof using Type.
      intros [Gamma1] [Gamma2] [Gamma3]; unfold union; cbn; f_equal; by rewrite app_assoc.
    Qed.

    Existing Instance GetFunctSymbols.
    Lemma funct_symbols_union :
      forall (Gamma1 Gamma2 : t),
        function_symbols (union Gamma1 Gamma2) =
          function_symbols Gamma1 \union function_symbols Gamma2.
    Proof using Type.
      intros; cbn.
      by rewrite fold_left_app set_fold_left.
    Qed.

    Lemma to_form_union :
      forall (Gamma1 Gamma2 : t),
        to_form (union Gamma1 Gamma2) \equiv Neg (Or (Neg (to_form Gamma1)) (Neg (to_form Gamma2))).
    Proof using Type. intros; apply ls_to_form_app. Qed.

    Lemma interp_form :
      forall (Gamma : t) (M : Model pred func) (rho : list M) (sigma : env M var),
        (forall F : Form, In F Gamma -> [[M # rho # sigma '|= F]]) ->
        [[M # rho # sigma '|= to_form Gamma]].
    Proof using Type. intros; by apply interp_form_list. Qed.

    Lemma in_interp :
      forall {Gamma : t} {M : Model pred func} {rho : list M} {sigma : env M var} {F : Form},
        [[M # rho # sigma '|= to_form Gamma]] -> In F Gamma -> [[M # rho # sigma '|= F]].
    Proof using Type. intros; eapply in_form_list_interp; eauto. Qed.
  End Def.
  #[global] Arguments t : clear implicits.
End ListCtx.

Module Ctx := ListCtx.
Opaque Ctx.t Ctx.empty Ctx.eq Ctx.mk Ctx.fv Ctx.existsb Ctx.mem Ctx.In Ctx.singleton
  Ctx.add Ctx.elements Ctx.union Ctx.to_form Ctx.GetFunctSymbols.
Existing Instance Ctx.GetFunctSymbols.
Notation "F \in Gamma" := (Ctx.In F Gamma) (at level 30).

#[global] Instance GetFunctSymbs_Ctx {pred func var : Atom} :
  @GetFunctSymbols func (Ctx.t pred func var) := fun Gamma => function_symbols (Ctx.elements Gamma).

(** ** Tableaux *)
Section Tableaux.
  Context `{set_nat : set nat} {pred func var : Atom} (sko : Skolemization_ pred func var).

  Let Form := Form pred func var.
  Let Ctx := Ctx.t pred func var.

  Inductive TableauTree :=
  | Leaf
  | Node (T1 : TableauTree) (Gamma : Ctx) (T2 : TableauTree) : TableauTree.

  Inductive BranchingStep := Left | Right.

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
  Notation "B \rhd d" := (B ++ [d]) (at level 20).

  Lemma branch_extend_left_right :
    forall (B : Branch), B \rhd Left <> B \rhd Right.
  Proof using Type.
    induction B; try easy.
    cbn; intro e; apply IHB; injection e => -> //.
  Qed.

  Definition EmptyBranch : Branch := [].

  (** A [Branch] [is_branch_of] a [TableauTree] whenever the list of branching steps describes
      a path from the root of the [TableauTree] to a node without children. *)
  Inductive is_branch_of : Branch -> TableauTree -> Prop :=
  | is_branch_of_nil : forall (Gamma : Ctx), is_branch_of EmptyBranch (Node Leaf Gamma Leaf)
  | is_branch_of_left :
    forall (T1 T2 : TableauTree) (Gamma : Ctx) (B : Branch),
      is_branch_of B T1 -> is_branch_of (Left :: B) (Node T1 Gamma T2)
  | is_branch_of_right :
    forall (T1 T2 : TableauTree) (Gamma : Ctx) (B : Branch),
      is_branch_of B T2 -> is_branch_of (Right :: B) (Node T1 Gamma T2).

  Lemma is_branch_of_dec :
    forall (B : Branch) (T : TableauTree),
      is_branch_of B T \/ ~ is_branch_of B T.
  Proof using Type.
    intros B T; revert B; induction T; intros B; destruct B as [|b B].
    - right; now intro.
    - right; now intro.
    - destruct T1, T2.
      * left; constructor.
      * right; intro contra; inversion contra; easy.
      * right; intro contra; inversion contra; easy.
      * right; intro contra; inversion contra; easy.
    - destruct b.
      + destruct (IHT1 B).
        * left; now constructor.
        * right; intro contra; now inversion contra.
      + destruct (IHT2 B).
        * left; now constructor.
        * right; intro contra; now inversion contra.
  Qed.

  (** A [Branch] [is_subbranch_of] a [TableauTree] whenever the list of branching steps describes
      a path from the root of the [TableauTree] to any node of the tree. *)
  Inductive is_subbranch_of : Branch -> TableauTree -> Prop :=
  | is_subbranch_of_node :
    forall (Gamma : Ctx) (T1 T2 : TableauTree), is_subbranch_of EmptyBranch (Node T1 Gamma T2)
  | is_subbranch_of_left :
    forall (T1 T2 : TableauTree) (Gamma : Ctx) (B : Branch),
      is_subbranch_of B T1 -> is_subbranch_of (Left :: B) (Node T1 Gamma T2)
  | is_subbranch_of_right :
    forall (T1 T2 : TableauTree) (Gamma : Ctx) (B : Branch),
      is_subbranch_of B T2 -> is_subbranch_of (Right :: B) (Node T1 Gamma T2).

  (** Of course, a branch [B] [is_subbranch_of] a [TableauTree] whenever it [is_branch_of] this
      [TableauTree]. *)
  Lemma is_branch_of_is_subbranch_of :
    forall (B : Branch) (T : TableauTree),
      is_branch_of B T -> is_subbranch_of B T.
  Proof using Type.
    intros ?? hbranchof; induction hbranchof.
    - apply is_subbranch_of_node.
    - apply is_subbranch_of_left; auto.
    - apply is_subbranch_of_right; auto.
  Defined.
  #[global] Coercion is_branch_of_is_subbranch_of : is_branch_of >-> is_subbranch_of.

  (** A [Form]ula [F] [is_on_branch] [B] if it appears in any one of the nodes along [B]. *)
  Inductive is_on_branch (F : Form) : Branch -> TableauTree -> Prop :=
  | is_on_branch_node :
    forall (T1 T2 : TableauTree) (Gamma : Ctx) (B : Branch),
      F \in Gamma -> is_on_branch F B (Node T1 Gamma T2)
  | is_on_branch_left :
    forall (T1 T2 : TableauTree) (Gamma : Ctx) (B : Branch),
      is_on_branch F B T1 -> is_on_branch F (Left :: B) (Node T1 Gamma T2)
  | is_on_branch_right :
    forall (T1 T2 : TableauTree) (Gamma : Ctx) (B : Branch),
      is_on_branch F B T2 -> is_on_branch F (Right :: B) (Node T1 Gamma T2).

  Definition mkOptionalNode (Gamma : option Ctx) :=
    match Gamma with
    | Some Gamma => Node Leaf Gamma Leaf
    | None => Leaf
    end.

  Fixpoint expand_tableau_branch__aux (left_forms right_forms : option Ctx)
    (B : Branch) (T : TableauTree) : option TableauTree :=
    match B, T with
    | [], Node Leaf Gamma Leaf =>
        Some (Node (mkOptionalNode left_forms) Gamma (mkOptionalNode right_forms))
    | Left :: B, Node T1 Gamma T2 =>
        expand_tableau_branch__aux left_forms right_forms B T1 >>=
          (fun T1 => Some (Node T1 Gamma T2))
    | Right :: B, Node T1 Gamma T2 =>
        expand_tableau_branch__aux left_forms right_forms B T2 >>=
          (fun T2 => Some (Node T1 Gamma T2))
    | _, _ => None
    end.

  Lemma expand_tableau_branch_Some_is_branch_of :
    forall {B : Branch} {T T' : TableauTree}
      {left_forms right_forms : option Ctx},
      expand_tableau_branch__aux left_forms right_forms B T = Some T' ->
      is_branch_of B T.
  Proof using Type.
    intros B; induction B as [|b B IHB]; intros ???? e.
    - destruct T; try easy.
      destruct T1, T2; try easy.
      apply is_branch_of_nil.
    - destruct b, T; try easy.
      + cbn in e; destruct (expand_tableau_branch__aux left_forms right_forms B T1) eqn:eexp;
          try easy.
        eapply is_branch_of_left, IHB; eauto.
      + cbn in e; destruct (expand_tableau_branch__aux left_forms right_forms B T2) eqn:eexp;
          try easy.
        eapply is_branch_of_right, IHB; eauto.
  Qed.

  Lemma expand_tableau_branch_left :
    forall (Gamma : Ctx) (T1 T1' T2 : TableauTree) (B : Branch)
      (left_forms right_forms : option Ctx),
      expand_tableau_branch__aux left_forms right_forms B T1 = Some T1' ->
      expand_tableau_branch__aux left_forms right_forms (Left :: B) (Node T1 Gamma T2) =
        Some (Node T1' Gamma T2).
  Proof using Type. intros ??????? e; cbn; rewrite e //. Qed.

  Lemma expand_tableau_branch_right :
    forall (Gamma : Ctx) (T1 T2 T2' : TableauTree) (B : Branch)
      (left_forms right_forms : option Ctx),
      expand_tableau_branch__aux left_forms right_forms B T2 = Some T2' ->
      expand_tableau_branch__aux left_forms right_forms (Right :: B) (Node T1 Gamma T2) =
        Some (Node T1 Gamma T2').
  Proof using Type. intros ??????? e; cbn; rewrite e //. Qed.

  Lemma is_branch_of_extend_left :
    forall {T T' : TableauTree} {B : Branch} {l : Ctx} {l' : option Ctx},
      is_branch_of B T -> expand_tableau_branch__aux (Some l) l' B T = Some T' ->
      is_branch_of (B \rhd Left) T'.
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

  Lemma is_branch_of_extend_left' :
    forall {T T' : TableauTree} {B : Branch} {l : Ctx} {l' : option Ctx},
      is_branch_of B T -> expand_tableau_branch__aux (Some l) l' B T = Some T' ->
      ~is_branch_of B T'.
  Proof using Type.
    intros ????? hbranchof e hbranchof'.
    generalize dependent T'; induction hbranchof; intros T' e hbranchof'; cbn in *.
    - injection e => eT; rewrite -eT in hbranchof'; inversion hbranchof'.
    - destruct (expand_tableau_branch__aux (Some l) l' B T1) eqn:eT'; try easy.
      injection e => eT; rewrite -eT in hbranchof'; inversion hbranchof'; subst.
      now specialize (IHhbranchof t eq_refl H1).
    -  destruct (expand_tableau_branch__aux (Some l) l' B T2) eqn:eT'; try easy.
      injection e => eT; rewrite -eT in hbranchof'; inversion hbranchof'; subst.
      now specialize (IHhbranchof t eq_refl H1).
  Qed.

  Lemma is_branch_of_extend_right :
    forall {T T' : TableauTree} {B : Branch} {l : option Ctx} {l' : Ctx},
      is_branch_of B T -> expand_tableau_branch__aux l (Some l') B T = Some T' ->
      is_branch_of (B \rhd Right) T'.
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

  Lemma is_branch_of_extend_oth :
    forall (T T' : TableauTree) (B B' : Branch) (l l' : option Ctx),
      is_branch_of B' T -> is_branch_of B T -> B <> B' ->
      expand_tableau_branch__aux l l' B T = Some T' -> is_branch_of B' T'.
  Proof using Type.
    intros ????. revert T T' B'. induction B as [|b B IHB];
      intros ????? hbranchof' hbranchof n e;  destruct B' as [|b' B'].
    - easy.
    - inversion hbranchof; subst; inversion hbranchof'; inversion H0.
    - inversion hbranchof'; subst; inversion hbranchof; inversion H0.
    - destruct b.
      + inversion hbranchof. destruct (expand_tableau_branch__aux l l' B T1) eqn:e1.
        * erewrite <-H1, expand_tableau_branch_left in e; eauto. destruct b'.
          -- injection e => <-. apply is_branch_of_left. eapply IHB; eauto.
             ++ inversion hbranchof'; subst; auto.
                injection H4 => _ _ <- //.
             ++ congruence.
          -- rewrite -H1 in hbranchof'. inversion hbranchof'; subst.
             injection e => <-. now apply is_branch_of_right.
        * cbn in e. destruct T; try easy. injection H1 => _ _ eT1. rewrite eT1 in e1.
          rewrite e1 in e. inversion e.
      + inversion hbranchof. destruct (expand_tableau_branch__aux l l' B T2) eqn:e2.
        * erewrite <- H1, expand_tableau_branch_right in e; eauto. destruct b'.
          -- rewrite -H1 in hbranchof'. inversion hbranchof'; subst.
             injection e => <-. now apply is_branch_of_left.
          -- injection e => <-. apply is_branch_of_right. eapply IHB; eauto.
             ++ inversion hbranchof'; subst; auto.
                injection H4 => <- _ _ //.
             ++ congruence.
        * cbn in e. destruct T; try easy. injection H1 => eT2 _ _. rewrite eT2 in e2.
          rewrite e2 in e. inversion e.
  Qed.

  Fixpoint replace_child (B : Branch) (T T' : TableauTree) : option TableauTree :=
    match B, T with
    | [], _ => ret T'
    | Left :: B, Node T1 Gamma T2 =>
        T1 <- replace_child B T1 T';
        ret (Node T1 Gamma T2)
    | Right :: B, Node T1 Gamma T2 =>
        T2 <- replace_child B T2 T';
        ret (Node T1 Gamma T2)
    | _, _ => None
    end.

  (** The [label] of a branch is the label of the last node of the branch. *)
  Fixpoint get_label (B : Branch) (T : TableauTree) : option Ctx :=
    match B, T with
    | [], Node _ Gamma _ => Some Gamma
    | Left :: B, Node T1 Gamma _ => get_label B T1
    | Right :: B, Node _ Gamma T2 => get_label B T2
    | _, _ => None
    end.

  Lemma is_subbranch_of_has_label :
    forall {B : Branch} {T : TableauTree},
      is_subbranch_of B T ->
      exists Gamma, get_label B T = Some Gamma.
  Proof using Type.
    intros ?? hsubbranchof; induction hsubbranchof; try easy.
    exists Gamma; auto.
  Qed.

  Fixpoint get_child_at (B : Branch) (T : TableauTree) : option TableauTree :=
    match B, T with
    | [], _ => ret T
    | Left :: B, Node T1 _ _ => get_child_at B T1
    | Right :: B, Node _ _ T2 => get_child_at B T2
    | _, _ => None
    end.

  Lemma is_branch_of_get_child_at :
    forall {B : Branch} {T : TableauTree},
      is_branch_of B T -> exists T', T' <> Leaf /\ get_child_at B T = Some T'.
  Proof using Type.
    intros ?? hbranchof. induction hbranchof; auto.
    exists (Node Leaf Gamma Leaf); split; easy.
  Qed.

  Lemma replace_child_get_child_at :
    forall (B : Branch) (T T' : TableauTree),
      get_child_at B T = Some T' ->
      replace_child B T T' = Some T.
  Proof using Type.
    intro B; induction B as [|b B IHB]; intros ?? e; try easy.
    destruct b.
    - destruct T; try easy.
      cbn; rewrite IHB; auto.
    - destruct T; try easy.
      cbn; rewrite IHB; auto.
  Qed.

  Lemma replace_expand_Left :
    forall {B : Branch} {T T0 : TableauTree} (T' : TableauTree) {l : Ctx},
      is_branch_of B T -> expand_tableau_branch__aux (Some l) None B T = Some T0 ->
      exists T'', T'' <> Leaf /\ replace_child B T T'' = replace_child (B \rhd Left) T0 T'.
  Proof using Type.
    intros ????? hbranchof; revert  T0 T' l.
    induction hbranchof; intros ??? hexpand.
    - cbn in *. injection hexpand => <-.
      exists (Node T' Gamma Leaf); split; easy.
    - cbn in *. destruct (expand_tableau_branch__aux (Some l) None B T1) eqn:eT1; try easy.
      destruct (IHhbranchof _ T' _ eT1) as (T0' & hnleaf & ereplace).
      exists T0'; rewrite ereplace; cbn.
      split; destruct T0; try easy.
      injection hexpand => e0 e1 e2; now subst.
    - cbn in *. destruct (expand_tableau_branch__aux (Some l) None B T2) eqn:eT2; try easy.
      destruct (IHhbranchof _ T' _ eT2) as (T0' & hnleaf & ereplace).
      exists T0'; rewrite ereplace; cbn.
      split; destruct T0; try easy.
      injection hexpand => e0 e1 e2; now subst.
  Qed.

  Lemma replace_child_sequence_expand :
    forall {B : Branch} {T T0 : TableauTree} (T1 T2 : TableauTree) {l l' : option Ctx},
      expand_tableau_branch__aux l l' B T = Some T0 ->
      (T' <- replace_child (B \rhd Left) T T1;
       replace_child (B \rhd Right) T' T2) =
      (T' <- replace_child (B \rhd Left) T0 T1;
       replace_child (B \rhd Right) T' T2).
  Proof using Type.
    intros B; induction B as [|b B IHB]; intros ?????? e.
    - destruct T; try easy; cbn in *.
      destruct T3, T4; try easy.
      now injection e => <-.
    - destruct b, T; cbn in *; try easy.
      + destruct (expand_tableau_branch__aux l l' B T3) eqn:eexpand; try easy.
        injection e => <-; cbn in *.
        specialize (IHB T3 t T1 T2 l l' eexpand).
        destruct (replace_child (B \rhd Left) T3 T1),
          (replace_child (B \rhd Left) t T1); try easy;
          rewrite IHB //.
        rewrite -IHB //.
      + destruct (expand_tableau_branch__aux l l' B T4) eqn:eexpand; try easy.
        injection e => <-; cbn in *.
        specialize (IHB T4 t T1 T2 _ _ eexpand).
        destruct (replace_child (B \rhd Left) T4 T1),
          (replace_child (B \rhd Left) t T1); try easy;
          rewrite IHB //.
        rewrite -IHB //.
  Qed.

  Lemma replace_child_Node :
    forall {B : Branch} {T : TableauTree} (T1 T2 : TableauTree) (Gamma : Ctx),
      is_branch_of B T -> get_label B T = Some Gamma ->
      replace_child B T (Node T1 Gamma T2) =
        (T' <- replace_child (B \rhd Left) T T1;
         replace_child (B \rhd Right) T' T2).
  Proof using Type.
    intros ????? hbranchof; revert T1 T2 Gamma; induction hbranchof; intros ??? elabel.
    - cbn in *; injection elabel => -> //.
    - cbn in *. specialize (IHhbranchof T0 T3 Gamma0 elabel).
      rewrite IHhbranchof. destruct (replace_child (B ++ [Left]) _ _) eqn:erepl0; easy.
    - cbn in *. specialize (IHhbranchof T0 T3 Gamma0 elabel).
      rewrite IHhbranchof. destruct (replace_child (B ++ [Left]) _ _) eqn:erepl0; easy.
  Qed.

  Lemma is_branch_of_replace_child_oth :
    forall {B B' : Branch} {T T' T0 : TableauTree},
      is_branch_of B T -> is_branch_of B' T -> B <> B' -> replace_child B' T T' = Some T0 ->
      is_branch_of B T0.
  Proof using Type.
    intros ????? hbranchof hbranchof'; revert B T' T0 hbranchof;
      induction hbranchof'; intros B0 T' T0 hbranchof ne e.
    - destruct B0; try easy.
      inversion hbranchof; easy.
    - cbn in e. destruct (replace_child B T1 T') eqn:erepl; try easy.
      injection e => e'; subst. destruct B0.
      + inversion hbranchof; subst. inversion hbranchof'.
      + destruct b.
        * inversion hbranchof; subst.
          eapply is_branch_of_left, IHhbranchof'; eauto. congruence.
        * apply is_branch_of_right. inversion hbranchof; now subst.
    - cbn in e. destruct (replace_child B T2 T') eqn:erepl; try easy.
      injection e => e'; subst. destruct B0.
      + inversion hbranchof; subst. inversion hbranchof'.
      + destruct b.
        * apply is_branch_of_left. inversion hbranchof; now subst.
        * inversion hbranchof; subst.
          eapply is_branch_of_right, IHhbranchof'; eauto. congruence.
  Qed.

  Lemma is_branch_of_replace_child_oth_inv :
    forall {B B' : Branch} {b b' : BranchingStep} {T T' T0 : TableauTree},
      is_branch_of (B ++ b :: B') T0 -> b <> b' -> replace_child (B \rhd b') T T' = Some T0 ->
      is_branch_of (B ++ b :: B') T.
  Proof using Type.
    intro B; induction B as [|b0 B0 IHB0]; intros ?????? hbranchof ne erepl.
    - cbn in *. destruct b, b'; try easy.
      + destruct T; try easy.
        injection erepl => eT0. rewrite -eT0 in hbranchof; inversion hbranchof; subst.
        now constructor.
      + destruct T; try easy.
        injection erepl => eT0. rewrite -eT0 in hbranchof; inversion hbranchof; subst.
        now constructor.
    - cbn in *; destruct b0.
      + destruct T; try easy.
        destruct (replace_child _ _ _) eqn:erepl0; try easy.
        inversion hbranchof; subst.
        injection erepl => eT2 eG et; subst.
        specialize (IHB0 B' b b' T1 T' T3 H0 ne erepl0).
        now constructor.
      + destruct T; try easy.
        destruct (replace_child _ _ _) eqn:erepl0; try easy.
        inversion hbranchof; subst.
        injection erepl => eT2 eG et; subst.
        specialize (IHB0 B' b b' T2 T' T4 H0 ne erepl0).
        now constructor.
  Qed.

  (** The [context] of a branch is the list of all the formulas of a branch. *)
  Fixpoint get_context (B : Branch) (T : TableauTree) : Ctx :=
    match B, T with
    | [], Node Leaf Gamma Leaf => Gamma
    | Left :: B, Node T1 Gamma _ => (Ctx.union (get_context B T1) Gamma)
    | Right :: B, Node _ Gamma T2 => (Ctx.union (get_context B T2) Gamma)
    | _, _ => Ctx.empty
    end.

  Lemma get_context_replace_child_oth :
    forall {B B' : Branch} {T T' T0 : TableauTree},
      is_branch_of B T -> is_branch_of B' T -> B <> B' -> replace_child B' T T' = Some T0 ->
      get_context B T = get_context B T0.
  Proof using Type.
    intros ????? hbranchof hbranchof'; revert B T' T0 hbranchof;
      induction hbranchof'; intros B0 T' T0 hbranchof ne e.
    - destruct B0; try easy.
      inversion hbranchof; easy.
    - cbn in e. destruct (replace_child B T1 T') eqn:erepl; try easy.
      injection e => e'; subst. destruct B0.
      + inversion hbranchof; subst. inversion hbranchof'.
      + destruct b.
        * inversion hbranchof; subst.
          cbn. erewrite IHhbranchof'; eauto. congruence.
        * now cbn.
    - cbn in e. destruct (replace_child B T2 T') eqn:erepl; try easy.
      injection e => e'; subst. destruct B0.
      + inversion hbranchof; subst. inversion hbranchof'.
      + destruct b.
        * now cbn.
        * inversion hbranchof; subst.
          cbn; erewrite IHhbranchof'; eauto. congruence.
  Qed.

  Lemma get_context_app_fst :
    forall (F : Form) (B B' : Branch) (T : TableauTree),
      F \in get_context B T -> F \in get_context (B ++ B') T.
  Proof using Type.
    intros ??; induction B as [|b B IHB]; intros ?? hin.
    - destruct T; cbn in *.
      + inversion hin.
      + destruct T1, T2; try easy.
        destruct B'; try easy.
        destruct b; cbn; rewrite Ctx.in_or_union; now right.
    - destruct b, T; cbn in *; try easy;
        rewrite Ctx.in_or_union in hin; destruct hin as [hin | hin];
        rewrite Ctx.in_or_union.
        + left; by apply IHB.
        + by right.
        + left; by apply IHB.
        + by right.
  Qed.

  Fixpoint get_all_formulas (T : TableauTree) : Ctx :=
    match T with
    | Leaf => Ctx.empty
    | Node T1 Gamma T2 => Ctx.union (Ctx.union Gamma (get_all_formulas T1)) (get_all_formulas T2)
    end.

  Lemma in_get_ctx_in_all_formulas :
    forall (B : Branch) (T : TableauTree) (F : Form),
      is_branch_of B T -> F \in get_context B T -> F \in get_all_formulas T.
  Proof using Type.
    intros ??? hbranchof; induction hbranchof.
    - intro; cbn in *. rewrite !Ctx.union_emptyr //.
    - cbn; intros [hin | hin]%Ctx.in_or_union.
      + rewrite Ctx.in_or_union; left.
        rewrite Ctx.in_or_union; right.
        by apply IHhbranchof.
      + rewrite Ctx.in_or_union; left.
        by rewrite Ctx.in_or_union; left.
    - cbn; intros [hin | hin]%Ctx.in_or_union.
      + rewrite Ctx.in_or_union; right.
        now apply IHhbranchof.
      + rewrite Ctx.in_or_union; left.
        by rewrite Ctx.in_or_union; left.
  Qed.

  (** Actually, a [Tableau] also keeps in memory the Skolem symbols introduced. *)
  Record Tableau :=
    mkTab { tree :> TableauTree ; symbols : sko_record sko }.

  Definition expand_tableau_branch (left_forms right_forms : option Ctx)
    (B : Branch) (T : Tableau) : option Tableau :=
    expand_tableau_branch__aux left_forms right_forms B T >>=
      (fun tree => Some (mkTab tree (symbols T))).

  (** A [Sequence] is a list of tableaux. *)
  Definition Sequence := list Tableau.

  Definition is_branch_closed (T : Tableau) (sigma : Substitution var (Term func var))
    (B : Branch) : Prop :=
    Bot \in get_context B T \/
      (exists (F G : Form),
          F \in get_context B T /\ G \in get_context B T /\
            F@[sigma] = Neg G@[sigma]).

  (** A [Tableau] is said closed under a substitution if every branch has a contradiction. *)
  Definition is_tableau_closed (T : Tableau) (sigma : Substitution var (Term func var)) : Prop :=
    forall (B : Branch), is_branch_of B T -> is_branch_closed T sigma B.

  (** A [Branch] of a [Tableau] is satisfied if its context is satisfied. *)
  Definition exists_satisfied_branch (M : Model pred func) (mu : env M var) (T : Tableau) : Prop :=
    exists (B : Branch),
      is_branch_of B T /\ [[ M # [] # mu '|= Ctx.to_form (get_context B T) ]].

  (** A [Tableau] is said satisfiable if there exists a model such that for every free-variable
      environment, there is a branch that is satisfied. *)
  Definition is_tableau_satisfiable (T : Tableau) :=
    exists (M : Model pred func), forall (mu : env M var), exists_satisfied_branch M mu T.

  (** We say that a tableau [T] preserves the function symbols of [s] if the function symbols of
      [get_all_formulas T] is equal to [s \union to_set record]. *)
  Definition preserves_function_symbols (T : Tableau) (s : set_atom func) :=
    function_symbols (get_all_formulas T) \subseteq s \union to_set (symbols T).

  Definition mkTableau (Gamma : Ctx) : Tableau :=
    mkTab (Node Leaf Gamma Leaf) empty_record.

  Definition mkLeaf : Tableau :=
    mkTab Leaf empty_record.

  Lemma get_context_extend_left :
    forall {T T' : TableauTree} {B : Branch} {Gamma l : Ctx} {l' : option Ctx},
      is_branch_of B T -> expand_tableau_branch__aux (Some l) l' B T = Some T' ->
      get_context B T = Gamma -> get_context (B \rhd Left) T' = Ctx.union l Gamma.
  Proof using Type.
    intro T; induction T; intros ????? hbranchof e eT; destruct B.
    - inversion e.
    - inversion e; destruct b; easy.
    - inversion hbranchof; subst; cbn in e.
      injection e => <- //.
    - destruct b; cbn.
      + inversion hbranchof; subst.
        cbn in e. destruct (expand_tableau_branch__aux (Some l) l' B T1) eqn:eT1.
        * injection e => <-; cbn in *. erewrite IHT1; eauto.
          rewrite Ctx.union_assoc //.
        * inversion e.
      + inversion hbranchof; subst; cbn in e.
        destruct (expand_tableau_branch__aux (Some l) l' B T2) eqn:eT2.
        * injection e => <-; cbn in *. erewrite IHT2; eauto.
          rewrite Ctx.union_assoc //.
        * inversion e.
  Qed.

  Lemma get_context_extend_right :
    forall {T T' : TableauTree} {B : Branch} {Gamma l' : Ctx} {l : option Ctx},
      is_branch_of B T -> expand_tableau_branch__aux l (Some l') B T = Some T' ->
      get_context B T = Gamma -> get_context (B \rhd Right) T' = Ctx.union l' Gamma.
  Proof using Type.
    intro T; induction T; intros ????? hbranchof e eT; destruct B.
    - inversion e.
    - inversion e. destruct b; easy.
    - inversion hbranchof; subst; cbn in e.
      injection e => <-; now cbn.
    - destruct b; cbn.
      + inversion hbranchof; subst; cbn in e.
        destruct (expand_tableau_branch__aux l (Some l') B T1) eqn:eT1.
        * injection e => <-; cbn in *. erewrite IHT1; eauto.
          rewrite Ctx.union_assoc //.
        * inversion e.
      + inversion hbranchof; subst.
        cbn in e. destruct (expand_tableau_branch__aux l (Some l') B T2) eqn:eT2.
        * injection e => <-; cbn in *. erewrite IHT2; eauto.
          rewrite Ctx.union_assoc //.
        * inversion e.
  Qed.

  Lemma get_context_extend_oth :
    forall (T T' : TableauTree) (B B' : Branch) (l l' : option Ctx),
      is_branch_of B T -> is_branch_of B' T -> B <> B' ->
      expand_tableau_branch__aux l l' B T = Some T' -> get_context B' T = get_context B' T'.
  Proof using Type.
    intros ?? B. revert T T'. induction B as [|b B IHB]; intros ????? hbranchof hbranchof' n e;
      destruct B' as [|b' B'].
    - easy.
    - inversion hbranchof; subst. inversion hbranchof'; subst; inversion H0.
    - inversion hbranchof'; subst. inversion hbranchof; subst; inversion H0.
    - destruct b, b'; cbn.
      + inversion hbranchof; subst.
        destruct (expand_tableau_branch__aux l l' B T1) eqn:e1.
        * erewrite expand_tableau_branch_left in e; eauto.
          injection e => <-. erewrite IHB; eauto.
          -- now inversion hbranchof'.
          -- congruence.
        * cbn in e; rewrite e1 in e; inversion e.
      + inversion hbranchof'; subst.
        destruct (expand_tableau_branch__aux l l' B T1) eqn:e1.
        * erewrite expand_tableau_branch_left in e; eauto. injection e => <- //.
        * cbn in e; rewrite e1 in e; inversion e.
      + inversion hbranchof'; subst.
        destruct (expand_tableau_branch__aux l l' B T2) eqn:e2.
        * erewrite expand_tableau_branch_right in e; eauto. injection e => <- //.
        * cbn in e; rewrite e2 in e; inversion e.
      + inversion hbranchof; subst.
        destruct (expand_tableau_branch__aux l l' B T2) eqn:e2.
        * erewrite expand_tableau_branch_right in e; eauto.
          injection e => <-. erewrite IHB; eauto.
          -- now inversion hbranchof'.
          -- congruence.
        * cbn in e; rewrite e2 in e; inversion e.
  Qed.

  Lemma is_branch_of_expand_tableau_branch :
    forall {B : Branch} {T : Tableau} (l l' : option Ctx),
      is_branch_of B T ->
      exists (T' : Tableau), expand_tableau_branch l l' B T = Some T'.
  Proof using Type.
    intros ? [T symbs ] ?? hbranchof; cbn in *. induction hbranchof; cbn.
    - exists (mkTab (Node (mkOptionalNode l) Gamma (mkOptionalNode l')) symbs); auto.
    - destruct IHhbranchof as (T1' & eT1').
      destruct (expand_tableau_branch__aux l l' B T1); cbn in *.
      + exists (mkTab (Node t Gamma T2) symbs); auto.
      + inversion eT1'.
    - destruct IHhbranchof as (T2' & eT2').
      destruct (expand_tableau_branch__aux l l' B T2); cbn in *.
      + exists (mkTab (Node T1 Gamma t) symbs); auto.
      + inversion eT2'.
  Qed.

  Lemma expand_tableau_branch_Some__aux :
    forall {B : Branch} {T T' : Tableau} {l l' : option Ctx},
      expand_tableau_branch l l' B T = Some T' ->
      expand_tableau_branch__aux l l' B T = Some (tree T').
  Proof using Type.
    intros ????? e; cbn in e.
    destruct (expand_tableau_branch__aux l l' B T); try easy.
    destruct T'; injection e => _ -> //.
  Qed.

  Lemma expand_tableau_branch_Some_symbs :
    forall {B : Branch} {T T' : Tableau} {l l' : option Ctx},
      expand_tableau_branch l l' B T = Some T' ->
      symbols T = symbols T'.
  Proof using Type.
    intros ????? e; cbn in e.
    destruct (expand_tableau_branch__aux l l' B T); try easy.
    destruct T'; injection e => -> _ //.
  Qed.

  Lemma replace_expanded_child_not_branch_Left :
    forall {B : Branch} {T T0 T0' T' : TableauTree} {Gamma : Ctx},
      is_branch_of B T -> T0' <> Leaf ->
      expand_tableau_branch__aux (Some Gamma) None B T = Some T0 ->
      replace_child (B \rhd Left) T0 T0' = Some T' -> ~is_branch_of B T'.
  Proof using Type.
    intro B; induction B as [|b B IHB]; intros ????? hbranchof hnleaf hexpand hrepl hbranchof'.

    - cbn in *. inversion hbranchof; subst; try easy.
      destruct T0; try easy.
      apply hnleaf. inversion hbranchof'; subst.
      injection hrepl => _ _ -> //.

    - destruct b; cbn in *.

      + destruct T, T0; try easy.
        destruct (expand_tableau_branch__aux _ _ _ _) eqn:hexpand1; try easy.
        destruct (replace_child _ _ _) eqn:erepl1; try easy.
        inversion hbranchof'; subst.
        inversion hbranchof; subst.
        specialize (IHB T1 t T0' T0); eapply IHB; eauto.
        injection hexpand => _ _ ->; injection hrepl => _ _ <- //.
      + destruct T, T0; try easy.
        inversion hbranchof; inversion hbranchof'; subst.
        destruct (expand_tableau_branch__aux _ _ _ _) eqn:hexpand1; try easy.
        destruct (replace_child _ _ _) eqn:erepl1; try easy.
        specialize (IHB T2); eapply IHB; eauto.
        injection hexpand => -> _ _; rewrite erepl1.
        injection hrepl => -> //.
  Qed.

  Lemma replace_expanded_child_not_branch_Right :
    forall {B : Branch} {T T0 T0' T1 T1' T2 : TableauTree} {Gamma1 Gamma2 : Ctx},
      is_branch_of B T -> T0' <> Leaf -> T1' <> Leaf ->
      expand_tableau_branch__aux (Some Gamma1) (Some Gamma2) B T = Some T0 ->
      replace_child (B \rhd Left) T0 T0' = Some T1 ->
      replace_child (B \rhd Right) T1 T1' = Some T2 -> ~is_branch_of B T2.
  Proof using Type.
    intro B; induction B as [|b B IHB];
      intros ???????? hbranchof hnleaf0 hnleaf1 hexpand hrepl1 hrepl2 hbranchof'.

    - cbn in *. inversion hbranchof; subst; try easy.
      destruct T0; try easy.
      destruct T1; try easy.
      apply hnleaf1. injection hrepl2 => eT2; subst.
      now inversion hbranchof'.

    - destruct b; cbn in *.

      + destruct T, T0, T1; try easy.
        destruct (expand_tableau_branch__aux _ _ _ _) eqn:hexpand1; try easy.
        destruct (replace_child (B ++ [Left]) _ _) eqn:erepl1; try easy.
        destruct (replace_child (B ++ [Right]) _ _) eqn:erepl2; try easy.
        inversion hbranchof'; subst.
        inversion hbranchof; subst.
        specialize (IHB T3 t T0' T1_1 T1' t1 Gamma1 Gamma2 H2 hnleaf0 hnleaf1 hexpand1).
        apply IHB; auto.
        * injection hexpand => _ _ ->.
          injection hrepl1 => _ _ <- //.
        * injection hrepl2 => _ _ -> //.
      + destruct T, T0, T1; try easy.
        destruct (expand_tableau_branch__aux _ _ _ _) eqn:hexpand1; try easy.
        destruct (replace_child (B ++ [Left]) _ _) eqn:erepl1; try easy.
        destruct (replace_child (B ++ [Right]) _ _) eqn:erepl2; try easy.
        inversion hbranchof'; subst.
        inversion hbranchof; subst.
        specialize (IHB T4 t T0' t0 T1' t1 Gamma1 Gamma2 H2 hnleaf0 hnleaf1 hexpand1).
        apply IHB; auto.
        * injection hexpand => -> //.
        * injection hrepl1 => -> //.
        * injection hrepl2 => -> //.
  Qed.

  Lemma replace_expanded_child_not_subbranch :
    forall {B : Branch} {T T0 T0' T' : TableauTree} {Gamma : Ctx},
      is_branch_of B T -> T0' <> Leaf ->
      expand_tableau_branch__aux (Some Gamma) None B T = Some T0 ->
      replace_child (B \rhd Left) T0 T0' = Some T' -> ~is_subbranch_of (B \rhd Right) T'.
  Proof using Type.
    intros ?????? hbranchof. revert T0 T0' T' Gamma; induction hbranchof;
      intros ???? ne hexpand erepl hbranchof'; cbn in *.

    - injection hexpand => eT0; subst.
      injection erepl => eT'; subst. inversion hbranchof'; subst.
      inversion H1.

    - destruct T0; try easy.
      destruct (expand_tableau_branch__aux _ _ _ _) eqn:hexpand1; try easy.
      destruct (replace_child _ _ _) eqn:erepl1; try easy.
      injection erepl => eT'; subst; inversion hbranchof'; subst.
      eapply IHhbranchof with (T' := t0); eauto.
      injection hexpand => _ _ -> //.

    - destruct T0; try easy.
      destruct (expand_tableau_branch__aux _ _ _ _) eqn:hexpand1; try easy.
      destruct (replace_child _ _ _) eqn:erepl1; try easy.
      injection erepl => eT'; subst; inversion hbranchof'; subst.
      eapply IHhbranchof with (T' := t0); eauto.
      injection hexpand => -> //.
  Qed.

  Lemma not_subbranch_no_ext_is_branch :
    forall {B : Branch} (B' : Branch) {T : TableauTree},
      ~is_subbranch_of B T -> ~is_branch_of (B ++ B') T.
  Proof using Type.
    intros ??? hsubbranch hbranch.
    apply is_branch_of_is_subbranch_of in hbranch. apply hsubbranch; clear hsubbranch.
    revert B' T hbranch; induction B as [|b B IHB]; intros ?? hsubbranch.
    - cbn in hsubbranch; inversion hsubbranch; constructor.
    - destruct b; inversion hsubbranch; subst.
      + constructor. eapply IHB; eauto.
      + constructor. eapply IHB; eauto.
  Qed.

  Lemma extend_function_symbols_value :
    forall {B : Branch} {T T' : Tableau} {l l' : option Ctx},
      is_branch_of B T ->
      expand_tableau_branch__aux l l' B T = Some (tree T') ->
      function_symbols (get_all_formulas T') =
        function_symbols (get_all_formulas T) \union function_symbols l \union function_symbols l'.
  Proof using Type.
    intros ????? hbranchof; revert T' l l'; induction hbranchof; intros ??? e.
    - cbn in e; injection e => <-; cbn.
      rewrite !Ctx.union_emptyr !Ctx.funct_symbols_union.
      destruct l, l'; cbn; by rewrite ?Ctx.union_emptyr ?empty_unitr.
    - cbn in e; destruct (expand_tableau_branch__aux l l' B T1) eqn:hexpand; try easy.
      injection e => <-; cbn.
      specialize (IHhbranchof (mkTab t (symbols T)) _ _ hexpand); cbn in IHhbranchof.
      rewrite !Ctx.funct_symbols_union. apply set_ext; intro f; split; intro hin.
      + rewrite !union_spec in hin |- *.
        destruct hin as [ [ hG | ht ] | hT2 ].
        * now do 4 left.
        * rewrite IHhbranchof !union_spec in ht. destruct ht as [ [ hT1 | hl ] | hl' ].
          -- now do 3 left; right.
          -- now left; right.
          -- now right.
        * do 2 left; now right.
      + rewrite !union_spec in hin |- *.
        rewrite IHhbranchof !union_spec.
        destruct hin as [ [ [ [ hG | hT1 ] | hT2 ] | hl ] | hl' ].
        * now repeat left.
        * left; right; now repeat left.
        * now right.
        * now left; right; left; right.
        * now left; repeat right.
    - cbn in e; destruct (expand_tableau_branch__aux l l' B T2) eqn:hexpand; try easy.
      injection e => <-; cbn.
      specialize (IHhbranchof (mkTab t (symbols T)) _ _ hexpand); cbn in IHhbranchof.
      rewrite !Ctx.funct_symbols_union. apply set_ext; intro f; split; intro hin.
      + rewrite !union_spec in hin |- *.
        destruct hin as [ [ hG | ht ] | hT2 ].
        * now do 4 left.
        * do 3 left; now right.
        * rewrite IHhbranchof !union_spec in hT2. destruct hT2 as [ [ hT2 | hl ] | hl' ].
          -- do 2 left; now right.
          -- left; now right.
          -- now right.
      + rewrite !union_spec in hin |- *.
        rewrite IHhbranchof !union_spec.
        destruct hin as [ [ [ [ hG | hT1 ] | hT2 ] | hl ] | hl' ].
        * now repeat left.
        * left; right; now repeat left.
        * now right; repeat left.
        * now right; left; right.
        * now repeat right.
  Qed.

  Lemma extend_subset_preserves_function_symbols :
    forall {B : Branch} {T T' : Tableau} (s : set_atom func) {l l' : option Ctx},
      is_branch_of B T -> preserves_function_symbols T s ->
      to_set (symbols T) \subseteq to_set (symbols T') ->
      function_symbols l \subseteq s \union to_set (symbols T') ->
      function_symbols l' \subseteq s \union to_set (symbols T') ->
      expand_tableau_branch__aux l l' B T = Some (tree T') ->
      preserves_function_symbols T' s.
  Proof using Type.
    intros ?????? hbranchof hpres hsubsymb hsub1 hsub2 e.
    red in hpres |- *; cbn in hpres |- *.
    erewrite extend_function_symbols_value; eauto.
    intros g hin. rewrite !union_spec in hin |- *.
    destruct hin as [ [ hT | hl ] | hl' ].
    - specialize (hpres g hT); rewrite union_spec in hpres; destruct hpres as [hs | hsymbT].
      + now left.
      + right; now apply hsubsymb.
    - now rewrite -union_spec; apply hsub1.
    - now rewrite -union_spec; apply hsub2.
  Qed.

  (** An optional list of formulas is satisfied either if it is none or if the list is
      satisfied. *)
  Definition is_optional_satisfied
    (M : Model pred func) (mu : env M var) (l : option Ctx) :=
    match l with
    | None => False
    | Some l => [[ M # [] # mu '|= Ctx.to_form l ]]
    end.

  (** If a satisfiable tableau is extended with lists of formulas of which one of them is also
      satisfied by the same model, then the extended tableau is also satisfiable. *)
  Lemma is_satisfiable_extend_gen :
    forall (M M' : Model pred func) (T T' : Tableau) (B : Branch) (l l' : option Ctx)
      (mu' : env M' var) (f : env M' var -> env M var),
      is_branch_of B T -> expand_tableau_branch__aux l l' B T = Some (tree T') ->
      (forall (F : Form),
          F \in get_all_formulas T ->
          [[ M # [] # f mu' '|= F ]] ->
          [[ M' # [] # mu' '|= F ]]) ->
      ([[ M # [] # (f mu') '|= Ctx.to_form (get_context B T) ]] ->
       is_optional_satisfied M' mu' l \/ is_optional_satisfied M' mu' l') ->
      (exists_satisfied_branch M (f mu') T) ->
      exists_satisfied_branch M' mu' T'.
  Proof using Type.
    intros ?? [T symbs] [T' symbs'] ????? hbranchof e hcsv hsatlr (B & hbranchB & hsatB);
      cbn in e.

    destruct (B == B0); subst.

    (* Case: the branch that was satisfied is, in fact, [B0]. *)
    - destruct (hsatlr hsatB) as [hsatl | hsatr].

      (* Case: the extension with the formulas on the left is satisfied. *)
      + destruct l as [l|].
        * exists (B0 \rhd Left); split; cbn.
          -- destruct (expand_tableau_branch__aux (Some l) l' B0 T) eqn:eT.
             ++ eapply is_branch_of_extend_left; eauto.
                injection e => <-; eauto.
             ++ inversion e.
          -- destruct (expand_tableau_branch__aux (Some l) l' B0 T) eqn:eT.
             ++ injection e => eT'. rewrite eT' in eT. erewrite get_context_extend_left; eauto.
                cbn; unfold interpret; rewrite (Ctx.to_form_union l (get_context B0 T) M' [] mu').
                cbn; intros [hl | hnB0]; auto. apply hnB0, Ctx.interp_form.
                intros F hin; apply hcsv; auto.
                ** eapply in_get_ctx_in_all_formulas; eauto.
                ** apply (in_form_list_interp hin hsatB).
             ++ inversion e.
        * now cbn in hsatl.

      (* Case: the extension with the formulas on the right is satisfied. *)
      + destruct l' as [l0|].
        * exists (B0 \rhd Right); split; cbn.
          -- destruct (expand_tableau_branch__aux l (Some l0) B0 T) eqn:eT.
             ++ eapply is_branch_of_extend_right; eauto.
                injection e => <-; eauto.
             ++ inversion e.
          -- destruct (expand_tableau_branch__aux l (Some l0) B0 T) eqn:eT.
             ++ injection e => eT'; rewrite eT' in eT.
                erewrite get_context_extend_right; eauto.
                cbn; unfold interpret.
                rewrite (Ctx.to_form_union l0 (get_context B0 T) M' [] mu').
                cbn; intros [hl0 | hnB0]; auto. apply hnB0, Ctx.interp_form.
                intros F hin; apply hcsv; auto.
                ** eapply in_get_ctx_in_all_formulas; eauto.
                ** apply (in_form_list_interp hin hsatB).
             ++ inversion e.

        * inversion hsatr.

      (* Case: the branch that was satisfied is not [B0]. *)
    - destruct (expand_tableau_branch__aux l l' B0 T) eqn:eT'.
      + injection e => <-. exists B; split.
        * apply is_branch_of_extend_oth with (T := T) (B := B0) (l := l) (l' := l'); auto.
        * cbn in *. rewrite -(get_context_extend_oth T t B0 B l l' hbranchof hbranchB); try easy.
          apply Ctx.interp_form; intros F hin; apply hcsv.
          -- eapply in_get_ctx_in_all_formulas; eauto.
          -- apply (in_form_list_interp hin hsatB).
      + inversion e.
  Qed.

  Lemma is_satisfiable_extend :
    forall (M : Model pred func) (mu : env M var) (T T' : Tableau) (B : Branch)
      (l l' : option Ctx),
      is_branch_of B T -> expand_tableau_branch l l' B T = Some T' ->
      ([[ M # [] # mu '|= Ctx.to_form (get_context B T) ]] ->
       is_optional_satisfied M mu l \/ is_optional_satisfied M mu l') ->
      exists_satisfied_branch M mu T -> exists_satisfied_branch M mu T'.
  Proof using Type.
    intros ??????? hbranchof e himp hb.
    eapply is_satisfiable_extend_gen with (f := fun x => x); eauto.
    cbn in *; destruct (expand_tableau_branch__aux l l' B T); try easy.
    injection e => <- //.
  Qed.

  Lemma is_on_branch_in_context :
    forall (T : Tableau) (B : Branch) (F : Form),
      is_branch_of B T -> is_on_branch F B T -> F \in get_context B T.
  Proof using Type.
    intros ??? hbranchof honbranch. induction honbranch.
    - destruct B; cbn in *.
      + inversion hbranchof; now subst.
      + destruct b; apply Ctx.in_or_union; now right.
    - cbn. apply Ctx.in_or_union; left. apply IHhonbranch. now inversion hbranchof.
    - cbn. apply Ctx.in_or_union; left. apply IHhonbranch. now inversion hbranchof.
  Qed.

  Lemma in_context_is_on_branch :
    forall {T : Tableau} {B : Branch} {F : Form},
      is_branch_of B T -> F \in get_context B T -> is_on_branch F B T.
  Proof using Type.
    intros ??? hbranchof hin. induction hbranchof.
    - now apply is_on_branch_node.
    - cbn in hin; apply Ctx.in_or_union in hin; destruct hin as [ hT1 | hG ].
      + now apply is_on_branch_left, IHhbranchof.
      + now apply is_on_branch_node.
    - cbn in hin; apply Ctx.in_or_union in hin; destruct hin as [ hT2 | hG ].
      + now apply is_on_branch_right, IHhbranchof.
      + now apply is_on_branch_node.
  Qed.

  Lemma is_on_satisfiable_branch :
    forall {T : Tableau} {B : Branch} {F : Form} {M : Model pred func} {mu : env M var},
      is_branch_of B T -> is_on_branch F B T -> [[ M # [] # mu '|= Ctx.to_form (get_context B T) ]] ->
      [[ M # [] # mu '|= F ]].
  Proof using Type.
    intros ????? hbranchof honbranch hsat.
    have h := Ctx.in_interp hsat.
    apply h, is_on_branch_in_context; auto.
  Qed.
End Tableaux.

Arguments tree {_ _ _ _}.
Arguments symbols {_ _ _ _}.
Arguments is_tableau_closed {_ _ _ _ _} _ _.
Arguments is_tableau_satisfiable {_ _ _ _} _.
Arguments exists_satisfied_branch {_ _ _ _} _ _ _.
Arguments preserves_function_symbols {_ _ _ _} _ _.

(** ** Expansion rules *)

(** We denote [T |> T'] when a [Tableau] [T] can be expanded to a tableau [T']. *)
Reserved Notation "T |> T'" (at level 30, right associativity).
Section ExpansionRules.
  Context `{set_nat : set nat} {pred func var : Atom} (sko : Skolemization_ pred func var).

  Let Term := Term func var.
  Let Form := Form pred func var.
  Let Tableau := Tableau sko.

  (** By convention, we expand a tableau on the left side for unary rules. *)
  Inductive ExpansionStep : Tableau -> Tableau -> Prop :=
  | expansion_NegNeg :
    forall (T T' : Tableau) (B : Branch) (F : Form),
      is_branch_of B T -> is_on_branch (Neg (Neg F)) B T ->
      expand_tableau_branch sko (Some (Ctx.singleton F)) None B T = Some T' -> T |> T'

  | expansion_NegOr :
    forall (T T' : Tableau) (B : Branch) (F1 F2 : Form),
      is_branch_of B T -> is_on_branch (Neg (Or F1 F2)) B T ->
      expand_tableau_branch sko (Some (Ctx.mk [Neg F1 ; Neg F2])) None B T = Some T' -> T |> T'

  | expansion_Or :
    forall (T T' : Tableau) (B : Branch) (F1 F2 : Form),
      is_branch_of B T -> is_on_branch (Or F1 F2) B T ->
      expand_tableau_branch sko (Some (Ctx.singleton F1)) (Some (Ctx.singleton F2)) B T =
        Some T' -> T |> T'

  | expansion_All :
    forall (T T' : Tableau) (B : Branch) (F : Form) (x : var),
      is_branch_of B T -> is_on_branch (All F) B T ->
      expand_tableau_branch sko (Some (Ctx.singleton F{0 \to Free x})) None B T = Some T' ->
      T |> T'

  | expansion_NegAll :
    forall (T T' : Tableau) (B : Branch) (F : Form) (t : Term)
      (hsko : sko t (Neg (All F)) (symbols T) (fv (get_context B T))
                (function_symbols (get_all_formulas T)) = true),
      is_branch_of B T -> is_on_branch (Neg (All F)) B T ->
      expand_tableau_branch__aux (Some (Ctx.singleton (Neg F{0 \to t}))) None B T = Some (tree T') ->
      symbols T' = add_symbol (symbol sko hsko) (Neg (All F)) (symbols T) ->
      T |> T'
  where "T |> T'" := (ExpansionStep T T').

  (** A [Sequence] is an [ExpansionSequence] if every neighbouring [Tableau] are related
      by an [ExpansionStep]. *)
  Definition is_expansion_sequence (s : Sequence sko) : Prop :=
    forall (i : nat) (T T' : Tableau),
      s.(i) = Some T -> s.(S i) = Some T' -> T |> T'.

  Lemma is_expansion_sequence_nil :
    is_expansion_sequence [].
  Proof using Type.
    intros ??? contra. rewrite nth_error_nil in contra; easy.
  Qed.

  Lemma is_expansion_sequence_singleton :
    forall (T : Tableau),
      is_expansion_sequence [T].
  Proof using Type.
    intros ???? contra0 contra; destruct i; [inversion contra|].
    cbn in contra0; rewrite nth_error_nil in contra0; easy.
  Qed.

  (** A sequence is a tableau proof if there it is an expansion sequence s.t. the first
      tableau of the sequence has a simple node labelled by this list of formulas and the
      last is closed under a substitution [sigma]. *)
  Definition is_tableau_proof (Gamma : Ctx) (sigma : Substitution var Term) (s : Sequence sko) : Prop :=
    is_expansion_sequence s /\
      hd_error s = Some (mkTableau sko Gamma) /\
      is_tableau_closed (last s (mkLeaf sko)) sigma.

  (** A list of formulas have a tableau if there exists a sequence that is a tableau proof *)
  Definition hasTableau (Gamma : Ctx) (sigma : Substitution var Term) : Prop :=
    exists (s : Sequence sko), is_tableau_proof Gamma sigma s.
End ExpansionRules.

Arguments ExpansionStep {_ _ _ _} _ _.
Arguments is_expansion_sequence {_ _ _ _} _.
Notation "T |> T'" := (ExpansionStep T T').

(** ** Soundness *)

(** In this section, we show that this definition of tableaux is sound, i.e., if list of formulas
    [Neg F :: Gamma] has a tableau, then [Gamma |= F]. *)
Section Soundness.
  Context `{set_nat : set nat} {pred func var : Atom} (sko : Skolemization_ pred func var).

  Let Term := Term func var.
  Let Form := Form pred func var.
  Let Tableau := Tableau sko.

  (** First, we show that the last tableau of a proof cannot be satisfiable. *)
  Lemma hasTableau_not_satisfiable :
    forall (M : Model pred func) (Gamma : Ctx) (sigma : Substitution var Term) (s : Sequence sko),
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
      satisfiable. We could even show the stronger property that there exists a model satisfying
      all the consecutive tableaux of the expansion. *)

  (** We start by showing that applying an [ExpansionStep] on a satisfiable tableau keeps
      satisfiability. *)
  Lemma satisfiable_expansion_satisfiable :
    forall (T T' : Tableau),
      is_tableau_satisfiable T -> (T |> T') ->
      is_tableau_satisfiable T'.
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
      intros [hnF | contra].
      + now apply (is_on_satisfiable_branch sko hbranchof hcontains H).
      + cbn in contra; apply contra; now intro.

    (* Case: [Neg (Or F1 F2)] *)
    - destruct hsat as (M & hsat). exists M; intro mu. specialize (hsat mu).
      eapply is_satisfiable_extend; eauto. left.
      intros [hF1 | hnnF ].
      + apply hF1; intro.
        apply (is_on_satisfiable_branch sko hbranchof hcontains H); now left.
      + apply hnnF; intros [hF2 | contra].
        * apply hF2; intro.
          apply (is_on_satisfiable_branch sko hbranchof hcontains H); now right.
        * apply contra. now intro.

    (* Case: [Or F1 F2] *)
    - destruct hsat as (M & hsat). exists M; intro mu. specialize (hsat mu).
      eapply is_satisfiable_extend; eauto.
      intro hinterp; have [hF1 | hF2] := is_on_satisfiable_branch sko hbranchof hcontains hinterp.
      + left; cbn. intros [hnF1 | contra]; try easy. apply contra; now intro.
      + right; cbn. intros [hnF2 | contra]; try easy. apply contra; now intro.

    (* Case: [All F] *)
    - destruct hsat as (M & hsat). exists M; intro mu. specialize (hsat mu).
      eapply is_satisfiable_extend; eauto. left.
      intros [hnF | contra].
      + have hall := is_on_satisfiable_branch sko hbranchof hcontains H.
        apply hnF, instantiate_imply_all; auto.
        now cbn.
      + cbn in contra; apply contra; now intro.

    (* Case: [Neg (All F)] *)
    - destruct hsat as (M & hsat0).
      destruct (is_sko_sound hsko M) as (interp & hinterpsko & hinterp).
      exists (ReplacementModel M interp); intro mu.
      eapply is_satisfiable_extend_gen with (M := M) (M' := ReplacementModel M interp)
                                            (f := fun x => x); eauto.
      + intros G hin hinterp'; apply hinterp; auto.
        intros f hin'; eapply GetFunctSymbols_in; eauto.
      + intro hinterp'; left; cbn. intros [ hnF | contra ].
        * apply hnF, hinterpsko.
          -- intros f hin;
               change (set_in f (function_symbols F)) with
               (set_in f (function_symbols (Neg (All F)))) in hin.
             eapply GetFunctSymbols_in; eauto.
             eapply in_get_ctx_in_all_formulas; eauto.
             eapply is_on_branch_in_context; eauto.
          -- eapply is_on_satisfiable_branch; eauto.
        * apply contra; now intro.
  Qed.

  (** By induction, it directly implies that if the first tableau of an expansion sequence
      is satisfied, then all the successive tableaux are satisfied. *)
  Lemma satisfiable_tableau_satisfiable_expansion_sequence :
    forall (seq : Sequence sko) (T : Tableau),
      is_expansion_sequence seq -> hd_error seq = Some T -> is_tableau_satisfiable T ->
      forall (i : nat) (T' : Tableau),
        seq.(i) = Some T' ->
        is_tableau_satisfiable T'.
  Proof using set_nat.
    intros seq T hisseq e hsat i. induction i as [|i' IHi']; intros T' e'.
    - rewrite nth_error_0 e in e'. injection e' => <- //.
    - have [T0 eT0] : exists (T0 : Tableau), seq.(i') = Some T0.
      { have hlt := nth_error_Some' _ _ _ e'.
        exists (nth i' seq T). apply nth_error_nth'. lia. }
      specialize (IHi' T0 eT0). eapply satisfiable_expansion_satisfiable; eauto.
  Qed.

  (** This allows us to deduce the the soundness theorem. *)
  Theorem hasTableau_sound :
    forall (sigma : Substitution var Term) (Gamma : Ctx) (F : Form),
      isClosed (Neg F :: Gamma) ->
      hasTableau sko (Neg F :: Gamma) sigma -> Gamma |= F.
  Proof using Type.
    intros ??? hclosedGamma (sequence & hproof).
    rewrite models_iff. intros M. left. intro hsat.
    have hsat' : forall (mu : env M var),
        interpret_form M [] mu (ls_to_form (Neg F :: Gamma)).
    { intro mu; change [[ M # [] # mu '|= ls_to_form (Neg F :: Gamma) ]].
      rewrite (isClosed_interp_form_env_eq _ _ _ _ (empty_env M var)); auto.
      rewrite isClosedList_isClosedFormList //. }

    (* Step 1: of course, as we have a tableau, there is always an unsatisfiable branch *)
    have hnsat := hasTableau_not_satisfiable _ _ _ _ hproof.

    (* But the first tableau of the sequence is satisfiable. *)
    have htab : is_tableau_satisfiable (mkTableau sko (Neg F :: Gamma)).
    { exists M. intro mu. exists []. split.
      - apply is_branch_of_nil.
      - apply hsat'. }
    destruct hproof as (hisseq & e & hclosed).

    (* Step 2: it means that the whole sequence is satisfiable. *)
    have htabsat := satisfiable_tableau_satisfiable_expansion_sequence
                      sequence (mkTableau sko (Neg F :: Gamma)) hisseq e htab.

    (* Step 3: in fact, even the last tableau of the sequence is satisfiable. *)
    specialize (htabsat (#|sequence| - 1)).
    have [T' eT'] : exists (T' : Tableau), sequence.(#|sequence| - 1) = Some T'.
    { destruct (sequence.(#|sequence| - 1)) eqn:elast.
      - exists t; auto.
      - exfalso. rewrite nth_error_None in elast.
        have hlt : 0 < #|sequence|.
        { eapply nth_error_Some'. rewrite nth_error_0. exact e. }
        lia. }
    specialize (htabsat T' eT'). destruct htabsat as (M' & htabsat').
    specialize (htabsat' (subst_to_env M' sigma)). destruct htabsat' as (B & hisbranch & hsatB).
    specialize (hnsat M' B).
    have elast : last sequence (mkLeaf sko) = T'.
    { destruct sequence.
      - inversion e.
      - clear hisseq e hclosed hisbranch hnsat. generalize dependent t.
        induction sequence as [|T0 seq IHseq]; intros T eT.
        + cbn in eT |- *. injection eT => -> //.
        + apply IHseq; cbn in eT |- *. rewrite PeanoNat.Nat.sub_0_r //. }
    rewrite -elast in hisbranch. specialize (hnsat hisbranch).

    (* Step 4: contradiction! *)
    apply hnsat. rewrite elast //.
  Qed.
End Soundness.

Module ConcreteProofInstances.
  Export ConcreteSkolemizationInstances.

  Definition Tableau := @Tableau string string string.
End ConcreteProofInstances.

(** Exposing tactics to simplify manipulation of trees. *)
Module TreeTactics.
  Ltac infer_branch_infos :=
    match goal with
    | [ e : expand_tableau_branch ?sko ?l ?l' ?B ?T = Some ?T' |- _ ] =>
        let eexpand := fresh "eexpand" in
        have eexpand := expand_tableau_branch_Some__aux sko e
    | _ => idtac
    end;
    match goal with
    | [ hb : is_branch_of ?B ?T |- _ ] =>
        let T0 := fresh "T" in
        let hnl := fresh "hnleaf" in
        let hc := fresh "hchild" in
        have [ T0 [ hnl hc ] ] := is_branch_of_get_child_at hb;
        match goal with
        | [ e : expand_tableau_branch__aux (Some ?l) (Some ?l') B T = Some ?T' |- _ ] =>
            let hb' := fresh "hbranchof" in
            have hb' := is_branch_of_extend_left hb e;
            let hnb := fresh "hnbranchof" in
            have hnb := is_branch_of_extend_left' hb e;
            let hb' := fresh "hbranchof" in
            have hb' := is_branch_of_extend_right hb e
        | [ e : expand_tableau_branch__aux (Some ?l) None B T = Some ?T' |- _ ] =>
            let T := fresh "T" in
            let hnl := fresh "hnleaf" in
            let er := fresh "erepl" in
            have [ T [ hnl er ] ] := replace_expand_Left hb;
            let hb' := fresh "hbranchof" in
            have hb' := is_branch_of_extend_left hb e;
            let hnb := fresh "hnbranchof" in
            have hnb := is_branch_of_extend_left' hb e
        | [ e : expand_tableau_branch__aux (Some ?l) ?l' B T = Some ?T' |- _ ] =>
            let hb' := fresh "hbranchof" in
            have hb' := is_branch_of_extend_left hb e;
            let hnb := fresh "hnbranchof" in
            have hnb := is_branch_of_extend_left' hb e
        | [ e : expand_tableau_branch__aux ?l (Some ?l') B T = Some ?T' |- _ ] =>
            let hb' := fresh "hbranchof" in
            have hb' := is_branch_of_extend_right hb e
        | [ e : expand_tableau_branch__aux None None B T = Some ?T' |- _ ] =>
            let hb' := fresh "hbranchof" in
            have hb' := is_branch_of_extend_None hb e
        | _ => idtac
        end
    | _ => fail 0 "No inferable data on branches from this context"
    end.

  Ltac infer_ctx_infos :=
    match goal with
    | [ hb : is_branch_of ?B ?T, e : get_context ?B ?T = ?Gamma |- _ ] =>
        match goal with
        | [ eexp : expand_tableau_branch__aux (Some ?l) ?l' B T = Some ?T' |- _ ] =>
            let ectx := fresh "ectx" in
            have ectx := get_context_extend_left hb eexp e
        | _ => idtac
        end;
        match goal with
        | [ eexp : expand_tableau_branch__aux ?l (Some ?l') B T = Some ?T' |- _ ] =>
            let ectx := fresh "ectx" in
            have ectx := get_context_extend_right hb eexp e
        | _ => idtac
        end
    | _ => idtac
    end;
    match goal with
    | [ hb : is_branch_of ?B ?T |- _ ] =>
        match goal with
        | [ hb' : is_branch_of ?B' T |- _ ] =>
            match goal with
            | [ ne : B <> B', e : replace_child B' T ?T' = Some ?T0 |- _ ] =>
                let ectx := fresh "ectx" in
                have ectx := get_context_replace_child_oth hb hb' ne e
            | _ => idtac
            end
        | _ => idtac
        end
    | _ => idtac
    end.

  Ltac infer_replace_child_infos :=
    match goal with
    | [ hb : is_branch_of ?B ?T |- _ ] =>
        match goal with
        | [ hb' : is_branch_of ?B' T |- _ ] =>
            match goal with
            | [ ne : B <> B', e : replace_child B' T ?T' = Some ?T0 |- _ ] =>
                let hb0 := fresh "hbranchof" in
                let ectx := fresh "ectx" in
                have hb0 := is_branch_of_replace_child_oth hb hb' ne e;
                have ectx := get_context_replace_child_oth hb hb' ne e
            | _ => fail 0 "Cannot infer replacement infos in this context: either [B <> B'] is
                          not in the context or there are no replace_child equations in it"
            end
        | _ => fail 0 "Cannot infer replacement infos in this context: only 1 is_branch_of in
                      the context"
        end
    | _ => fail 0 "Cannot infer replacement infos in this context: no is_branch_of in the context"
    end.
End TreeTactics.
