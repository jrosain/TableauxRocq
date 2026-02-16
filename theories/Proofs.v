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

  Let Form := Form pred func var.

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

  Definition EmptyBranch : Branch := [].

  (** A [Branch] [is_branch_of] a [TableauTree] whenever the list of branching steps describes
      a path from the root of the [TableauTree] to a node without children. *)
  Inductive is_branch_of : Branch -> TableauTree -> Prop :=
  | is_branch_of_nil : forall (Gamma : list Form), is_branch_of EmptyBranch (Node Leaf Gamma Leaf)
  | is_branch_of_left :
    forall (T1 T2 : TableauTree) (Gamma : list Form) (B : Branch),
      is_branch_of B T1 -> is_branch_of (Left :: B) (Node T1 Gamma T2)
  | is_branch_of_right :
    forall (T1 T2 : TableauTree) (Gamma : list Form) (B : Branch),
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
    forall (Gamma : list Form) (T1 T2 : TableauTree), is_subbranch_of EmptyBranch (Node T1 Gamma T2)
  | is_subbranch_of_left :
    forall (T1 T2 : TableauTree) (Gamma : list Form) (B : Branch),
      is_subbranch_of B T1 -> is_subbranch_of (Left :: B) (Node T1 Gamma T2)
  | is_subbranch_of_right :
    forall (T1 T2 : TableauTree) (Gamma : list Form) (B : Branch),
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
      {left_forms right_forms : option (list Form)},
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
    forall (Gamma : list Form) (T1 T1' T2 : TableauTree) (B : Branch)
      (left_forms right_forms : option (list Form)),
      expand_tableau_branch__aux left_forms right_forms B T1 = Some T1' ->
      expand_tableau_branch__aux left_forms right_forms (Left :: B) (Node T1 Gamma T2) =
        Some (Node T1' Gamma T2).
  Proof using Type. intros ??????? e; cbn; rewrite e //. Qed.

  Lemma expand_tableau_branch_right :
    forall (Gamma : list Form) (T1 T2 T2' : TableauTree) (B : Branch)
      (left_forms right_forms : option (list Form)),
      expand_tableau_branch__aux left_forms right_forms B T2 = Some T2' ->
      expand_tableau_branch__aux left_forms right_forms (Right :: B) (Node T1 Gamma T2) =
        Some (Node T1 Gamma T2').
  Proof using Type. intros ??????? e; cbn; rewrite e //. Qed.

  Lemma is_branch_of_extend_left :
    forall {T T' : TableauTree} {B : Branch} {l : list Form} {l' : option (list Form)},
      is_branch_of B T -> expand_tableau_branch__aux (Some l) l' B T = Some T' ->
      is_branch_of (B ++ [Left]) T'.
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
    forall {T T' : TableauTree} {B : Branch} {l : list Form} {l' : option (list Form)},
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
    forall {T T' : TableauTree} {B : Branch} {l : option (list Form)} {l' : list Form},
      is_branch_of B T -> expand_tableau_branch__aux l (Some l') B T = Some T' ->
      is_branch_of (B ++ [Right]) T'.
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
    forall (T T' : TableauTree) (B B' : Branch) (l l' : option (list Form)),
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
  Fixpoint get_label (B : Branch) (T : TableauTree) : option (list Form) :=
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
    forall {B : Branch} {T T0 : TableauTree} (T' : TableauTree) {l : list Form},
      is_branch_of B T -> expand_tableau_branch__aux (Some l) None B T = Some T0 ->
      exists T'', T'' <> Leaf /\ replace_child B T T'' = replace_child (B ++ [Left]) T0 T'.
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
    forall {B : Branch} {T T0 : TableauTree} (T1 T2 : TableauTree) {l l' : option (list Form)},
      expand_tableau_branch__aux l l' B T = Some T0 ->
      (T' <- replace_child (B ++ [Left]) T T1;
       replace_child (B ++ [Right]) T' T2) =
      (T' <- replace_child (B ++ [Left]) T0 T1;
       replace_child (B ++ [Right]) T' T2).
  Proof using Type.
    intros B; induction B as [|b B IHB]; intros ?????? e.
    - destruct T; try easy; cbn in *.
      destruct T3, T4; try easy.
      now injection e => <-.
    - destruct b, T; cbn in *; try easy.
      + destruct (expand_tableau_branch__aux l l' B T3) eqn:eexpand; try easy.
        injection e => <-; cbn in *.
        specialize (IHB T3 t T1 T2 l l' eexpand).
        destruct (replace_child (B ++ [Left]) T3 T1),
          (replace_child (B ++ [Left]) t T1); try easy;
          rewrite IHB //.
        rewrite -IHB //.
      + destruct (expand_tableau_branch__aux l l' B T4) eqn:eexpand; try easy.
        injection e => <-; cbn in *.
        specialize (IHB T4 t T1 T2 _ _ eexpand).
        destruct (replace_child (B ++ [Left]) T4 T1),
          (replace_child (B ++ [Left]) t T1); try easy;
          rewrite IHB //.
        rewrite -IHB //.
  Qed.

  Lemma replace_child_Node :
    forall {B : Branch} {T : TableauTree} (T1 T2 : TableauTree) (Gamma : list Form),
      is_branch_of B T -> get_label B T = Some Gamma ->
      replace_child B T (Node T1 Gamma T2) =
        (T' <- replace_child (B ++ [Left]) T T1;
         replace_child (B ++ [Right]) T' T2).
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
      is_branch_of (B ++ b :: B') T0 -> b <> b' -> replace_child (B ++ [b']) T T' = Some T0 ->
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
  Fixpoint get_context (B : Branch) (T : TableauTree) : list Form :=
    match B, T with
    | [], Node Leaf Gamma Leaf => Gamma
    | Left :: B, Node T1 Gamma _ => (get_context B T1 ++ Gamma)
    | Right :: B, Node _ Gamma T2 => (get_context B T2 ++ Gamma)
    | _, _ => []
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
        destruct b; cbn; apply in_or_app; now right.
    - destruct b, T; cbn in *; try easy.
      + apply in_app_or in hin; destruct hin as [hin | hin].
        * apply in_or_app; left. now apply IHB.
        * apply in_or_app; now right.
      + apply in_app_or in hin; destruct hin as [hin | hin].
        * apply in_or_app; left. now apply IHB.
        * apply in_or_app; now right.
  Qed.

  (** Actually, a [Tableau] also keeps in memory the Skolem symbols introduced. *)
  Record Tableau :=
    { tree :> TableauTree
    ; symbols : sko_record sko }.

  Definition expand_tableau_branch (left_forms right_forms : option (list Form))
    (B : Branch) (T : Tableau) : option Tableau :=
    expand_tableau_branch__aux left_forms right_forms B T >>=
      (fun tree => Some {| tree := tree; symbols := symbols T |}).

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
      is_branch_of B T /\ [[ M # [] # mu '|= ls_to_form (get_context B T) ]].

  (** A [Tableau] is said satisfiable if there exists a model such that for every free-variable
      environment, there is a branch that is satisfied. *)
  Definition is_tableau_satisfiable (T : Tableau) :=
    exists (M : Model pred func), forall (mu : env M var), exists_satisfied_branch M mu T.

  Definition mkTableau (Gamma : list Form) : Tableau :=
    {| tree := Node Leaf Gamma Leaf
    ;  symbols := empty_record |}.

  Definition mkLeaf : Tableau := {| tree := Leaf; symbols := empty_record |}.

  Lemma get_context_extend_left :
    forall {T T' : TableauTree} {B : Branch} {Gamma l : list Form} {l' : option (list Form)},
      is_branch_of B T -> expand_tableau_branch__aux (Some l) l' B T = Some T' ->
      get_context B T = Gamma -> get_context (B ++ [Left]) T' = (l ++ Gamma).
  Proof using Type.
    intro T. induction T; intros ????? hbranchof e eT; destruct B.
    - inversion e.
    - inversion e; destruct b; easy.
    - inversion hbranchof; subst. cbn in e.
      injection e => <- //.
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
    forall {T T' : TableauTree} {B : Branch} {Gamma l' : list Form} {l : option (list Form)},
      is_branch_of B T -> expand_tableau_branch__aux l (Some l') B T = Some T' ->
      get_context B T = Gamma -> get_context (B ++ [Right]) T' = (l' ++ Gamma).
  Proof using Type.
    intro T. induction T; intros ????? hbranchof e eT; destruct B.
    - inversion e.
    - inversion e. destruct b; easy.
    - inversion hbranchof; subst. cbn in e.
      injection e => <-; now cbn.
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

  Lemma get_context_extend_oth :
    forall (T T' : TableauTree) (B B' : Branch) (l l' : option (list Form)),
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
    forall {B : Branch} {T : Tableau} (l l' : option (list Form)),
      is_branch_of B T ->
      exists (T' : Tableau), expand_tableau_branch l l' B T = Some T'.
  Proof using Type.
    intros ? [T symbs ] ?? hbranchof; cbn in *. induction hbranchof; cbn.
    - exists {| tree := Node (mkOptionalNode l) Gamma (mkOptionalNode l'); symbols := symbs |}; auto.
    - destruct IHhbranchof as (T1' & eT1').
      destruct (expand_tableau_branch__aux l l' B T1); cbn in *.
      + exists {| tree := Node t Gamma T2; symbols := symbs |}; auto.
      + inversion eT1'.
    - destruct IHhbranchof as (T2' & eT2').
      destruct (expand_tableau_branch__aux l l' B T2); cbn in *.
      + exists {| tree := Node T1 Gamma t; symbols := symbs |}; auto.
      + inversion eT2'.
  Qed.

  Lemma expand_tableau_branch_Some__aux :
    forall {B : Branch} {T T' : Tableau} {l l' : option (list Form)},
      expand_tableau_branch l l' B T = Some T' ->
      expand_tableau_branch__aux l l' B T = Some (tree T').
  Proof using Type.
    intros ????? e; cbn in e.
    destruct (expand_tableau_branch__aux l l' B T); try easy.
    destruct T'; injection e => _ -> //.
  Qed.

  Lemma expand_tableau_branch_Some_symbs :
    forall {B : Branch} {T T' : Tableau} {l l' : option (list Form)},
      expand_tableau_branch l l' B T = Some T' ->
      symbols T = symbols T'.
  Proof using Type.
    intros ????? e; cbn in e.
    destruct (expand_tableau_branch__aux l l' B T); try easy.
    destruct T'; injection e => -> _ //.
  Qed.

  Lemma replace_expanded_child_not_branch_Left :
    forall {B : Branch} {T T0 T0' T' : TableauTree} {Gamma : list Form},
      is_branch_of B T -> T0' <> Leaf ->
      expand_tableau_branch__aux (Some Gamma) None B T = Some T0 ->
      replace_child (B ++ [Left]) T0 T0' = Some T' -> ~is_branch_of B T'.
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
    forall {B : Branch} {T T0 T0' T1 T1' T2 : TableauTree} {Gamma1 Gamma2 : list Form},
      is_branch_of B T -> T0' <> Leaf -> T1' <> Leaf ->
      expand_tableau_branch__aux (Some Gamma1) (Some Gamma2) B T = Some T0 ->
      replace_child (B ++ [Left]) T0 T0' = Some T1 ->
      replace_child (B ++ [Right]) T1 T1' = Some T2 -> ~is_branch_of B T2.
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
    forall {B : Branch} {T T0 T0' T' : TableauTree} {Gamma : list Form},
      is_branch_of B T -> T0' <> Leaf ->
      expand_tableau_branch__aux (Some Gamma) None B T = Some T0 ->
      replace_child (B ++ [Left]) T0 T0' = Some T' -> ~is_subbranch_of (B ++ [Right]) T'.
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
  Lemma is_satisfiable_extend_gen :
    forall (M M' : Model pred func) (T T' : Tableau) (B : Branch) (l l' : option (list Form))
      (mu' : env M' var) (f : env M' var -> env M var),
      is_branch_of B T -> expand_tableau_branch__aux l l' B T = Some (tree T') ->
      (forall (F : Form), [[ M # [] # f mu' '|= F ]] ->
                     [[ M' # [] # mu' '|= F ]]) ->
      ([[ M # [] # (f mu') '|= ls_to_form (get_context B T) ]] ->
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
      + destruct l.
        * exists (B0 ++ [Left]); split; cbn.
          -- destruct (expand_tableau_branch__aux (Some l) l' B0 T) eqn:eT.
             ++ eapply is_branch_of_extend_left; eauto.
                injection e => <-; eauto.
             ++ inversion e.
          -- destruct (expand_tableau_branch__aux (Some l) l' B0 T) eqn:eT.
             ++ injection e => eT'. rewrite eT' in eT. erewrite get_context_extend_left; eauto.
                cbn. unfold interpret; rewrite (ls_to_form_app l (get_context B0 T) M' [] mu').
                cbn. intros [hl | hnB0]; auto. now apply hnB0, hcsv.
             ++ inversion e.
        * now cbn in hsatl.

      (* Case: the extension with the formulas on the right is satisfied. *)
      + destruct l'.
        * exists (B0 ++ [Right]); split; cbn.
          -- destruct (expand_tableau_branch__aux l (Some l0) B0 T) eqn:eT.
             ++ eapply is_branch_of_extend_right; eauto.
                injection e => <-; eauto.
             ++ inversion e.
          -- destruct (expand_tableau_branch__aux l (Some l0) B0 T) eqn:eT.
             ++ injection e => eT'; rewrite eT' in eT.
                erewrite get_context_extend_right; eauto.
                cbn; unfold interpret. rewrite (ls_to_form_app l0 (get_context B0 T) M' [] mu').
                cbn. intros [hl0 | hnB0]; auto. now apply hnB0, hcsv.
             ++ inversion e.

        * inversion hsatr.

      (* Case: the branch that was satisfied is not [B0]. *)
    - destruct (expand_tableau_branch__aux l l' B0 T) eqn:eT'.
      + injection e => <-. exists B; split.
        * apply is_branch_of_extend_oth with (T := T) (B := B0) (l := l) (l' := l'); auto.
        * cbn in *. rewrite -(get_context_extend_oth T t B0 B l l' hbranchof hbranchB); try easy.
          now apply hcsv.
      + inversion e.
  Qed.

  Lemma is_satisfiable_extend :
    forall (M : Model pred func) (mu : env M var) (T T' : Tableau) (B : Branch)
      (l l' : option (list Form)),
      is_branch_of B T -> expand_tableau_branch l l' B T = Some T' ->
      ([[ M # [] # mu '|= ls_to_form (get_context B T) ]] ->
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
      + destruct b; apply in_or_app; now right.
    - cbn. apply in_or_app; left. apply IHhonbranch. now inversion hbranchof.
    - cbn. apply in_or_app; left. apply IHhonbranch. now inversion hbranchof.
  Qed.

  Lemma in_context_is_on_branch :
    forall {T : Tableau} {B : Branch} {F : Form},
      is_branch_of B T -> F \in get_context B T -> is_on_branch F B T.
  Proof using Type.
    intros ??? hbranchof hin. induction hbranchof.
    - now apply is_on_branch_node.
    - cbn in hin; apply in_app_or in hin; destruct hin as [ hT1 | hG ].
      + now apply is_on_branch_left, IHhbranchof.
      + now apply is_on_branch_node.
    - cbn in hin; apply in_app_or in hin; destruct hin as [ hT2 | hG ].
      + now apply is_on_branch_right, IHhbranchof.
      + now apply is_on_branch_node.
  Qed.

  Lemma is_on_satisfiable_branch :
    forall {T : Tableau} {B : Branch} {F : Form} {M : Model pred func} {mu : env M var},
      is_branch_of B T -> is_on_branch F B T -> [[ M # [] # mu '|= ls_to_form (get_context B T) ]] ->
      [[ M # [] # mu '|= F ]].
  Proof using Type.
    intros ????? hbranchof honbranch hsat.
    have h := in_form_list_interp _ hsat.
    apply h, is_on_branch_in_context; auto.
  Qed.
End Tableaux.

Arguments tree {_ _ _ _}.
Arguments symbols {_ _ _ _}.
Arguments is_tableau_closed {_ _ _ _ _} _ _.
Arguments is_tableau_satisfiable {_ _ _ _} _.
Arguments exists_satisfied_branch {_ _ _ _} _ _ _.

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
      expand_tableau_branch__aux (Some [Neg F{0 \to t}]) None B T = Some (tree T') ->
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
  Definition is_tableau_proof (Gamma : list Form) (sigma : Substitution var Term) (s : Sequence sko) : Prop :=
    is_expansion_sequence s /\
      hd_error s = Some (mkTableau sko Gamma) /\
      is_tableau_closed (last s (mkLeaf sko)) sigma.

  (** A list of formulas have a tableau if there exists a sequence that is a tableau proof *)
  Definition hasTableau (Gamma : list Form) (sigma : Substitution var Term) : Prop :=
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
      intro hinterp'; left; cbn. intros [ hnF | contra ].
      + apply hnF, hinterpsko.
        eapply is_on_satisfiable_branch; eauto.
      + apply contra; now intro.
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
    forall (sigma : Substitution var Term) (Gamma : list Form) (F : Form),
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
