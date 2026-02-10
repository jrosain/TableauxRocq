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

  (** The [context] of a branch is the list of all the formulas of a branch. *)
  Fixpoint get_context (B : Branch) (T : TableauTree) : list Form :=
    match B, T with
    | [], Node Leaf Gamma Leaf => Gamma
    | Left :: B, Node T1 Gamma _ => (Gamma ++ get_context B T1)%list
    | Right :: B, Node _ Gamma T2 => (Gamma ++ get_context B T2)%list
    | _, _ => []
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

  Lemma get_context_extend_left :
    forall (T T' : TableauTree) (B : Branch) (Gamma l : list Form) (l' : option (list Form)),
      is_branch_of B T -> expand_tableau_branch__aux (Some l) l' B T = Some T' ->
      get_context B T = Gamma -> get_context (B ++ [Left])%list T' = (Gamma ++ l)%list.
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
    forall (T T' : TableauTree) (B : Branch) (Gamma l' : list Form) (l : option (list Form)),
      is_branch_of B T -> expand_tableau_branch__aux l (Some l') B T = Some T' ->
      get_context B T = Gamma -> get_context (B ++ [Right])%list T' = (Gamma ++ l')%list.
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
    forall {B : Branch} {T : Tableau_} (l l' : option (list Form)),
      is_branch_of B T ->
      exists (T' : Tableau_), expand_tableau_branch l l' B T = Some T'.
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
    forall {B : Branch} {T T' : Tableau_} {l l' : option (list Form)},
      expand_tableau_branch l l' B T = Some T' ->
      expand_tableau_branch__aux l l' B T = Some (tree T').
  Proof using Type.
    intros ????? e; cbn in e.
    destruct (expand_tableau_branch__aux l l' B T); try easy.
    destruct T'; injection e => _ -> //.
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
    forall (M M' : Model pred func) (T T' : Tableau_) (B : Branch) (l l' : option (list Form))
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
        * exists (B0 ++ [Left])%list; split; cbn.
          -- destruct (expand_tableau_branch__aux (Some l) l' B0 T) eqn:eT.
             ++ eapply is_branch_of_extend_left; eauto.
                injection e => <-; eauto.
             ++ inversion e.
          -- destruct (expand_tableau_branch__aux (Some l) l' B0 T) eqn:eT.
             ++ injection e => eT'. rewrite eT' in eT. erewrite get_context_extend_left; eauto.
                cbn. unfold interpret; rewrite (ls_to_form_app (get_context B0 T) l M' [] mu').
                cbn. intros [hnB0 | hl]; auto. now apply hnB0, hcsv.
             ++ inversion e.
        * now cbn in hsatl.

      (* Case: the extension with the formulas on the right is satisfied. *)
      + destruct l'.
        * exists (B0 ++ [Right])%list; split; cbn.
          -- destruct (expand_tableau_branch__aux l (Some l0) B0 T) eqn:eT.
             ++ eapply is_branch_of_extend_right; eauto.
                injection e => <-; eauto.
             ++ inversion e.
          -- destruct (expand_tableau_branch__aux l (Some l0) B0 T) eqn:eT.
             ++ injection e => eT'; rewrite eT' in eT.
                erewrite get_context_extend_right; eauto.
                cbn; unfold interpret. rewrite (ls_to_form_app (get_context B0 T) l0 M' [] mu').
                cbn. intros [hnB0 | hl0]; auto. now apply hnB0, hcsv.
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
    forall (M : Model pred func) (mu : env M var) (T T' : Tableau_) (B : Branch)
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
    forall (T : Tableau_) (B : Branch) (F : Form),
      is_branch_of B T -> is_on_branch F B T -> F \in get_context B T.
  Proof using Type.
    intros ??? hbranchof honbranch. induction honbranch.
    - destruct B; cbn in *.
      + inversion hbranchof; now subst.
      + destruct b; apply in_or_app; now left.
    - cbn. apply in_or_app; right. apply IHhonbranch. now inversion hbranchof.
    - cbn. apply in_or_app; right. apply IHhonbranch. now inversion hbranchof.
  Qed.

  Lemma is_on_satisfiable_branch :
    forall {T : Tableau_} {B : Branch} {F : Form} {M : Model pred func} {mu : env M var},
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
      expand_tableau_branch__aux (Some [Neg F{0 \to t}]) None B T = Some (tree T') ->
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
Arguments is_expansion_sequence {_ _ _ _} _.
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
        interpret_form_ M [] mu (ls_to_form (Neg F :: Gamma)).
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

  Definition Tableau := @Tableau_ string string string.
End ConcreteProofInstances.
