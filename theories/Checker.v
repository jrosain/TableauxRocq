(** * Reflect: sound and complete algorithm to "search" for tableaux proofs *)

From Tableaux Require Import Core.
From Tableaux Require Import ExtendedSyntax.

(** In this file, we implement a guided tableau proof-search procedure. It is named
    "guided" as the rules to apply and the substitution are given.

    It returns a boolean if the tableau is closed. We show that this procedure
    is sound, which makes it possible to output proof certificates from this
    algorithm. *)

(** ** 1. The algorithm *)

(** *** Data-structures *)

(** We start by giving a data structure that reflects the rules of [ExpansionStep]. *)
Inductive Rule : Type :=
| AlphaNegNeg : Form -> Rule
| AlphaNegOr : Form -> Rule
| BetaOr : Form -> Rule
| GammaAll : Form -> string -> Rule
| DeltaNegAll : Form -> Term -> Rule.

(** As we want a proof tree, we will take a tree of extended rules as an input of the algorithm.
    Unary rules can be implemented by ignoring the _2nd_ child of the tree. *)
Inductive RuleTree : Type :=
| Leaf : option (Form * Form) -> RuleTree
| Node : RuleTree -> Rule -> RuleTree -> RuleTree.

Definition mkTrivialClosure : RuleTree := Leaf None.

Definition mkClosure (F G : Form) : RuleTree :=
  Leaf (Some (F, G)).

Definition mkUnaryNode (rule : Rule) (T1 : RuleTree) : RuleTree :=
  Node T1 rule (Leaf None).

Definition mkBinaryNode (rule : Rule) (T1 T2 : RuleTree) : RuleTree :=
  Node T1 rule T2.

(** A small [Result] monad that stores the errors encountered. *)
Definition Result (A : Type) : Type := A * list string.

#[global] Instance Monad_Result : Monad Result :=
  {| ret := fun A x => (x, [])
  ;  bind A B r f :=
      let (x, s) := f (fst r) in
      (x, (snd r ++ s)%list) |}.

(** *** Utility functions *)

(** Printers *)

Definition pr_bool (b : bool) : string :=
  match b with
  | true => "true"
  | false => "false"
  end.

Fixpoint pr_term (t : Term) : string :=
  match t with
  | Bound n => "x@" ++ nat_to_string n
  | Free x => x
  | Fun f l => f ++ "(" ++ pr_list pr_term l ++ ")"
  end.

Fixpoint pr_form (F : Form) : string :=
  match F with
  | Bot => "$false"
  | Pred p l => p ++ "(" ++ pr_list pr_term l ++ ")"
  | Neg F => "~(" ++ pr_form F ++ ")"
  | Or F1 F2 => "(" ++ pr_form F1 ++ " | " ++ pr_form F2 ++ ")"
  | All F => "! (" ++ pr_form F ++ ")"
  end.

(** We abstract the context as a module in order to be able to easily swap the implementation.
    It is currently implemented as a list, but it would probably be better to use sets. *)
Module Ctx.
  Definition t := list Form.
  Definition eq : t -> t -> Prop := eq.
  Definition from_list (l : list Form) : t := l.
  Definition fv (Gamma : t) : SetOfString := fv Gamma.
  Definition existsb (pred : Form -> bool) (Gamma : t) : bool := List.existsb pred Gamma.
  Definition mem (F : Form) (Gamma : t) : bool := list_mem F Gamma.
  Definition In (F : Form) (Gamma : t) : Prop := F \in Gamma.
  Definition singleton (F : Form) : t := [F].
  Definition add (F : Form) (Gamma : t) : t := F :: Gamma.
  Definition elements (Gamma : t) : list Form := Gamma.
  Definition union (Gamma1 Gamma2 : t) : t := (Gamma1 ++ Gamma2)%list.
  Definition pr (Gamma : t) : string := "[" ++ pr_list pr_form Gamma ++ "]".

  Lemma mem_spec :
    forall (F : Form) (Gamma : t),
      mem F Gamma = true <-> In F Gamma.
  Proof. apply list_mem_spec. Qed.
End Ctx.

(** Returns true iff [Bot] is in the list. *)
Definition trivial_contradiction (Gamma : Ctx.t) : bool :=
  Ctx.existsb (fun F => eqb F Bot) Gamma.

Definition is_neg (F : Form) : bool :=
  match F with
  | Neg _ => true
  | _ => false
  end.

(** Returns true iff there exists two formulas [F] and [F'] such that
    [Neg P@[sigma] = P'@[sigma]] in [Gamma]. *)
Definition formula_contradiction (F G : Form) (Gamma : Ctx.t) (sigma : Substitution string Term): bool :=
  Ctx.mem F Gamma && Ctx.mem G Gamma &&
    (match F with
     | Neg F => negb (is_neg G) && eqb F@[sigma] G@[sigma]
     | _ => is_neg G && eqb (Neg F)@[sigma] G@[sigma]
     end).

Definition get_neg_neg (F : Form) : option Ctx.t :=
  match F with
  | Neg (Neg F) => Some (Ctx.singleton F)
  | _ => None
  end.

Definition get_or (F : Form) : option (Ctx.t * Ctx.t) :=
  match F with
  | Or F1 F2 => Some (Ctx.singleton F1, Ctx.singleton F2)
  | _ => None
  end.

Definition get_neg_or (F : Form) : option Ctx.t :=
  match F with
  | Neg (Or F1 F2) => Some (Ctx.add (Neg F1) (Ctx.singleton (Neg F2)))
  | _ => None
  end.

Definition get_all (F : Form) : option Form :=
  match F with
  | All F => Some F
  | _ => None
  end.

Definition get_neg_all (F : Form) : option Form :=
  match F with
  | Neg (All F) => Some (Neg F)
  | _ => None
  end.

(** *** The actual algorithm *)
Section GuidedTableauSearchAlgorithm.
  Context (sko : Skolemization).

  Record algo_result := { status: bool; symbs: sko_record sko }.

  Definition result := Result algo_result.

  Definition error (s : string) : result := ({| status := false; symbs := empty_record |}, [s]).

  Definition rule_wrapper {A : Type} (Gamma : Ctx.t) (F : Form) (err : string)
    (getter : Form -> option A) (action : A -> result) : result :=
    if negb (Ctx.mem F Gamma)
    then error ("Formula " ++ pr_form F ++ " not found in the context " ++
                  Ctx.pr Gamma)
    else
      match getter F with
      | None => error ("The formula " ++ pr_form F ++ " is not a " ++ err)
      | Some x => action x
      end.

  Definition SearchAlgorithm :=
    Ctx.t -> Substitution string Term -> sko_record sko -> RuleTree -> result.

  Definition closure_rule (search_contradiction : Ctx.t -> Substitution string Term -> bool)
    (Gamma : Ctx.t) (sigma : Substitution string Term) (symbols : sko_record sko) : result :=
    if search_contradiction Gamma sigma
    then ret {| status := true; symbs := symbols |}
    else error ("No trivial contradiction in the context: " ++
                  pr_list pr_form (Ctx.elements Gamma)@[sigma]).

  Definition alpha_rule (Gamma : Ctx.t) (sigma : Substitution string Term) (T : RuleTree)
    (record : sko_record sko) (F : Form) (getter : Form -> option Ctx.t) (err : string)
    (search : SearchAlgorithm)  :=
    rule_wrapper Gamma F err getter (fun l => search (Ctx.union l Gamma) sigma record T).

  Definition beta_rule (Gamma : Ctx.t) (sigma : Substitution string Term) (T1 T2 : RuleTree)
    (record : sko_record sko) (F : Form) (getter : Form -> option (Ctx.t * Ctx.t))
    (err : string) (search : SearchAlgorithm)  :=
    rule_wrapper Gamma F err getter
      (fun l =>
         r <- search (Ctx.union (fst l) Gamma) sigma record T1;
         if status r then search (Ctx.union (snd l) Gamma) sigma (symbs r) T2
         else ret r).

  Definition gamma_rule (Gamma : Ctx.t) (sigma : Substitution string Term) (T : RuleTree)
    (record : sko_record sko) (F : Form) (x : string) (getter : Form -> option Form)
    (err : string) (search : SearchAlgorithm)  :=
    rule_wrapper Gamma F err getter
      (fun F => search (Ctx.add (F{0 \to Free x}) Gamma) sigma record T).

  Definition delta_rule (Gamma : Ctx.t) (sigma : Substitution string Term) (T : RuleTree)
    (record : sko_record sko) (F : Form) (t : Term) (getter : Form -> option Form)
    (err : string) (search : SearchAlgorithm)  :=
    rule_wrapper Gamma F err getter
      (fun F0 => if sko t F record (Ctx.elements Gamma)
             then
               match get_symbol t with
               | None => error "This shouldn't ever happen."
               | Some f => search (Ctx.add (F0{0 \to t}) Gamma) sigma (add_symbol f F record) T
               end
             else
               error ("The term " ++ pr_term t ++ " is not a valid Skolem symbol in the context "
                        ++ Ctx.pr Gamma)).

  (** The guided proof-search is the following algorithm:
      - on a leaf: it tries to search for a closure [Bot] or [Neg Top] or a contradiction using
        the supplied substitution ; returns [false] if no closure rule can be found ;
      - on a node: it tries to apply the given rule on the given formula, and calls the
        algorithm recursively. *)
  Fixpoint GuidedTableauSearch__aux
    (Gamma : Ctx.t) (sigma : Substitution string Term)
    (record : sko_record sko) (tree : RuleTree) : result :=
    match tree with
    | Leaf None => closure_rule (fun Gamma _ => trivial_contradiction Gamma) Gamma sigma record

    | Leaf (Some (F, G)) => closure_rule (formula_contradiction F G) Gamma sigma record

    | Node T1 rule T2 =>

        let alpha_rule (F : Form) (getter : Form -> option Ctx.t) (err : string) :=
          alpha_rule Gamma sigma T1 record F getter err GuidedTableauSearch__aux in

        let beta_rule (F : Form) (getter : Form -> option (Ctx.t * Ctx.t)) (err : string) :=
          beta_rule Gamma sigma T1 T2 record F getter err GuidedTableauSearch__aux in

        let gamma_rule (F : Form) (x : string) (getter : Form -> option Form) (err : string) :=
          gamma_rule Gamma sigma T1 record F x getter err GuidedTableauSearch__aux in

        let delta_rule (F : Form) (t : Term) (getter : Form -> option Form) (err : string) :=
          delta_rule Gamma sigma T1 record F t getter err GuidedTableauSearch__aux in

        match rule with
        | AlphaNegNeg F => alpha_rule F get_neg_neg "double negation"
        | AlphaNegOr F => alpha_rule F get_neg_or "negated disjunction"

        | BetaOr F => beta_rule F get_or "disjunction"

        | GammaAll F x => gamma_rule F x get_all "universal formula"

        | DeltaNegAll F t => delta_rule F t get_neg_all "negated universal formula"
        end
    end.

  Definition GuidedTableauSearch (Gamma : list Form) (sigma : Substitution string Term)
    (tree : RuleTree) : result :=
    GuidedTableauSearch__aux (Ctx.from_list Gamma) sigma empty_record tree.
End GuidedTableauSearchAlgorithm.
Arguments status {_} _.
Arguments symbs {_} _.

(** ** 2. Soundness *)

(** *** Soundness of the getters *)

Lemma getter_neg_neg_sound :
  forall {F : Form} {l : list Form},
    get_neg_neg F = Some l -> exists (G : Form), l = [G] /\ F = Neg (Neg G).
Proof.
  intros ?? e. unfold get_neg_neg in e. destruct F; try inversion e.
  destruct F; try inversion e.
  exists F; auto.
Qed.

(** *** Soundness of the rules *)

Section RulesSoundness.
  Context {sko : Skolemization}.

  Lemma formula_contradiction_sound_neg :
    forall {F F' G : Form} {Gamma : Ctx.t} {sigma : Substitution string Term},
      formula_contradiction F G Gamma sigma = true -> F = Neg F' ->
      exists (P P' : Form), Ctx.In P Gamma /\ Ctx.In P' Gamma /\ P@[sigma] = (Neg P')@[sigma].
  Proof using Type.
    intros ????? ((hin & hin')%andb_prop & e)%andb_prop eF; unfold formula_contradiction in e;
      rewrite eF in e.
    apply andb_prop in e; destruct e as (h & e).
    rewrite eqbIsEq in e. exists F, G. rewrite !Ctx.mem_spec in hin, hin'; repeat split; auto.
    rewrite eF; cbn; now apply f_equal.
  Qed.

  Lemma formula_contradiction_sound_pos :
    forall {F G : Form} {Gamma : Ctx.t} {sigma : Substitution string Term},
      formula_contradiction F G Gamma sigma = true -> is_neg F = false ->
      exists (P P' : Form), Ctx.In P Gamma /\ Ctx.In P' Gamma /\ P@[sigma] = (Neg P')@[sigma].
  Proof using Type.
    intros ???? ((hin & hin')%andb_prop & e)%andb_prop eF; unfold formula_contradiction in e.
    have e' : (is_neg G && eqb (Neg F) @[ sigma] G @[ sigma])%bool = true.
    { destruct F; try inversion eF; auto. }
    clear e. apply andb_prop in e'; destruct e' as (h & e).
    rewrite eqbIsEq in e. exists G, F. rewrite !Ctx.mem_spec in hin, hin'; repeat split; auto.
  Qed.

  Lemma is_neg_dec :
    forall (F : Form), (exists (F' : Form), F = Neg F') \/ is_neg F = false.
  Proof using Type.
    intros F; destruct F; auto.
    left. now exists F.
  Qed.

  Lemma formula_contradiction_sound :
    forall {F G : Form} {Gamma : Ctx.t} {sigma : Substitution string Term},
      formula_contradiction F G Gamma sigma = true ->
      exists (P P' : Form), Ctx.In P Gamma /\ Ctx.In P' Gamma /\ P@[sigma] = (Neg P')@[sigma].
  Proof using Type.
    intros ???? e. destruct (is_neg_dec F) as [e0 | e0].
    - destruct e0 as (F' & eF). eapply formula_contradiction_sound_neg; eauto.
    - eapply formula_contradiction_sound_pos; eauto.
  Qed.

  Lemma trivial_contradiction_sound :
    forall (Gamma : Ctx.t),
      trivial_contradiction Gamma = true -> Ctx.In Bot Gamma.
  Proof using Type.
    intro Gamma; induction Gamma as [|F Fs IHFs]; cbn.
    - now intro.
    - intros [ e1 | e2 ]%Bool.orb_prop.
      + left. now rewrite eqbIsEq in e1.
      + specialize (IHFs e2). now right.
  Qed.

  Lemma rule_wrapper_sound :
    forall {A : Type} (Gamma : Ctx.t) (F : Form) (err : string)
      (getter : Form -> option A) (action : A -> result sko) (symbols : sko_record sko),
      rule_wrapper sko Gamma F err getter action = ret {| status := true; symbs := symbols |} ->
      exists (x : A),
        getter F = Some x /\ Ctx.In F Gamma /\ action x = ret {| status := true; symbs := symbols |}.
  Proof using Type.
    intros ??????? e. unfold rule_wrapper in e.
    destruct (negb (Ctx.mem F Gamma)) eqn:ein.
    - inversion e.
    - destruct (getter F) eqn:egetter.
      + rewrite Bool.negb_false_iff Ctx.mem_spec in ein. exists a; auto.
      + inversion e.
  Qed.

  Lemma alpha_rule_sound :
    forall {Gamma : Ctx.t} {sigma : Substitution string Term}
      {record record' : sko_record sko} {T : RuleTree} {F : Form} {err : string}
      {getter : Form -> option Ctx.t},
      alpha_rule sko Gamma sigma T record F getter err (GuidedTableauSearch__aux sko) =
        ret {| status := true; symbs := record' |} ->
      exists (l : Ctx.t),
        getter F = Some l /\ Ctx.In F Gamma /\
          GuidedTableauSearch__aux sko (Ctx.union l Gamma) sigma record T =
            ret {| status := true; symbs := record' |}.
  Proof using Type.
    intros ???????? e. unfold alpha_rule in e.
    now apply rule_wrapper_sound in e.
  Qed.

  Lemma beta_rule_sound :
    forall {Gamma : Ctx.t} {sigma : Substitution string Term}
      {record record' : sko_record sko} {T1 T2 : RuleTree} {F : Form} {err : string}
      {getter : Form -> option (Ctx.t * Ctx.t)},
      beta_rule sko Gamma sigma T1 T2 record F getter err (GuidedTableauSearch__aux sko) =
        ret {| status := true; symbs := record' |} ->
      exists (l1 l2 : Ctx.t) (symbols : sko_record sko),
        getter F = Some (l1, l2) /\ Ctx.In F Gamma /\
          GuidedTableauSearch__aux sko (Ctx.union l1 Gamma) sigma record T1 =
            ret {| status := true; symbs := symbols |} /\
          GuidedTableauSearch__aux sko (Ctx.union l2 Gamma) sigma symbols T2 =
            ret {| status := true; symbs := record' |}.
  Proof using Type.
    intros ????????? e. unfold beta_rule in e.
    apply rule_wrapper_sound in e. destruct e as ((l1 & l2) & eg & hin & hact).
    exists l1, l2; cbn[fst snd] in hact.
    destruct (GuidedTableauSearch__aux sko (Ctx.union l1 Gamma) sigma record T1); cbn in *.
    destruct a as (b & s). exists s; repeat split; cbn in *; destruct b; unfold ret in hact; cbn in *;
      auto.

    2,4: injection hact => _ _ contra; inversion contra.

    all: destruct (GuidedTableauSearch__aux sko (Ctx.union l2 Gamma) sigma s T2); cbn in *;
      destruct (status a); cbn in *; auto.

    all: injection hact => e _; apply app_eq_nil in e; destruct e as [el el']; subst; auto.
  Qed.

  Lemma gamma_rule_sound :
    forall {Gamma : Ctx.t} {sigma : Substitution string Term}
      {record record' : sko_record sko} {T : RuleTree} {F : Form} {x : string} {err : string}
      {getter : Form -> option Form},
      gamma_rule sko Gamma sigma T record F x getter err (GuidedTableauSearch__aux sko) =
        ret {| status := true; symbs := record' |} ->
      exists (G : Form),
        getter F = Some G /\ Ctx.In F Gamma /\
          GuidedTableauSearch__aux sko (Ctx.add (G{0 \to Free x}) Gamma) sigma record T =
            ret {| status := true; symbs := record' |}.
  Proof using Type.
    intros ????????? e. unfold gamma_rule in e.
    now apply rule_wrapper_sound in e.
  Qed.

  Lemma delta_rule_sound :
    forall {Gamma : Ctx.t} {sigma : Substitution string Term}
      {record record' : sko_record sko} {T : RuleTree} {F : Form} {t : Term} {err : string}
      {getter : Form -> option Form},
      delta_rule sko Gamma sigma T record F t getter err (GuidedTableauSearch__aux sko) =
        ret {| status := true; symbs := record' |} ->
      exists (f : string) (G : Form),
        getter F = Some G /\ F \in Gamma /\ sko t F record Gamma = true /\ get_symbol t = Some f /\
          GuidedTableauSearch__aux sko (G{0 \to t} :: Gamma) sigma (add_symbol f F record) T =
            ret {| status := true; symbs := record' |}.
  Proof using Type.
    intros ????????? e. unfold delta_rule in e.
    apply rule_wrapper_sound in e.
    destruct e as (G & eG & hin & e).
    destruct (sko t F record (Ctx.elements Gamma)) eqn:hsko; try inversion e.
    destruct (get_symbol t) eqn:esym; try inversion e.
    exists a, G; repeat split; auto.
  Qed.
End RulesSoundness.

(** To show the soundness of this algorithm, we proceed as follows:

    For every [RuleTree], we can craft a [Sequence] where each tableau of the sequence is
    obtained by applying the corresponding rule of the [RuleTree].

    Then, we show that (i) if the algorithm returns [ret true], then the _last_ tableau of
    the sequence is actually closed, and (ii) if the algorithm returns [ret true], then
    a _specific portion_ of the [Sequence] is an expansion sequence.

    In fact, this specific portion is the size of the [Sequence] returned by the algorithm
    that transforms a [RuleTree] into a [Sequence], and for the whole [RuleTree], it is
    the "single portion" starting at [0] of size [#|s|]. *)

(** *** Making a [Sequence] out of a [RuleTree]. *)
Section RuleTreeToSequence.
  Context (sko : Skolemization).

  Let Tableau := Tableau_ sko.

  (** Of course, making a [Sequence] out of a [RuleTree] is not always possible, e.g., when
    the formulas specified by the [Rule] is not of the right format. Hence, we work in the
    option monad. *)
  Fixpoint RuleTree_to_Sequence__aux (B : Branch) (T : Tableau) (R : RuleTree) :
    option (Sequence sko) :=
    match R with

    | Leaf _ => ret [T]

    | Node R1 r R2 =>
        match r with

        | AlphaNegNeg F =>
            Gamma <- get_neg_neg F;
            T' <- expand_tableau_branch sko (Some (Ctx.elements Gamma)) None B T;
            s <- RuleTree_to_Sequence__aux (B ++ [Left])%list T' R1;
            ret (T :: s)

        | AlphaNegOr F =>
            Gamma <- get_neg_or F;
            T' <- expand_tableau_branch sko (Some (Ctx.elements Gamma)) None B T;
            s <- RuleTree_to_Sequence__aux (B ++ [Left])%list T' R1;
            ret (T :: s)

        | BetaOr F =>
            Gammas <- get_or F;
            T' <- expand_tableau_branch sko (Some (Ctx.elements (fst Gammas)))
                   (Some (Ctx.elements (snd Gammas))) B T;
            s1 <- RuleTree_to_Sequence__aux (B ++ [Left])%list T' R1;
            s2 <- RuleTree_to_Sequence__aux (B ++ [Right])%list (last s1 (mkLeaf sko)) R2;
            ret (T :: s1 ++ s2)

        | GammaAll F x =>
            G <- get_all F;
            T' <- expand_tableau_branch sko (Some [G{0 \to Free x}]) None B T;
            s <- RuleTree_to_Sequence__aux (B ++ [Left])%list T' R1;
            ret (T :: s)

        | DeltaNegAll F t =>
            G <- get_neg_all F;
            f <- get_symbol t;
            T0 <- expand_tableau_branch__aux (Some [G{0 \to t}]) None B T;
            let T' := {| tree := T0; symbols := add_symbol f F (symbols T) |} in
            s <- RuleTree_to_Sequence__aux (B ++ [Left])%list T' R1;
            ret (T :: s)
        end
    end.

  (** The [Sequence] gotten from [RuleTree_to_Sequence] is never [nil]. *)
  Lemma RuleTree_to_Sequence_not_nil :
    forall {R : RuleTree} {B : Branch} {T : Tableau} {s : Sequence sko},
      RuleTree_to_Sequence__aux B T R = Some s -> s <> [].
  Proof using Type.
    intro R; induction R; intros ??? e; cbn in *.
    - injection e => <-; now intro.
    - destruct r; [destruct (get_neg_neg f) | destruct (get_neg_or f) | destruct (get_or f) |
                    destruct (get_all f) | destruct (get_neg_all f), (get_symbol t)];
        try easy.
      1,2,4,5:
          destruct (expand_tableau_branch__aux _ _ _ _);
          try easy; destruct (RuleTree_to_Sequence__aux _ _ _);
                    try easy; injection e => <-; now intro.
      destruct (expand_tableau_branch__aux _ _ _ _); try easy.
      destruct (RuleTree_to_Sequence__aux _ _ _); try easy.
      destruct (RuleTree_to_Sequence__aux _ _ _); try easy.
      injection e => <-; now intro.
  Qed.

  (** First, we show that [RuleTree_to_Sequence__aux] only affects the subtree starting at
      the branch [B] in [T]. *)
  Lemma RuleTree_to_Sequence_branch :
    forall {R : RuleTree} {B : Branch} {T : Tableau} {s : Sequence sko},
      is_branch_of B T -> RuleTree_to_Sequence__aux B T R = Some s ->
      exists (T'' : TableauTree), replace_child B T T'' = Some (tree (last s (mkLeaf sko))).
  Proof using Type.
    intros R. induction R as [ l | R1 IHR1 r R2 IHR2 ];
      intros ??? hbranchof e.

    - cbn in e. injection e => <-; cbn.
      have [ T'' eT'' ] := is_branch_of_get_child_at hbranchof.
      exists T''. now apply replace_child_get_child_at.

    (* TODO: factor out the boilerplate code *)
    - destruct r; cbn in e.

      + destruct (get_neg_neg f) eqn:ef; try easy.
        destruct (expand_tableau_branch__aux (Some (Ctx.elements t)) None B T) eqn:hexpand;
          try easy.
        destruct (RuleTree_to_Sequence__aux _ _ _) eqn:etree; try easy.
        have hbranchof0 := is_branch_of_extend_left hbranchof hexpand.
        injection e => <-.

        destruct (IHR1 (B ++ [Left])%list {| tree := t0; symbols := symbols T |}
                    s0 hbranchof0 etree) as (T'' & hreplace).
        rewrite last_cons.
        * eapply RuleTree_to_Sequence_not_nil; eauto.
        * rewrite -hreplace; eapply replace_expand_Left; eauto.

      + destruct (get_neg_or f) eqn:ef; try easy.
        destruct (expand_tableau_branch__aux (Some (Ctx.elements t)) None B T) eqn:hexpand;
          try easy.
        destruct (RuleTree_to_Sequence__aux _ _ _) eqn:etree; try easy.
        have hbranchof0 := is_branch_of_extend_left hbranchof hexpand.
        injection e => <-.

        destruct (IHR1 (B ++ [Left])%list {| tree := t0; symbols := symbols T |}
                    s0 hbranchof0 etree) as (T'' & hreplace).
        rewrite last_cons.
        * eapply RuleTree_to_Sequence_not_nil; eauto.
        * rewrite -hreplace; eapply replace_expand_Left; eauto.

      + destruct (get_or f) eqn:ef; try easy.
        destruct (expand_tableau_branch__aux (Some (Ctx.elements (fst p)))
                    (Some (Ctx.elements (snd p))) B T) eqn:hexpand; try easy.
        destruct (RuleTree_to_Sequence__aux _ _ _) eqn:etree1; try easy.
        destruct (RuleTree_to_Sequence__aux _ _ R2) eqn:etree2; try easy.

        (* We replace the _current_ node. To do so, we first get the two trees yielded by
           the induction hypotheses. *)
        have hbranchof1 := is_branch_of_extend_left hbranchof hexpand.
        have hbranchof2 := is_branch_of_extend_right hbranchof hexpand.
        have [Gamma eGamma] := is_subbranch_of_has_label hbranchof.
        revert etree1; set T0 := {| tree := t; symbols := symbols T |}; intro etree1.
        change (is_branch_of (B ++ [Left])%list T0) in hbranchof1.
        change (is_branch_of (B ++ [Right])%list T0) in hbranchof2.

        (* The tree that replaces the left child. *)
        destruct (IHR1 (B ++ [Left])%list T0 s0 hbranchof1 etree1)
          as (T1' & hreplace1).

        have hneq : (B ++ [Right])%list <> (B ++ [Left])%list.
        { clear. induction B; try easy.
          cbn; intro e; apply IHB; injection e => -> //. }
        have hbranchof2' := is_branch_of_replace_child_oth hbranchof2 hbranchof1 hneq hreplace1.

        (* The tree that replaces the right child. *)
        destruct (IHR2 (B ++ [Right])%list (last s0 (mkLeaf sko)) s1 hbranchof2' etree2)
          as (T2' & hreplace2).

        exists (Proofs.Node T1' Gamma T2').
        injection e => <-.

        rewrite replace_child_Node; auto.
        erewrite replace_child_sequence_expand; eauto.
        rewrite hreplace1; etransitivity; [now cbn|].
        rewrite hreplace2 app_comm_cons last_app //.
        eapply RuleTree_to_Sequence_not_nil; eauto.

      + destruct (get_all f) eqn:ef; try easy.
        destruct (expand_tableau_branch__aux _ _ _ _) eqn:hexpand;
          try easy.
        destruct (RuleTree_to_Sequence__aux _ _ _) eqn:etree; try easy.
        have hbranchof0 := is_branch_of_extend_left hbranchof hexpand.
        injection e => <-.

        destruct (IHR1 (B ++ [Left])%list {| tree := t; symbols := symbols T |}
                    s1 hbranchof0 etree) as (T'' & hreplace).
        rewrite last_cons.
        * eapply RuleTree_to_Sequence_not_nil; eauto.
        * rewrite -hreplace; eapply replace_expand_Left; eauto.

      + destruct (get_neg_all f) eqn:ef; try easy.
        destruct (get_symbol t) eqn:esymbol; try easy.
        destruct (expand_tableau_branch__aux _ _ _ _) eqn:hexpand;
          try easy.
        destruct (RuleTree_to_Sequence__aux _ _ _) eqn:etree; try easy.
        have hbranchof0 := is_branch_of_extend_left hbranchof hexpand.
        injection e => <-.

        destruct (IHR1 (B ++ [Left])%list {| tree := t0; symbols := add_symbol a f (symbols T) |}
                    s0 hbranchof0 etree) as (T'' & hreplace).
        rewrite last_cons.
        * eapply RuleTree_to_Sequence_not_nil; eauto.
        * rewrite -hreplace; eapply replace_expand_Left; eauto.
  Qed.

  (** Then, we can show that whenever the [GuidedTableauSearch__aux] algorithm finds a result,
      then the algorithm [RuleTree_to_Sequence__aux] converts the [RuleTree] to a [Sequence]
      successfully. *)
  Lemma GuidedTableauSearch_Some_RuleTree_to_Sequence_Some__aux :
    forall {Gamma : list Form} {sigma : Substitution string Term} {R : RuleTree}
      {B : Branch} {T : Tableau} {record record' : sko_record sko},
      GuidedTableauSearch__aux sko Gamma sigma record R = ret {| status := true; symbs := record' |} ->
      is_branch_of B T -> get_context B T = Gamma ->
      exists (s : Sequence sko) (T' : Tableau), RuleTree_to_Sequence__aux B T R = Some (s, T').
  Proof using Type.
    intros ??????? e hbranchof econ. generalize dependent Gamma. generalize dependent T.
    revert B record record'. induction R; intros B record record' T hbranchof Gamma e econ.

    (* Case: [Leaf] *)
    - exists [], T; auto.

    (* Case: [Node]. TODO: factor out the boilerplate code. *)
    - destruct r.

      (* Case: [AlphaNegNeg] *)
      + have [ l [ eget [ hin hnext ] ] ] := alpha_rule_sound e.
        have [ T0 hexpand ] :=
          is_branch_of_expand_tableau_branch sko (Some l) None hbranchof.
        have hbranchof0 :=
          is_branch_of_extend_left hbranchof
            (expand_tableau_branch_Some__aux sko hexpand).
        have esymbs := expand_tableau_branch_Some_symbs sko hexpand.
        have ectx := get_context_extend_left hbranchof
                       (expand_tableau_branch_Some__aux sko hexpand) econ.

        destruct (IHR1 (B ++ [Left])%list record record' T0 hbranchof0 (Ctx.union l Gamma) hnext ectx)
          as (s & T' & hseq).
        exists (T0 :: s), T'; cbn.
        rewrite eget (expand_tableau_branch_Some__aux sko hexpand) esymbs hseq.
        reflexivity.

      (* Case: [AlphaNegOr] *)
      + have [ l [ eget [ hin hnext ] ] ] := alpha_rule_sound e.
        have [ T0 hexpand ] :=
          is_branch_of_expand_tableau_branch sko (Some l) None hbranchof.
        have hbranchof0 :=
          is_branch_of_extend_left hbranchof
            (expand_tableau_branch_Some__aux sko hexpand).
        have esymbs := expand_tableau_branch_Some_symbs sko hexpand.
        have ectx := get_context_extend_left hbranchof
                       (expand_tableau_branch_Some__aux sko hexpand) econ.

        destruct (IHR1 (B ++ [Left])%list record record' T0 hbranchof0 (Ctx.union l Gamma) hnext ectx)
          as (s & T' & hseq).
        exists (T0 :: s), T'; cbn.
        rewrite eget (expand_tableau_branch_Some__aux sko hexpand) esymbs hseq.
        reflexivity.

      (* Case: [BetaOr] *)
      + have [ l [ l' [ symbs [ eget [ hin [ hnext1 hnext2 ] ] ] ] ] ] := beta_rule_sound e.
        have [ T0 hexpand ] :=
          is_branch_of_expand_tableau_branch sko (Some l) (Some l') hbranchof.
        have hbranchof1 :=
          is_branch_of_extend_left hbranchof
            (expand_tableau_branch_Some__aux sko hexpand).
        have hbranchof2 :=
          is_branch_of_extend_right hbranchof
            (expand_tableau_branch_Some__aux sko hexpand).
        have esymbs := expand_tableau_branch_Some_symbs sko hexpand.
        have ectx1 := get_context_extend_left hbranchof
                        (expand_tableau_branch_Some__aux sko hexpand) econ.
        have ectx2 := get_context_extend_right hbranchof
                        (expand_tableau_branch_Some__aux sko hexpand) econ.
        destruct (IHR1 (B ++ [Left])%list record symbs T0 hbranchof1 (Ctx.union l Gamma) hnext1 ectx1)
          as (s1 & T1 & hseq1).

        have [T1' ereplace] := RuleTree_to_Sequence_branch hbranchof1 hseq1.
        have ebranch : (B ++ [Right])%list <> (B ++ [Left])%list.
        { clear; induction B; cbn; intro; congruence. }

        have hbranchof2' : is_branch_of (B ++ [Right])%list T1.
        { eapply is_branch_of_replace_child_oth.
          3: eassumption.
          all: eauto. }
        have ectx2' : get_context (B ++ [Right])%list T0 = get_context (B ++ [Right])%list T1.
        { eapply get_context_replace_child_oth.
          3: eassumption.
          all: eauto.}
        rewrite ectx2' in ectx2; auto.

        destruct (IHR2 (B ++ [Right])%list symbs record' T1 hbranchof2'
                    (Ctx.union l' Gamma) hnext2 ectx2) as (s2 & T2 & hseq2).

        exists (T0 :: s1 ++ s2), T2; cbn.
        rewrite eget (expand_tableau_branch_Some__aux sko hexpand) esymbs hseq1 hseq2 //.

      (* Case: [GammaAll] *)
      + have [ F [ eget [ hin hnext ] ] ] := gamma_rule_sound e.
        have [ T0 hexpand ] :=
          is_branch_of_expand_tableau_branch sko (Some [opening_form 0 (Free s) F]) None hbranchof.
        have hbranchof0 :=
          is_branch_of_extend_left hbranchof
            (expand_tableau_branch_Some__aux sko hexpand).
        have esymbs := expand_tableau_branch_Some_symbs sko hexpand.
        have ectx := get_context_extend_left hbranchof
                       (expand_tableau_branch_Some__aux sko hexpand) econ.

        destruct (IHR1 (B ++ [Left])%list record record' T0 hbranchof0 (Ctx.add (F{0 \to Free s}) Gamma)
                    hnext ectx)
          as (seq & T' & hseq).
        exists (T0 :: seq), T'; cbn.
        rewrite eget (expand_tableau_branch_Some__aux sko hexpand) esymbs hseq.
        reflexivity.

      (* Case: [DeltaNegAll] *)
      + have [ f0 [ F [ eget [ hin [ hsko [ esymbol hnext ] ] ] ] ] ] := delta_rule_sound e.
        have [ T0 hexpand ] :=
          is_branch_of_expand_tableau_branch sko (Some [opening_form 0 t F]) None hbranchof.
        have hbranchof0 :=
          is_branch_of_extend_left hbranchof
            (expand_tableau_branch_Some__aux sko hexpand).
        have esymbs := expand_tableau_branch_Some_symbs sko hexpand.
        have ectx := get_context_extend_left hbranchof
                       (expand_tableau_branch_Some__aux sko hexpand) econ.

        destruct (IHR1 (B ++ [Left])%list (add_symbol f0 f record) record'
                       {| tree := T0; symbols := (add_symbol f0 f (symbols T0)) |}
                       hbranchof0 (Ctx.add (F{0 \to t}) Gamma) hnext ectx)
          as (seq & T' & hseq).
        exists ({| tree := T0; symbols := (add_symbol f0 f (symbols T0)) |} :: seq), T'; cbn.
        rewrite eget (expand_tableau_branch_Some__aux sko hexpand) esymbol esymbs hseq.
        reflexivity.
  Qed.

  (** Of course, we can make a [Sequence] out of a first tableau which has the single node [Gamma] *)
  Definition RuleTree_to_Sequence (Gamma : list Form) (R : RuleTree) : option (Sequence sko) :=
    RuleTree_to_Sequence__aux EmptyBranch (mkTableau sko Gamma) R.

  Lemma GuidedTableauSearch_Some_RuleTree_to_Sequence_Some :
    forall {Gamma : list Form} {sigma : Substitution string Term} {R : RuleTree}
      {record record' : sko_record sko},
      GuidedTableauSearch__aux sko Gamma sigma record R = ret {| status := true; symbs := record' |} ->
      exists (s : Sequence sko), RuleTree_to_Sequence Gamma R = Some s.
  Proof using Type.
    intros ????? e. cbn.
    have [ s [ T' es ] ] :
      exists s T', RuleTree_to_Sequence__aux EmptyBranch (mkTableau sko Gamma) R = ret (s, T').
    { eapply GuidedTableauSearch_Some_RuleTree_to_Sequence_Some__aux; eauto.
      apply is_branch_of_nil. }
    destruct R.
    - cbn. exists [mkTableau sko Gamma]; auto.
    - exists s. unfold RuleTree_to_Sequence. rewrite es; now cbn.
  Qed.

  Lemma GuidedTableauSearch_Some_RuleTree_to_Sequence_closed :
    forall {R : RuleTree} {sigma : Substitution string Term} {B : Branch}
      {T T' : Tableau} {record record' : sko_record sko} {s : Sequence sko},
      (forall (B : Branch),
          is_branch_of B T ->
          GuidedTableauSearch__aux sko (get_context B T) sigma record R =
            ret {| status := true; symbs := record' |}) ->
      RuleTree_to_Sequence__aux B T R = Some (s, T') ->
      is_tableau_closed T' sigma.
  Proof.
(*     intros R ??????? esrch eseq B' hbranchof'; specialize (esrch B'); *)
(*       revert sigma B T record record' s esrch eseq; induction R; *)
(*       intros ?????? esrch eseq. *)

(*     (* Case: [Leaf] *) *)
(*     - destruct o. *)
(*       + cbn in eseq, esrch. injection eseq => eT _; subst. *)
(*         destruct p as (F & G). *)
(*         unfold closure_rule in esrch; *)
(*           destruct (formula_contradiction F G (get_context B' T') sigma) eqn:econtr; *)
(*           try easy. *)
(*         right; eapply formula_contradiction_sound; eauto. *)
(*       + cbn in eseq, esrch. injection eseq => eT _; subst. *)
(*         unfold closure_rule in esrch; *)
(*           destruct (trivial_contradiction (get_context B' T')) eqn:econtr; *)
(*           try easy. *)
(*         left; eapply trivial_contradiction_sound; eauto. *)

(*     (* Case: [Node] *) *)
(*     - destruct r. *)

(*       (* Case: [AlphaNegNeg] *) *)
(*       + cbn in esrch. apply alpha_rule_sound in esrch; *)
(*           destruct esrch as (l & eget & hin & esrch); *)
(*           cbn in eseq. *)
(*         rewrite eget in eseq. *)
(*         destruct (expand_tableau_branch__aux _ _ _ _) eqn:et; try easy. *)
(*         destruct (RuleTree_to_Sequence__aux (B ++ [Left])%list _ _) eqn:eseq'; try easy. *)
(*         destruct p as (s1 & T1); cbn in eseq. injection eseq => eT' _. *)
(*         rewrite -eT' in hbranchof'.  *)
(*         * admit. *)
(*         * cbn in eseq. *)

(* cbn in esrch. apply alpha_rule_sound in esrch; *)
(*           destruct esrch as (l & eget & hin & esrch). *)
(*         cbn in eseq; rewrite eget in eseq. *)
(*         destruct (expand_tableau_branch__aux _ _ _ _) eqn:et; try easy. *)
(*         destruct (RuleTree_to_Sequence__aux (B ++ [Left])%list _ _) eqn:eseq'; try easy. *)
(*         destruct p as (s1 & T1); cbn in eseq. injection eseq => eT' _. *)
(*         rewrite -eT' in hbranchof'. *)
(*         have hbranchof0 := expand_tableau_branch_Some_is_branch_of et. *)
(*         have hbranchof1 : is_branch_of (B ++ [Left])%list {| tree := t; symbols := symbols T |} *)
(*           := is_branch_of_extend_left hbranchof0 et. *)
        
(*         exfalso. *)

(*         destruct (RuleTree_to_Sequence_branch hbranchof1 eseq') as *)
(*           (T0' & hreplace); cbn in *. *)
(*         have hbranchof' := is_branch_of_extend_left' hbranchof0 et. *)

        (* Contradiction: [B] cannot be a branch of [T1]. *)
        (* Actually, only true if [T0'] is not a leaf. (which is the case but eh) *)
  Admitted.

  Lemma GuidedTableauSearch_Some_Sequence_closed :
    forall {Gamma : list Form} {sigma : Substitution string Term} {R : RuleTree}
      {record record' : sko_record sko},
      GuidedTableauSearch__aux sko Gamma sigma record R = ret {| status := true; symbs := record' |} ->
      exists (s : Sequence sko), RuleTree_to_Sequence Gamma R = Some s /\
                              is_tableau_closed (last s (mkLeaf sko)) sigma.
  Proof.
    intros ????? e.
    have eGamma : get_context EmptyBranch (mkTableau sko Gamma) = Gamma by reflexivity.
    rewrite -eGamma in e. destruct R.
    
    - cbn; exists [mkTableau sko Gamma]; split; auto.
      eapply @GuidedTableauSearch_Some_RuleTree_to_Sequence_closed with
        (s := []) (B := EmptyBranch) (T := mkTableau sko Gamma) (R := Leaf o); auto.
      intros ? hbranchof. inversion hbranchof; subst; eauto; inversion H1.

    - have e' := e.
      apply @GuidedTableauSearch_Some_RuleTree_to_Sequence_Some__aux
        with (T := mkTableau sko Gamma) (B := EmptyBranch) in e.
      + destruct e as (s & T' & e). exists s; split.
        * unfold RuleTree_to_Sequence; rewrite e //.
        * eapply @GuidedTableauSearch_Some_RuleTree_to_Sequence_closed
            with (B := EmptyBranch) (T := mkTableau sko Gamma) (s := s); eauto.
          -- intros ? hbranchof; inversion hbranchof; subst; eauto; inversion H1.
          -- (* TODO: in this case, [last s (mkLeaf sko)] is exactly [T']. *) admit.
      + apply is_branch_of_nil.
      + reflexivity.
  Admitted.

  Lemma GuidedTableauSearch_Some_RuleTree_to_Sequence_is_expansion_sequence :
    forall {R : RuleTree} {sigma : Substitution string Term} {B : Branch}
      {T T' : Tableau} {record record' : sko_record sko} {s : Sequence sko},
      is_branch_of B T ->
      GuidedTableauSearch__aux sko (get_context B T) sigma record R =
        ret {| status := true; symbs := record' |} ->
      RuleTree_to_Sequence__aux B T R = Some (s, T') ->
      is_expansion_sequence s.
  Proof.
    intro R; induction R; intros ??????? hbranchof esrch eseq.

    - cbn in eseq; injection eseq => _ <-.
      apply is_expansion_sequence_nil.

    - destruct r.

      + have [ l [ eget [ hin esrch1 ] ] ] := alpha_rule_sound esrch.
        cbn in eseq; rewrite eget in eseq.
        destruct (expand_tableau_branch__aux _ _ _ _) eqn:hexpand; try easy.
        destruct (RuleTree_to_Sequence__aux _ _ _) eqn:eseq1; try easy.
        have ectx1 := get_context_extend_left hbranchof hexpand eq_refl.
        have hbranchof1 := is_branch_of_extend_left hbranchof hexpand.
        rewrite /Ctx.union /Ctx.elements in esrch1, ectx1; rewrite -ectx1 in esrch1.
        destruct p as (s1 & T1).
        specialize (IHR1 sigma (B ++ [Left])%list {| tree := t; symbols := symbols T |} T1
                      record record' s1 hbranchof1 esrch1 eseq1).
        

End RuleTreeToSequence.

(** *** The last tableau of the sequence is closed (TODO) *)

(** *** The sequence is an expansion sequence (TODO) *)

(** ** 3. Extended Syntax *)

Inductive ExtendedRule : Type :=
| AlphaNegNeg : Form -> ExtendedRule
| AlphaAnd : Form -> ExtendedRule
| AlphaNegOr : Form -> ExtendedRule
| AlphaNegImp : Form -> ExtendedRule
| BetaOr : Form -> ExtendedRule
| BetaImp : Form -> ExtendedRule
| BetaNegAnd : Form -> ExtendedRule
| BetaEqu : Form -> ExtendedRule
| BetaNegEqu : Form -> ExtendedRule
| GammaAll : Form -> string -> ExtendedRule
| GammaNegEx : Form -> string -> ExtendedRule
| DeltaEx : Form -> Term -> ExtendedRule
| DeltaNegAll : Form -> Term -> ExtendedRule.

(** TODO: we actually define this using the extended syntax *)

(* Lemma auxiliary_GuidedTableauSearch_sound : *)
(*   forall (sko : Skolemization) (Gamma : Ctx.t) (sigma : Substitution string Term) *)
(*     (record : sko_record sko) (tree : ExtendedRuleTree), *)
(*     GuidedTableauSearch__aux sko (Ctx.from_list Gamma) sigma record tree = ret true -> *)
(*     hasTableau_ sko Gamma record sigma. *)
(* Proof. *)
(*   intros ????? e. generalize dependent Gamma. revert record. induction tree as [|T1 IHT1 r T2 IHT2]; *)
(*     intros record Gamma e. *)

(*   (* Case: [Leaf] *) *)
(*   - destruct o; cbn in e. *)
(*     + destruct p as (F & G); unfold closure_rule in e; *)
(*         destruct (formula_contradiction F G Gamma sigma) eqn:e'; try inversion e. *)
(*       apply formula_contradiction_sound in e'; destruct e' as (P & P' & hin & hin' & e'). *)
(*       eapply hasTableauContr. *)
(*       * apply hin'. *)
(*       * apply hin. *)
(*       * now symmetry. *)
(*     + unfold closure_rule in e; destruct (trivial_contradiction Gamma) eqn:e'; try inversion e. *)
(*       apply trivial_contradiction_sound in e'; destruct e' as [hbot | hnegtop]. *)
(*       * now apply hasTableauBot. *)
(*       * cbn in hnegtop; eapply hasTableauNegNeg; eauto. *)
(*         apply hasTableauBot. now left. *)

(*   (* Case: [Node] *) *)
(*   - destruct r. *)

(*     (* The first 4 goals are alpha rules. *) *)
(*     1-4: cbn in e; apply alpha_rule_sound in e; destruct e as (l & e & hin & e1). *)

(*     (* The 5 next goals are beta rules. *) *)
(*     5-9: cbn in e; apply beta_rule_sound in e; destruct e as (l1 & l2 & e & hin & e1 & e2). *)

(*     (* The next two are gamma rules. *) *)
(*     10,11: cbn in e; apply gamma_rule_sound in e; destruct e as (G & e & hin & e1). *)

(*     (* The last two cases are delta rules. *) *)
(*     12,13: cbn in e; apply delta_rule_sound in e; *)
(*       destruct e as (g & G & e & hin & hsko & esym & e1). *)

(*     (* Case: [AlphaNegNeg] *) *)
(*     + apply getter_neg_neg_sound in e; destruct e as (G & el & e); rewrite e in hin. *)
(*       eapply hasTableauNegNeg; eauto. *)
(*       rewrite el in e1; now apply IHT1. *)

(*     (* Case: [AlphaAnd] *) *)
(*     + apply getter_and_sound in e; destruct e as (F1 & F2 & el & e); rewrite e in hin. *)
(*       eapply hasTableauNegOr; eauto. eapply hasTableauNegNeg. *)
(*       * now left. *)
(*       * eapply hasTableauNegNeg. *)
(*         -- do 2 right; now left. *)
(*         -- apply weakening with (Gamma := Gamma ,, F2 ,, F1). *)
(*            ++ cbn. symmetry; etransitivity; [apply f_equal; now rewrite -union_assoc union_idemp|]. *)
(*               etransitivity; [apply f_equal; *)
(*                               now rewrite -union_assoc (union_comm (fv F2) (fv F1)) union_assoc|]; *)
(*                 rewrite -!union_assoc union_idemp //. *)
(*            ++ do 2 apply extend_sub_ctx; do 2 apply cons_sub_ctx; apply sub_ctx_refl. *)
(*            ++ rewrite el in e1; now apply IHT1. *)

(*     (* Case: [AlphaNegOr] *) *)
(*     + apply getter_neg_or_sound in e; destruct e as (F1 & F2 & el & e); rewrite e in hin. *)
(*       eapply hasTableauNegOr; eauto. *)
(*       rewrite el in e1; now apply IHT1. *)

(*     (* Case: [AlphaNegImp] *) *)
(*     + apply getter_neg_imp_sound in e; destruct e as (F1 & F2 & el & e); rewrite e in hin. *)
(*       eapply hasTableauNegOr; eauto. *)
(*       eapply hasTableauNegNeg. *)
(*       * right; now left. *)
(*       * apply weakening with (Gamma := Gamma ,, Neg F2 ,, F1). *)
(*         ++ now cbn; rewrite -!union_assoc (union_comm (fv F1) (fv F2)); *)
(*              symmetry; etransitivity; [refine (f_equal (fun s => s \union fv Gamma) _); *)
(*                                        rewrite union_assoc union_idemp //|]. *)
(*         ++ do 2 apply extend_sub_ctx. apply cons_sub_ctx, sub_ctx_refl. *)
(*         ++ rewrite el in e1; now apply IHT1. *)

(*     (* Case: [BetaOr] *) *)
(*     + apply get_or_sound in e; destruct e as (F1 & F2 & el & e); rewrite e in hin. *)
(*       eapply hasTableauOr; eauto. *)
(*       * injection el => e2' e1'; rewrite e1' in e1; now apply IHT1. *)
(*       * injection el => e2' e1'; rewrite e2' in e2; now apply IHT2. *)

(*     (* Case: [BetaImp] *) *)
(*     + apply get_imp_sound in e; destruct e as (F1 & F2 & el & e); rewrite e in hin. *)
(*       eapply hasTableauOr; eauto. *)
(*       * injection el => e2' e1'; rewrite e1' in e1; now apply IHT1. *)
(*       * injection el => e2' e1'; rewrite e2' in e2; now apply IHT2. *)

(*     (* Case: [BetaNegAnd] *) *)
(*     + apply get_neg_and_sound in e; destruct e as (F1 & F2 & el & e); rewrite e in hin. *)
(*       eapply hasTableauNegNeg; eauto. *)
(*       have efv1 : @fv_list string _ _ (Gamma ,, Or (Neg F1) (Neg F2)) = *)
(*                     @fv_list string _ _ (Gamma ,, Neg (Neg (Or (Neg F1) (Neg F2)))) by reflexivity. *)
(*       have efv2 : @fv_list string _ _ (Gamma ,, Neg (Neg (Or (Neg F1) (Neg F2)))) = *)
(*                     @fv_list string _ _ Gamma by symmetry; apply fv_list_in. *)
(*       eapply hasTableauOr. *)
(*       * now left. *)
(*       * apply weakening with (Gamma := Gamma ,, Neg F1). *)
(*         -- now etransitivity; [cbn; unfold fv, fv_ctx; now rewrite -efv2|]. *)
(*         -- apply extend_sub_ctx, cons_sub_ctx, sub_ctx_refl. *)
(*         -- injection el => e2' e1'; rewrite e1' in e1; now apply IHT1. *)
(*       * apply weakening with (Gamma := Gamma ,, Neg F2). *)
(*         -- now etransitivity; [cbn; unfold fv, fv_ctx; now rewrite -efv2|]. *)
(*         -- apply extend_sub_ctx, cons_sub_ctx, sub_ctx_refl. *)
(*         -- injection el => e2' e1'; rewrite e2' in e2; now apply IHT2. *)

(*     (* Case: [BetaEqu] *) *)
(*     + apply get_equ_sound in e; destruct e as (F1 & F2 & el & e); rewrite e in hin. *)
(*       eapply hasTableauNegOr; eauto. *)
(*       do 2 (eapply hasTableauNegNeg; [right; now left|]). *)
(*       eapply hasTableauOr; [now left| |]. *)
(*       * eapply hasTableauOr; [do 2 right; now left| |]. *)
(*         -- apply weakening with (Gamma := Gamma ,, Neg F2 ,, Neg F1). *)
(*            ++ cbn; do 2 apply union_congl; *)
(*               symmetry; rewrite !union_assoc; etransitivity; *)
(*                 [apply f_equal; rewrite -!union_assoc union_idemp !union_assoc; *)
(*                  apply f_equal; rewrite -!union_assoc union_idemp !union_assoc; *)
(*                  apply f_equal; rewrite -!union_assoc union_idemp // |]. *)
(*               have efv : fv Gamma = ((fv F1 \union fv F2) \union (fv F2 \union fv F1)) \union @fv_list string _ _ Gamma. *)
(*               { rewrite (fv_list_in f); rewrite e; auto. } *)
(*               symmetry; etransitivity; [apply efv|]; rewrite -!union_assoc; *)
(*                 refine (f_equal (fun s => s \union fv Gamma) _). *)
(*               rewrite (union_comm (fv F1) (fv F2)); rewrite !union_assoc; do 2 f_equal; *)
(*                 do 2 rewrite (union_comm (fv F1) (fv F2)); rewrite -union_assoc union_idemp //. *)
(*            ++ do 2 apply extend_sub_ctx; do 4 apply cons_sub_ctx; apply sub_ctx_refl. *)
(*            ++ injection el => e2' e1'; rewrite e1' in e1; now apply IHT1. *)
(*         -- apply hasTableauContr with (P := F2) (P' := Neg F2); auto. *)
(*            ++ now left. *)
(*            ++ right; now left. *)
(*       * eapply hasTableauOr; [do 2 right; now left| |]. *)
(*         -- apply hasTableauContr with (P := F1) (P' := Neg F1); auto. *)
(*            ++ right; now left. *)
(*            ++ now left. *)
(*         -- apply weakening with (Gamma := Gamma ,, F1 ,, F2). *)
(*            ++ cbn; do 2 apply union_congl; *)
(*                 have efv : fv Gamma = ((fv F1 \union fv F2) \union (fv F2 \union fv F1)) \union @fv_list string _ _ Gamma. *)
(*               { rewrite (fv_list_in f); rewrite e; auto. } *)
(*               etransitivity; [apply efv|]; rewrite -!union_assoc; *)
(*                 refine (f_equal (fun s => s \union fv Gamma) _); symmetry; etransitivity; *)
(*                 [now do 2 (rewrite !union_assoc; apply f_equal; *)
(*                            rewrite -!union_assoc union_idemp)|]. *)
(*               rewrite union_comm !union_assoc; do 2 f_equal; *)
(*                 rewrite union_idemp -union_assoc union_idemp union_comm //. *)
(*            ++ do 2 apply extend_sub_ctx; do 4 apply cons_sub_ctx; apply sub_ctx_refl. *)
(*            ++ injection el => e2' e1'; rewrite e2' in e2; now apply IHT2. *)

(*     (* Case: [BetaNegEqu] *) *)
(*     + apply get_neg_equ_sound in e; destruct e as (F1 & F2 & el & e); rewrite e in hin. *)
(*       eapply hasTableauNegNeg; eauto. *)
(*       eapply hasTableauOr; [now left| |]. *)
(*       -- eapply hasTableauNegOr; [now left|]. *)
(*          eapply hasTableauNegNeg; [right; now left|]. *)
(*          apply weakening with (Gamma := Gamma ,, F1 ,, Neg F2). *)
(*          ++ cbn; rewrite -!union_assoc; apply union_congr; symmetry; etransitivity; *)
(*               [apply union_congr; rewrite !union_assoc union_idemp; do 2 apply union_congl; *)
(*                rewrite -!union_assoc union_idemp //|]. *)
(*             etransitivity; [apply union_congr; rewrite union_comm; apply union_congr; *)
(*                             apply union_congl; rewrite union_comm //|]; *)
(*               rewrite !union_assoc !union_idemp -!union_assoc union_idemp; *)
(*               rewrite (union_comm (fv F2 \union fv F1) (fv F2)) -!union_assoc union_idemp *)
(*                 !union_assoc union_idemp //. *)
(*          ++ apply sub_ctx_cong, extend_sub_ctx. do 3 apply cons_sub_ctx; apply sub_ctx_refl. *)
(*          ++ injection el => e2' e1'; rewrite e1' in e1; now apply IHT1. *)
(*       -- eapply hasTableauNegOr; [now left|]. *)
(*          eapply hasTableauNegNeg; [right; now left|]. *)
(*          apply weakening with (Gamma := Gamma ,, F2 ,, Neg F1). *)
(*          ++ cbn; rewrite -!union_assoc; apply union_congr; symmetry; etransitivity; *)
(*               [now do 3 (apply union_congr; rewrite !union_assoc union_idemp; *)
(*                          rewrite -!union_assoc)|]. *)
(*             etransitivity; [now do 2 (apply union_congr; *)
(*                                       rewrite union_comm -!union_assoc union_idemp)|]; *)
(*               rewrite !union_assoc !union_idemp union_comm //. *)
(*          ++ apply sub_ctx_cong, extend_sub_ctx. do 3 apply cons_sub_ctx; apply sub_ctx_refl. *)
(*          ++ injection el => e2' e1'; rewrite e2' in e2; now apply IHT2. *)

(*     (* Case: [GammaAll] *) *)
(*     + apply get_all_sound in e; rewrite e in hin. *)
(*       eapply hasTableauAll; eauto. *)

(*     (* Case: [GammaNegEx] *) *)
(*     + apply get_neg_ex_sound in e; destruct e as (F & eF & e); rewrite e in hin. *)
(*       subst. eapply hasTableauNegNeg; eauto. *)
(*       eapply hasTableauAll with (x := s); [now left|]. *)
(*       apply weakening with (Gamma := Gamma ,, (Neg F){0 \to Free s}). *)
(*       * have efv : fv Gamma = @fv_list string _ _ (Gamma ,, All (Neg F)). *)
(*         { now rewrite (fv_list_in (Neg (Neg (All (Neg F)))) Gamma). } *)
(*         now cbn; rewrite efv; cbn; symmetry; *)
(*           etransitivity; [rewrite union_comm -!union_assoc union_idemp union_comm //|]. *)
(*       * apply extend_sub_ctx, cons_sub_ctx, sub_ctx_refl. *)
(*       * now apply IHT1. *)

(*     (* Case: [DeltaEx] *) *)
(*     + apply get_ex_sound in e; rewrite !e in hin hsko. *)
(*       eapply hasTableauNegAll with (t := t) (Hsko := hsko); eauto. *)
(*       eapply hasTableauNegNeg; [now left|]. *)
(*       change (hasTableau_ sko ((Gamma ,, Neg (Neg G) {0 \to t}) ,, G {0 \to t}) *)
(*                 (add_symbol (symbol sko t hsko) (Neg (All (Neg G))) record) sigma). *)
(*       apply weakening with (Gamma := Gamma ,, G {0 \to t}). *)
(*       * cbn; rewrite -union_assoc union_idemp //. *)
(*       * apply extend_sub_ctx, cons_sub_ctx, sub_ctx_refl. *)
(*       * rewrite (symbol_sound hsko) in esym; injection esym => ->. *)
(*         rewrite -e; now apply IHT1. *)

(*     (* Case: [DeltaNegAll] *) *)
(*     + apply get_neg_all_sound in e; destruct e as (F & eF & e); rewrite e in hin hsko. *)
(*       eapply hasTableauNegAll with (t := t) (Hsko := hsko); eauto. *)
(*       rewrite (symbol_sound hsko) in esym; injection esym => ->. *)
(*       rewrite -e; rewrite eF in e1; now apply IHT1. *)
(* Qed. *)


(* (** *** The [Leaf] Case *) *)
(* Lemma trivial_contradiction_sound : *)
(*   forall (Gamma : Con.t), *)
(*     trivial_contradiction Gamma = true -> *)
(*     Con.In Bot Gamma \/ Con.In [[ ENeg ETop ]] Gamma. *)
(* Proof using Type. *)
(*   intro Gamma; induction Gamma as [|F Fs IHFs]; cbn. *)
(*   - now intro. *)
(*   - intros [ [e1 | e2]%Bool.orb_prop | e3]%Bool.orb_prop. *)
(*     + do 2 left. now rewrite eqbIsEq in e1. *)
(*     + right. left. now rewrite eqbIsEq in e2. *)
(*     + specialize (IHFs e3). destruct IHFs. *)
(*       * left. now right. *)
(*       * right. now right. *)
(* Qed. *)

(* (** *** Soundness of rule wrapper *) *)
(* Lemma rule_wrapper_sound : *)
(*   forall {A : Type} (Gamma : Con) (F : Form) (err : string) (getter : Form -> option A) *)
(*     (action : A -> Result bool), *)
(*     rule_wrapper Gamma F err getter action = ret true -> *)
(*     exists (x : A), getter F = Some x /\ F \in Gamma /\ action x = ret true. *)
(* Proof. *)
(*   intros ?????? e. unfold rule_wrapper in e. *)
(*   destruct (negb (mem_ctx F Gamma)) eqn:ein. *)
(*   - inversion e. *)
(*   - destruct (getter F) eqn:egetter. *)
(*     + rewrite Bool.negb_false_iff mem_ctx_in_ctx in ein. now exists a. *)
(*     + inversion e. *)
(* Qed. *)

(* (** *** alpha rules *) *)
(* Lemma alpha_rule_sound : *)
(*   forall (sko : Skolemization) (Gamma : Con) (sigma : Substitution string Term) *)
(*     (record : sko_record sko) (T : ExtendedRuleTree) (F : Form) (err : string) *)
(*     (getter : Form -> option (list Form)), *)
(*     alpha_rule sko Gamma sigma T record F getter err (GuidedTableauSearch__aux sko) = ret true -> *)
(*     exists (l : list Form), getter F = Some l /\ F \in Gamma /\ *)
(*                          GuidedTableauSearch__aux sko (List.app l Gamma) sigma record T = ret true. *)
(* Proof. *)
(*   intros ???????? e. unfold alpha_rule in e. *)
(*   now apply rule_wrapper_sound in e. *)
(* Qed. *)

(* (** *** alpha-rules getters *) *)
(* Lemma getter_neg_neg_sound : *)
(*   forall (F : Form) (l : list Form), *)
(*     get_neg_neg F = Some l -> exists (G : Form), l = [G] /\ F = Neg (Neg G). *)
(* Proof. *)
(*   intros ?? e. unfold get_neg_neg in e. destruct F; try inversion e. *)
(*   destruct F; try inversion e. *)
(*   now exists F. *)
(* Qed. *)

(* Lemma getter_and_sound : *)
(*   forall (F : Form) (l : list Form), *)
(*     get_and F = Some l -> exists (F1 F2 : Form), l = [F1 ; F2] /\ F = Neg (Or (Neg F1) (Neg F2)). *)
(* Proof. *)
(*   intros ?? e. unfold get_and in e. destruct F eqn:eF; try inversion e. *)
(*   destruct f eqn:ef; try inversion e. *)
(*   destruct f0_1 eqn:f1; try inversion e. *)
(*   destruct f0_2 eqn:f2; try inversion e. *)
(*   exists f0, f3; auto. *)
(* Qed. *)

(* Lemma getter_neg_or_sound : *)
(*   forall (F : Form) (l : list Form), *)
(*     get_neg_or F = Some l -> exists (F1 F2 : Form), l = [Neg F2 ; Neg F1] /\ F = Neg (Or F1 F2). *)
(* Proof. *)
(*   intros ?? e. unfold get_neg_or in e. destruct F eqn:eF; try inversion e. *)
(*   unfold Utils.bind in e. *)
(*   have h : exists F1 F2, get_or f = Some ([F1], [F2]). *)
(*   { destruct (get_or f) eqn:ef; try inversion e. *)
(*     destruct f; try inversion ef. cbn in ef. now exists f1, f2. } *)
(*   destruct h as (F1 & F2 & h). rewrite h in e. *)
(*   cbn in e. exists F1, F2; split. *)
(*   - now injection e => ->. *)
(*   - destruct f; try inversion h; auto. *)
(* Qed. *)

(* Lemma getter_neg_imp_sound : *)
(*   forall (F : Form) (l : list Form), *)
(*     get_neg_imp F = Some l -> exists (F1 F2 : Form), l = [F1 ; Neg F2] /\ F = Neg (Or (Neg F1) F2). *)
(* Proof. *)
(*   intros ?? e. unfold get_neg_imp in e. destruct F eqn:eF; try inversion e. *)
(*   destruct f eqn:ef; try inversion e. *)
(*   destruct f0_1 eqn:ef1; try inversion e. *)
(*   now exists f0, f0_2. *)
(* Qed. *)

(* (** *** beta rules *) *)
(* Lemma beta_rule_sound : *)
(*   forall (sko : Skolemization) (Gamma : Con) (sigma : Substitution string Term) *)
(*     (record : sko_record sko) (T1 T2 : ExtendedRuleTree) (F : Form) (err : string) *)
(*     (getter : Form -> option (list Form * list Form)), *)
(*     beta_rule sko Gamma sigma T1 T2 record F getter err (GuidedTableauSearch__aux sko) = ret true -> *)
(*     exists (l1 l2 : list Form), *)
(*       getter F = Some (l1, l2) /\ F \in Gamma /\ *)
(*         GuidedTableauSearch__aux sko (List.app l1 Gamma) sigma record T1 = ret true /\ *)
(*         GuidedTableauSearch__aux sko (List.app l2 Gamma) sigma record T2 = ret true. *)
(* Proof. *)
(*   intros ????????? e. unfold beta_rule in e. *)
(*   apply rule_wrapper_sound in e. destruct e as ((l1 & l2) & eg & hin & hact). *)
(*   exists l1, l2; repeat split; auto; unfold bind in hact; cbn in hact. *)

(*   all: destruct (GuidedTableauSearch__aux sko (l1 ++ Gamma)%list sigma record T1); cbn in *; *)
(*     destruct b; unfold ret in hact; cbn in *. *)

(*   2,4: injection hact => _ contra; inversion contra. *)

(*   all: destruct (GuidedTableauSearch__aux sko (l2 ++ Gamma)%list sigma record T2); cbn in *; *)
(*     destruct b; cbn in *. *)

(*   2,4: injection hact => _ contra; inversion contra. *)

(*   all: injection hact => e; apply app_eq_nil in e; destruct e as [el el']. *)

(*   - now rewrite el. *)
(*   - now rewrite el'. *)
(* Qed. *)

(* (** *** beta-rules getters *) *)

(* Lemma get_or_sound : *)
(*   forall (F : Form) (l : list Form * list Form), *)
(*     get_or F = Some l -> exists (F1 F2 : Form), l = ([F1], [F2]) /\ F = Or F1 F2. *)
(* Proof. *)
(*   intros ?? e. destruct F eqn:eF; cbn in *; try inversion e. *)
(*   now exists f1, f2. *)
(* Qed. *)

(* Lemma get_imp_sound : *)
(*   forall (F : Form) (l : list Form * list Form), *)
(*     get_imp F = Some l -> exists (F1 F2 : Form), l = ([Neg F1], [F2]) /\ F = Or (Neg F1) F2. *)
(* Proof. *)
(*   intros ?? e. destruct F eqn:eF; cbn in *; try inversion e. *)
(*   destruct f1 eqn:ef1; try inversion e. *)
(*   now exists f, f2. *)
(* Qed. *)

(* Lemma get_neg_and_sound : *)
(*   forall (F : Form) (l : list Form * list Form), *)
(*     get_neg_and F = Some l -> exists (F1 F2 : Form), l = ([Neg F1], [Neg F2]) /\ F = Neg (Neg (Or (Neg F1) (Neg F2))). *)
(* Proof. *)
(*   intros ?? e. destruct F eqn:eF; cbn in *; try inversion e. *)
(*   destruct f eqn:ef; cbn in *; try inversion e. *)
(*   destruct f0 eqn:ef0; cbn in *; try inversion e. *)
(*   destruct f1_1 eqn:ef1_1; cbn in *; try inversion e. *)
(*   destruct f1_2 eqn:ef1_2; cbn in *; try inversion e. *)
(*   now exists f1, f2. *)
(* Qed. *)

(* Lemma get_equ_sound : *)
(*   forall (F : Form) (l : list Form * list Form), *)
(*     get_equ F = Some l -> exists (F1 F2 : Form), l = ([Neg F1 ; Neg F2], [F2 ; F1]) /\ *)
(*                                              F = Neg (Or (Neg (Or (Neg F1) F2)) (Neg (Or (Neg F2) F1))). *)
(* Proof. *)
(*   intros ?? e. destruct F eqn:eF; cbn in *; try inversion e. *)
(*   destruct f eqn:ef; cbn in *; try inversion e. *)
(*   destruct f0_1; cbn in *; try inversion e. *)
(*   destruct f0_2; cbn in *; try inversion e. *)
(*   destruct f0_1; cbn in *; try inversion e. *)
(*   destruct f0_1_1; cbn in *; try inversion e. *)
(*   destruct f0_2; cbn in *; try inversion e. *)
(*   destruct f0_2_1; cbn in *; try inversion e. *)
(*   destruct (eqb f0_1_1 f0_2_2) eqn:ef0; *)
(*     destruct (eqb f0_2_1 f0_1_2) eqn:ef1; cbn in e; try inversion e. *)
(*   rewrite !eqbIsEq in ef0, ef1. subst. *)
(*   exists f0_2_2, f0_1_2; split; auto. *)
(* Qed. *)

(* Lemma get_neg_equ_sound : *)
(*   forall (F : Form) (l : list Form * list Form), *)
(*     get_neg_equ F = Some l -> *)
(*     exists (F1 F2 : Form), l = ([Neg F2 ; F1], [Neg F1 ; F2]) /\ *)
(*                         F = Neg (Neg (Or (Neg (Or (Neg F1) F2)) (Neg (Or (Neg F2) F1)))). *)
(* Proof. *)
(*   intros ?? e. destruct F eqn:eF; try inversion e. *)
(*   have e0 : exists l0, get_equ f = Some l0. { destruct (get_equ f) eqn:eequ; [now exists p|inversion H0]. } *)
(*   destruct e0 as (l0 & el0). *)
(*   have el0' := get_equ_sound _ _ el0. destruct el0' as (F1 & F2 & el0' & eF'). *)
(*   rewrite el0 el0' in H0. exists F1, F2; split. *)
(*   - now injection H0 => <-. *)
(*   - now apply f_equal. *)
(* Qed. *)

(* (** *** Gamma rules *) *)

(* Lemma gamma_rule_sound : *)
(*   forall (sko : Skolemization) (Gamma : Con) (sigma : Substitution string Term) *)
(*     (record : sko_record sko) (T : ExtendedRuleTree) (F : Form) (x : string) (err : string) *)
(*     (getter : Form -> option Form), *)
(*     gamma_rule sko Gamma sigma T record F x getter err (GuidedTableauSearch__aux sko) = ret true -> *)
(*     exists (G : Form), getter F = Some G /\ F \in Gamma /\ *)
(*                          GuidedTableauSearch__aux sko (G{0 \to Free x} :: Gamma) sigma record T = ret true. *)
(* Proof. *)
(*   intros ????????? e. unfold gamma_rule in e. *)
(*   now apply rule_wrapper_sound in e. *)
(* Qed. *)

(* (** *** Gamma rules getters *) *)

(* Lemma get_all_sound : *)
(*   forall (F G : Form), *)
(*     get_all F = Some G -> F = All G. *)
(* Proof. *)
(*   intros ?? e. destruct F eqn:eF; cbn in *; try inversion e; auto. *)
(* Qed. *)

(* Lemma get_neg_ex_sound : *)
(*   forall (F G : Form), *)
(*     get_neg_ex F = Some G -> exists (H : Form), G = Neg H /\ F = Neg (Neg (All (Neg H))). *)
(* Proof. *)
(*   intros ?? e. destruct F eqn:eF; cbn in *; try inversion e. *)
(*   destruct f eqn:ef; try inversion e. *)
(*   destruct f0 eqn:ef0; try inversion e. *)
(*   destruct f1 eqn:ef1; try inversion e. *)
(*   now exists f2. *)
(* Qed. *)

(* (** *** Delta rules *) *)

(* Lemma delta_rule_sound : *)
(*   forall (sko : Skolemization) (Gamma : Con) (sigma : Substitution string Term) *)
(*     (record : sko_record sko) (T : ExtendedRuleTree) (F : Form) (t : Term) (err : string) *)
(*     (getter : Form -> option Form), *)
(*     delta_rule sko Gamma sigma T record F t getter err (GuidedTableauSearch__aux sko) = ret true -> *)
(*     exists (f : string) (G : Form), *)
(*       getter F = Some G /\ F \in Gamma /\ sko t F (fv Gamma) record = true /\ get_symbol t = Some f /\ *)
(*         GuidedTableauSearch__aux sko (G{0 \to t} :: Gamma) sigma (add_symbol f F record) T = ret true. *)
(* Proof. *)
(*   intros ????????? e. unfold delta_rule in e. *)
(*   apply rule_wrapper_sound in e. *)
(*   destruct e as (G & eG & hin & e). *)
(*   destruct (sko t F (fv Gamma) record) eqn:hsko; try inversion e. *)
(*   destruct (get_symbol t) eqn:esym; try inversion e. *)
(*   exists a, G; repeat split; auto. *)
(* Qed. *)

(* (** *** Delta rules getters *) *)

(* Lemma get_ex_sound : *)
(*   forall (F G : Form), *)
(*     get_ex F = Some G -> F = Neg (All (Neg G)). *)
(* Proof. *)
(*   intros ?? e; destruct F eqn:eF; try inversion e. *)
(*   destruct f eqn:ef; try inversion e. *)
(*   now destruct f0 eqn:ef0; try inversion e. *)
(* Qed. *)

(* Lemma get_neg_all_sound : *)
(*   forall (F G : Form), *)
(*     get_neg_all F = Some G -> exists (H : Form), G = Neg H /\ F = Neg (All H). *)
(* Proof. *)
(*   intros ?? e; destruct F eqn:eF; try inversion e. *)
(*   destruct f eqn:ef; try inversion e. *)
(*   now exists f0. *)
(* Qed. *)

(* (** *** Soundness of the auxiliary algorithm. *) *)

(* Lemma auxiliary_GuidedTableauSearch_sound : *)
(*   forall (sko : Skolemization) (Gamma : Con) (sigma : Substitution string Term) *)
(*     (record : sko_record sko) (tree : ExtendedRuleTree), *)
(*     GuidedTableauSearch__aux sko Gamma sigma record tree = ret true -> *)
(*     hasTableau_ sko Gamma record sigma. *)
(* Proof. *)
(*   intros ????? e. generalize dependent Gamma. revert record. induction tree as [|T1 IHT1 r T2 IHT2]; *)
(*     intros record Gamma e. *)

(*   (* Case: [Leaf] *) *)
(*   - destruct o; cbn in e. *)
(*     + destruct p as (F & G); unfold closure_rule in e; *)
(*         destruct (formula_contradiction F G Gamma sigma) eqn:e'; try inversion e. *)
(*       apply formula_contradiction_sound in e'; destruct e' as (P & P' & hin & hin' & e'). *)
(*       eapply hasTableauContr. *)
(*       * apply hin'. *)
(*       * apply hin. *)
(*       * now symmetry. *)
(*     + unfold closure_rule in e; destruct (trivial_contradiction Gamma) eqn:e'; try inversion e. *)
(*       apply trivial_contradiction_sound in e'; destruct e' as [hbot | hnegtop]. *)
(*       * now apply hasTableauBot. *)
(*       * cbn in hnegtop; eapply hasTableauNegNeg; eauto. *)
(*         apply hasTableauBot. now left. *)

(*   (* Case: [Node] *) *)
(*   - destruct r. *)

(*     (* The first 4 goals are alpha rules. *) *)
(*     1-4: cbn in e; apply alpha_rule_sound in e; destruct e as (l & e & hin & e1). *)

(*     (* The 5 next goals are beta rules. *) *)
(*     5-9: cbn in e; apply beta_rule_sound in e; destruct e as (l1 & l2 & e & hin & e1 & e2). *)

(*     (* The next two are gamma rules. *) *)
(*     10,11: cbn in e; apply gamma_rule_sound in e; destruct e as (G & e & hin & e1). *)

(*     (* The last two cases are delta rules. *) *)
(*     12,13: cbn in e; apply delta_rule_sound in e; *)
(*       destruct e as (g & G & e & hin & hsko & esym & e1). *)

(*     (* Case: [AlphaNegNeg] *) *)
(*     + apply getter_neg_neg_sound in e; destruct e as (G & el & e); rewrite e in hin. *)
(*       eapply hasTableauNegNeg; eauto. *)
(*       rewrite el in e1; now apply IHT1. *)

(*     (* Case: [AlphaAnd] *) *)
(*     + apply getter_and_sound in e; destruct e as (F1 & F2 & el & e); rewrite e in hin. *)
(*       eapply hasTableauNegOr; eauto. eapply hasTableauNegNeg. *)
(*       * now left. *)
(*       * eapply hasTableauNegNeg. *)
(*         -- do 2 right; now left. *)
(*         -- apply weakening with (Gamma := Gamma ,, F2 ,, F1). *)
(*            ++ cbn. symmetry; etransitivity; [apply f_equal; now rewrite -union_assoc union_idemp|]. *)
(*               etransitivity; [apply f_equal; *)
(*                               now rewrite -union_assoc (union_comm (fv F2) (fv F1)) union_assoc|]; *)
(*                 rewrite -!union_assoc union_idemp //. *)
(*            ++ do 2 apply extend_sub_ctx; do 2 apply cons_sub_ctx; apply sub_ctx_refl. *)
(*            ++ rewrite el in e1; now apply IHT1. *)

(*     (* Case: [AlphaNegOr] *) *)
(*     + apply getter_neg_or_sound in e; destruct e as (F1 & F2 & el & e); rewrite e in hin. *)
(*       eapply hasTableauNegOr; eauto. *)
(*       rewrite el in e1; now apply IHT1. *)

(*     (* Case: [AlphaNegImp] *) *)
(*     + apply getter_neg_imp_sound in e; destruct e as (F1 & F2 & el & e); rewrite e in hin. *)
(*       eapply hasTableauNegOr; eauto. *)
(*       eapply hasTableauNegNeg. *)
(*       * right; now left. *)
(*       * apply weakening with (Gamma := Gamma ,, Neg F2 ,, F1). *)
(*         ++ now cbn; rewrite -!union_assoc (union_comm (fv F1) (fv F2)); *)
(*              symmetry; etransitivity; [refine (f_equal (fun s => s \union fv Gamma) _); *)
(*                                        rewrite union_assoc union_idemp //|]. *)
(*         ++ do 2 apply extend_sub_ctx. apply cons_sub_ctx, sub_ctx_refl. *)
(*         ++ rewrite el in e1; now apply IHT1. *)

(*     (* Case: [BetaOr] *) *)
(*     + apply get_or_sound in e; destruct e as (F1 & F2 & el & e); rewrite e in hin. *)
(*       eapply hasTableauOr; eauto. *)
(*       * injection el => e2' e1'; rewrite e1' in e1; now apply IHT1. *)
(*       * injection el => e2' e1'; rewrite e2' in e2; now apply IHT2. *)

(*     (* Case: [BetaImp] *) *)
(*     + apply get_imp_sound in e; destruct e as (F1 & F2 & el & e); rewrite e in hin. *)
(*       eapply hasTableauOr; eauto. *)
(*       * injection el => e2' e1'; rewrite e1' in e1; now apply IHT1. *)
(*       * injection el => e2' e1'; rewrite e2' in e2; now apply IHT2. *)

(*     (* Case: [BetaNegAnd] *) *)
(*     + apply get_neg_and_sound in e; destruct e as (F1 & F2 & el & e); rewrite e in hin. *)
(*       eapply hasTableauNegNeg; eauto. *)
(*       have efv1 : @fv_list string _ _ (Gamma ,, Or (Neg F1) (Neg F2)) = *)
(*                     @fv_list string _ _ (Gamma ,, Neg (Neg (Or (Neg F1) (Neg F2)))) by reflexivity. *)
(*       have efv2 : @fv_list string _ _ (Gamma ,, Neg (Neg (Or (Neg F1) (Neg F2)))) = *)
(*                     @fv_list string _ _ Gamma by symmetry; apply fv_list_in. *)
(*       eapply hasTableauOr. *)
(*       * now left. *)
(*       * apply weakening with (Gamma := Gamma ,, Neg F1). *)
(*         -- now etransitivity; [cbn; unfold fv, fv_ctx; now rewrite -efv2|]. *)
(*         -- apply extend_sub_ctx, cons_sub_ctx, sub_ctx_refl. *)
(*         -- injection el => e2' e1'; rewrite e1' in e1; now apply IHT1. *)
(*       * apply weakening with (Gamma := Gamma ,, Neg F2). *)
(*         -- now etransitivity; [cbn; unfold fv, fv_ctx; now rewrite -efv2|]. *)
(*         -- apply extend_sub_ctx, cons_sub_ctx, sub_ctx_refl. *)
(*         -- injection el => e2' e1'; rewrite e2' in e2; now apply IHT2. *)

(*     (* Case: [BetaEqu] *) *)
(*     + apply get_equ_sound in e; destruct e as (F1 & F2 & el & e); rewrite e in hin. *)
(*       eapply hasTableauNegOr; eauto. *)
(*       do 2 (eapply hasTableauNegNeg; [right; now left|]). *)
(*       eapply hasTableauOr; [now left| |]. *)
(*       * eapply hasTableauOr; [do 2 right; now left| |]. *)
(*         -- apply weakening with (Gamma := Gamma ,, Neg F2 ,, Neg F1). *)
(*            ++ cbn; do 2 apply union_congl; *)
(*               symmetry; rewrite !union_assoc; etransitivity; *)
(*                 [apply f_equal; rewrite -!union_assoc union_idemp !union_assoc; *)
(*                  apply f_equal; rewrite -!union_assoc union_idemp !union_assoc; *)
(*                  apply f_equal; rewrite -!union_assoc union_idemp // |]. *)
(*               have efv : fv Gamma = ((fv F1 \union fv F2) \union (fv F2 \union fv F1)) \union @fv_list string _ _ Gamma. *)
(*               { rewrite (fv_list_in f); rewrite e; auto. } *)
(*               symmetry; etransitivity; [apply efv|]; rewrite -!union_assoc; *)
(*                 refine (f_equal (fun s => s \union fv Gamma) _). *)
(*               rewrite (union_comm (fv F1) (fv F2)); rewrite !union_assoc; do 2 f_equal; *)
(*                 do 2 rewrite (union_comm (fv F1) (fv F2)); rewrite -union_assoc union_idemp //. *)
(*            ++ do 2 apply extend_sub_ctx; do 4 apply cons_sub_ctx; apply sub_ctx_refl. *)
(*            ++ injection el => e2' e1'; rewrite e1' in e1; now apply IHT1. *)
(*         -- apply hasTableauContr with (P := F2) (P' := Neg F2); auto. *)
(*            ++ now left. *)
(*            ++ right; now left. *)
(*       * eapply hasTableauOr; [do 2 right; now left| |]. *)
(*         -- apply hasTableauContr with (P := F1) (P' := Neg F1); auto. *)
(*            ++ right; now left. *)
(*            ++ now left. *)
(*         -- apply weakening with (Gamma := Gamma ,, F1 ,, F2). *)
(*            ++ cbn; do 2 apply union_congl; *)
(*                 have efv : fv Gamma = ((fv F1 \union fv F2) \union (fv F2 \union fv F1)) \union @fv_list string _ _ Gamma. *)
(*               { rewrite (fv_list_in f); rewrite e; auto. } *)
(*               etransitivity; [apply efv|]; rewrite -!union_assoc; *)
(*                 refine (f_equal (fun s => s \union fv Gamma) _); symmetry; etransitivity; *)
(*                 [now do 2 (rewrite !union_assoc; apply f_equal; *)
(*                            rewrite -!union_assoc union_idemp)|]. *)
(*               rewrite union_comm !union_assoc; do 2 f_equal; *)
(*                 rewrite union_idemp -union_assoc union_idemp union_comm //. *)
(*            ++ do 2 apply extend_sub_ctx; do 4 apply cons_sub_ctx; apply sub_ctx_refl. *)
(*            ++ injection el => e2' e1'; rewrite e2' in e2; now apply IHT2. *)

(*     (* Case: [BetaNegEqu] *) *)
(*     + apply get_neg_equ_sound in e; destruct e as (F1 & F2 & el & e); rewrite e in hin. *)
(*       eapply hasTableauNegNeg; eauto. *)
(*       eapply hasTableauOr; [now left| |]. *)
(*       -- eapply hasTableauNegOr; [now left|]. *)
(*          eapply hasTableauNegNeg; [right; now left|]. *)
(*          apply weakening with (Gamma := Gamma ,, F1 ,, Neg F2). *)
(*          ++ cbn; rewrite -!union_assoc; apply union_congr; symmetry; etransitivity; *)
(*               [apply union_congr; rewrite !union_assoc union_idemp; do 2 apply union_congl; *)
(*                rewrite -!union_assoc union_idemp //|]. *)
(*             etransitivity; [apply union_congr; rewrite union_comm; apply union_congr; *)
(*                             apply union_congl; rewrite union_comm //|]; *)
(*               rewrite !union_assoc !union_idemp -!union_assoc union_idemp; *)
(*               rewrite (union_comm (fv F2 \union fv F1) (fv F2)) -!union_assoc union_idemp *)
(*                 !union_assoc union_idemp //. *)
(*          ++ apply sub_ctx_cong, extend_sub_ctx. do 3 apply cons_sub_ctx; apply sub_ctx_refl. *)
(*          ++ injection el => e2' e1'; rewrite e1' in e1; now apply IHT1. *)
(*       -- eapply hasTableauNegOr; [now left|]. *)
(*          eapply hasTableauNegNeg; [right; now left|]. *)
(*          apply weakening with (Gamma := Gamma ,, F2 ,, Neg F1). *)
(*          ++ cbn; rewrite -!union_assoc; apply union_congr; symmetry; etransitivity; *)
(*               [now do 3 (apply union_congr; rewrite !union_assoc union_idemp; *)
(*                          rewrite -!union_assoc)|]. *)
(*             etransitivity; [now do 2 (apply union_congr; *)
(*                                       rewrite union_comm -!union_assoc union_idemp)|]; *)
(*               rewrite !union_assoc !union_idemp union_comm //. *)
(*          ++ apply sub_ctx_cong, extend_sub_ctx. do 3 apply cons_sub_ctx; apply sub_ctx_refl. *)
(*          ++ injection el => e2' e1'; rewrite e2' in e2; now apply IHT2. *)

(*     (* Case: [GammaAll] *) *)
(*     + apply get_all_sound in e; rewrite e in hin. *)
(*       eapply hasTableauAll; eauto. *)

(*     (* Case: [GammaNegEx] *) *)
(*     + apply get_neg_ex_sound in e; destruct e as (F & eF & e); rewrite e in hin. *)
(*       subst. eapply hasTableauNegNeg; eauto. *)
(*       eapply hasTableauAll with (x := s); [now left|]. *)
(*       apply weakening with (Gamma := Gamma ,, (Neg F){0 \to Free s}). *)
(*       * have efv : fv Gamma = @fv_list string _ _ (Gamma ,, All (Neg F)). *)
(*         { now rewrite (fv_list_in (Neg (Neg (All (Neg F)))) Gamma). } *)
(*         now cbn; rewrite efv; cbn; symmetry; *)
(*           etransitivity; [rewrite union_comm -!union_assoc union_idemp union_comm //|]. *)
(*       * apply extend_sub_ctx, cons_sub_ctx, sub_ctx_refl. *)
(*       * now apply IHT1. *)

(*     (* Case: [DeltaEx] *) *)
(*     + apply get_ex_sound in e; rewrite !e in hin hsko. *)
(*       eapply hasTableauNegAll with (t := t) (Hsko := hsko); eauto. *)
(*       eapply hasTableauNegNeg; [now left|]. *)
(*       change (hasTableau_ sko ((Gamma ,, Neg (Neg G) {0 \to t}) ,, G {0 \to t}) *)
(*                 (add_symbol (symbol sko t hsko) (Neg (All (Neg G))) record) sigma). *)
(*       apply weakening with (Gamma := Gamma ,, G {0 \to t}). *)
(*       * cbn; rewrite -union_assoc union_idemp //. *)
(*       * apply extend_sub_ctx, cons_sub_ctx, sub_ctx_refl. *)
(*       * rewrite (symbol_sound hsko) in esym; injection esym => ->. *)
(*         rewrite -e; now apply IHT1. *)

(*     (* Case: [DeltaNegAll] *) *)
(*     + apply get_neg_all_sound in e; destruct e as (F & eF & e); rewrite e in hin hsko. *)
(*       eapply hasTableauNegAll with (t := t) (Hsko := hsko); eauto. *)
(*       rewrite (symbol_sound hsko) in esym; injection esym => ->. *)
(*       rewrite -e; rewrite eF in e1; now apply IHT1. *)
(* Qed. *)

(* Theorem GuidedTableauSearch_sound : *)
(*   forall (sko : Skolemization) (Gamma : Con) (sigma : Substitution string Term) *)
(*     (tree : ExtendedRuleTree), *)
(*     GuidedTableauSearch sko Gamma sigma tree = ret true -> *)
(*     hasTableau sko Gamma sigma. *)
(* Proof. intros. eapply auxiliary_GuidedTableauSearch_sound; eauto. Qed. *)

(* (** ** 3. Tactic *) *)

(* (** Using the algorithm together with the soundness theorem, we provide a tactic [tableaux] *)
(*     that gives a proof [hasTableau sko Gamma sigma] if possible, or fails with an error otherwise. *) *)
(* Ltac tableaux tree := *)
(*   progress (apply (GuidedTableauSearch_sound _ _ _ tree); native_compute; *)
(*             lazymatch goal with *)
(*             | [ |- (false, [?err]) = (true, []) ] => *)
(*                 fail 0 "tableaux failed with the following error message: " err *)
(*             | _ => reflexivity *)
(*             end). *)
