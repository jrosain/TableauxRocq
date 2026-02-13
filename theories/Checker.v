(** * Reflect: sound and complete algorithm to "search" for tableaux proofs *)

From Tableaux Require Import Core.
From Tableaux Require Import ExtendedSyntax.

From Stdlib Require Import Lia.

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
    (tree : RuleTree) : Result bool :=
    result <- GuidedTableauSearch__aux (Ctx.from_list Gamma) sigma empty_record tree;
    ret (status result).
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

(* TODO: in this section, many proofs are "repeated". We _really_ should factorize this stuff. *)
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
            ret (T :: removelast s1 ++ s2)

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

  Lemma RuleTree_to_Sequence_hd :
    forall {R : RuleTree} {B : Branch} {T : Tableau} {s : Sequence sko},
      RuleTree_to_Sequence__aux B T R = Some s -> hd_error s = Some T.
  Proof using Type.
    intro R; induction R; intros ??? e; cbn in *.
    - injection e => <- //.
    - destruct r; [destruct (get_neg_neg f) | destruct (get_neg_or f) | destruct (get_or f) |
          destruct (get_all f) | destruct (get_neg_all f), (get_symbol t)];
      try easy.
      1,2,4,5:
        destruct (expand_tableau_branch__aux _ _ _ _);
      try easy; destruct (RuleTree_to_Sequence__aux _ _ _);
      try easy; injection e => <- //.
      destruct (expand_tableau_branch__aux _ _ _ _); try easy.
      do 2 (destruct (RuleTree_to_Sequence__aux _ _ _); try easy).
      injection e => <- //.
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
      exists (s : Sequence sko), RuleTree_to_Sequence__aux B T R = Some s.
  Proof using Type.
    intros ??????? e hbranchof econ. generalize dependent Gamma. generalize dependent T.
    revert B record record'. induction R; intros B record record' T hbranchof Gamma e econ.

    (* Case: [Leaf] *)
    - exists [T]; auto.

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
          as (s & hseq).
        exists (T :: s); cbn.
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
          as (s & hseq).
        exists (T :: s); cbn.
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
          as (s1 & hseq1).

        have [T1' ereplace] := RuleTree_to_Sequence_branch hbranchof1 hseq1.
        have ebranch : (B ++ [Right])%list <> (B ++ [Left])%list.
        { clear; induction B; cbn; intro; congruence. }

        have hbranchof2' : is_branch_of (B ++ [Right])%list (last s1 (mkLeaf sko)).
        { eapply is_branch_of_replace_child_oth.
          3: eassumption.
          all: eauto. }
        have ectx2' : get_context (B ++ [Right])%list T0 = get_context (B ++ [Right])%list
                                                             (last s1 (mkLeaf sko)).
        { eapply get_context_replace_child_oth.
          3: eassumption.
          all: eauto.}
        rewrite ectx2' in ectx2; auto.

        destruct (IHR2 (B ++ [Right])%list symbs record' (last s1 (mkLeaf sko)) hbranchof2'
                    (Ctx.union l' Gamma) hnext2 ectx2) as (s2 & hseq2).

        exists (T :: removelast s1 ++ s2); cbn.
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
          as (seq & hseq).
        exists (T :: seq); cbn.
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
          as (seq & hseq).
        exists (T :: seq); cbn.
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
    eapply GuidedTableauSearch_Some_RuleTree_to_Sequence_Some__aux; eauto.
    apply is_branch_of_nil.
  Qed.

  (** The set of symbols returned by the [GuidedTableauSearch__aux] algorithm is exactly the
      set of symbols of the last tableau of the sequence returned by
      [RuleTree_to_Sequence__aux]. *)
  Lemma RuleTree_to_Sequence_symbols :
    forall {R : RuleTree} {sigma : Substitution string Term} {B : Branch}
      {T : Tableau} {record : sko_record sko} {s : Sequence sko},
      is_branch_of B T ->
      GuidedTableauSearch__aux sko (get_context B T) sigma (symbols T) R =
        ret {| status := true; symbs := record |} ->
      RuleTree_to_Sequence__aux B T R = Some s ->
      record = symbols (last s (mkLeaf sko)).
  Proof using Type.
    intro R; induction R; intros ????? hbranchof esrch eseq.

    - cbn in eseq; injection eseq => <-; cbn.
      destruct o; cbn in esrch.
      + destruct p as (F & G); unfold closure_rule in esrch; cbn in esrch.
        destruct (formula_contradiction _ _ _ _); try easy.
        injection esrch => -> //.
      + unfold closure_rule in esrch; cbn in esrch.
        destruct (trivial_contradiction _); try easy.
        injection esrch => -> //.

    - destruct r; cbn in eseq.

      + apply alpha_rule_sound in esrch; destruct esrch as (l & eget & hin & esrch1).
        rewrite eget in eseq.
        destruct (expand_tableau_branch__aux _ _ _) eqn:hexpand; try easy.
        destruct (RuleTree_to_Sequence__aux _ _ _) eqn:eseq1; try easy.
        have ectx1 := get_context_extend_left hbranchof hexpand eq_refl.
        have hbranchof1 : is_branch_of (B ++ [Left])%list {| tree := t; symbols := symbols T |} :=
          is_branch_of_extend_left hbranchof hexpand.
        rewrite /Ctx.union /Ctx.elements in esrch1, ectx1; rewrite -ectx1 in esrch1.
        rewrite (IHR1 sigma (B ++ [Left])%list _ _ s0 hbranchof1 esrch1 eseq1).
        have hs0 : s0 <> [] by eapply RuleTree_to_Sequence_not_nil; eauto.
        injection eseq => <-; cbn. destruct s0; easy.

      + apply alpha_rule_sound in esrch; destruct esrch as (l & eget & hin & esrch1).
        rewrite eget in eseq.
        destruct (expand_tableau_branch__aux _ _ _) eqn:hexpand; try easy.
        destruct (RuleTree_to_Sequence__aux _ _ _) eqn:eseq1; try easy.
        have ectx1 := get_context_extend_left hbranchof hexpand eq_refl.
        have hbranchof1 : is_branch_of (B ++ [Left])%list {| tree := t; symbols := symbols T |} :=
          is_branch_of_extend_left hbranchof hexpand.
        rewrite /Ctx.union /Ctx.elements in esrch1, ectx1; rewrite -ectx1 in esrch1.
        rewrite (IHR1 sigma (B ++ [Left])%list _ _ s0 hbranchof1 esrch1 eseq1).
        have hs0 : s0 <> [] by eapply RuleTree_to_Sequence_not_nil; eauto.
        injection eseq => <-; cbn. destruct s0; easy.

      + apply beta_rule_sound in esrch;
          destruct esrch as (l & l' & symbs & eget & hin & esrch1 & esrch2).
        rewrite eget in eseq.
        destruct (expand_tableau_branch__aux _ _ _) eqn:hexpand; try easy.
        destruct (RuleTree_to_Sequence__aux _ _ _) eqn:eseq1; try easy.
        destruct (RuleTree_to_Sequence__aux (B ++ [Right])%list _ _) eqn:eseq2; try easy.
        have ectx1 := get_context_extend_left hbranchof hexpand eq_refl.
        have ectx2 := get_context_extend_right hbranchof hexpand eq_refl.
        have hbranchof1 : is_branch_of (B ++ [Left])%list {| tree := t; symbols := symbols T |}
          := is_branch_of_extend_left hbranchof hexpand.
        have hbranchof2 := is_branch_of_extend_right hbranchof hexpand.
        rewrite /Ctx.union /Ctx.elements in esrch1, ectx1, esrch2, ectx2.
        rewrite -ectx1 in esrch1; rewrite -ectx2 in esrch2.

        have esymbs' : symbs = symbols (last s0 (mkLeaf sko)).
        { eapply IHR1; eauto. }

        rewrite esymbs' in esrch2. injection eseq => <-.
        rewrite app_comm_cons last_app.
        { eapply RuleTree_to_Sequence_not_nil; eauto. }

        have [T1' ereplace] := RuleTree_to_Sequence_branch hbranchof1 eseq1.
        have ebranch : (B ++ [Right])%list <> (B ++ [Left])%list.
        { clear; induction B; cbn; intro; congruence. }

        have hbranchof2' : is_branch_of (B ++ [Right])%list (last s0 (mkLeaf sko)).
        { eapply is_branch_of_replace_child_oth.
          3: eassumption.
          all: eauto. }

        have ectx2' : get_context (B ++ [Right])%list t = get_context (B ++ [Right])%list
                                                             (last s0 (mkLeaf sko)).
        { eapply get_context_replace_child_oth.
          3: eassumption.
          all: eauto.}

        eapply IHR2; eauto.
        now rewrite -ectx2'.

      + apply gamma_rule_sound in esrch; destruct esrch as (F & eget & hin & esrch1).
        rewrite eget in eseq.
        destruct (expand_tableau_branch__aux _ _ _) eqn:hexpand; try easy.
        destruct (RuleTree_to_Sequence__aux _ _ _) eqn:eseq1; try easy.
        have ectx1 := get_context_extend_left hbranchof hexpand eq_refl.
        have hbranchof1 : is_branch_of (B ++ [Left])%list {| tree := t; symbols := symbols T |} :=
          is_branch_of_extend_left hbranchof hexpand.
        rewrite /Ctx.add /Ctx.elements in esrch1, ectx1; cbn in ectx1; rewrite -ectx1 in esrch1.
        rewrite (IHR1 sigma (B ++ [Left])%list _ _ s1 hbranchof1 esrch1 eseq1).
        have hs0 : s1 <> [] by eapply RuleTree_to_Sequence_not_nil; eauto.
        injection eseq => <-; cbn. destruct s1; easy.

      + apply delta_rule_sound in esrch; destruct esrch as
          (f0 & F & eget & hin & hsko & esymb & esrch1).
        rewrite eget esymb in eseq.
        destruct (expand_tableau_branch__aux _ _ _) eqn:hexpand; try easy.
        destruct (RuleTree_to_Sequence__aux _ _ _) eqn:eseq1; try easy.
        have ectx1 := get_context_extend_left hbranchof hexpand eq_refl.
        have hbranchof1 : is_branch_of
                            (B ++ [Left])%list
                            {| tree := t0; symbols := add_symbol f0 f (symbols T) |} :=
          is_branch_of_extend_left hbranchof hexpand.
        rewrite /Ctx.add /Ctx.elements in esrch1, ectx1; cbn in ectx1; rewrite -ectx1 in esrch1.
        rewrite (IHR1 sigma (B ++ [Left])%list _ _ s0 hbranchof1 esrch1 eseq1).
        have hs0 : s0 <> [] by eapply RuleTree_to_Sequence_not_nil; eauto.
        injection eseq => <-; cbn. destruct s0; easy.
  Qed.

  (** Now, we show that, in the same setting, the sequence gotten from [RuleTree_to_Sequence]
      is actually an expansion sequence. A small lemma that will be useful later on is that
      the tableau with which we call the auxiliary function and the second element of the
      sequence (if it exists) give an expansion step. *)
  Lemma RuleTree_to_Sequence_snd_expansion :
    forall {R : RuleTree} {sigma : Substitution string Term} {B : Branch}
      {T T' : Tableau} {record : sko_record sko} {s : Sequence sko},
      is_branch_of B T ->
      GuidedTableauSearch__aux sko (get_context B T) sigma (symbols T) R =
        ret {| status := true; symbs := record |} ->
      RuleTree_to_Sequence__aux B T R = Some s -> s.(1) = Some T' ->
      T |> T'.
  Proof using Type.
    intro R; destruct R; intros ?????? hbranchof esrch eseq esnd.

    - cbn in eseq. injection eseq => eseq'; rewrite -eseq' in esnd; inversion esnd.

    - destruct r; cbn in eseq, esrch.

      + apply alpha_rule_sound in esrch; destruct esrch as (l & eget & hin & esrch);
          rewrite eget in eseq.
        destruct (expand_tableau_branch__aux _ _ _ _) eqn:hexpand; try easy.
        destruct (RuleTree_to_Sequence__aux _ _ _) eqn:eseq1; try easy.
        injection eseq => eseq'; rewrite -eseq' nth_error_S nth_error_0 in esnd.
        erewrite RuleTree_to_Sequence_hd in esnd; eauto.
        injection esnd => <-.
        do 2 (destruct f; try easy).
        eapply expansion_NegNeg; eauto.
        * apply in_context_is_on_branch; eauto.
        * cbn in eget; unfold Ctx.singleton in eget. rewrite eget.
          unfold Ctx.elements in hexpand; cbn.
          now rewrite hexpand.

      + apply alpha_rule_sound in esrch; destruct esrch as (l & eget & hin & esrch);
          rewrite eget in eseq.
        destruct (expand_tableau_branch__aux _ _ _ _) eqn:hexpand; try easy.
        destruct (RuleTree_to_Sequence__aux _ _ _) eqn:eseq1; try easy.
        injection eseq => eseq'; rewrite -eseq' nth_error_S nth_error_0 in esnd.
        erewrite RuleTree_to_Sequence_hd in esnd; eauto.
        injection esnd => <-.
        do 2 (destruct f; try easy).
        eapply expansion_NegOr; eauto.
        * apply in_context_is_on_branch; eauto.
        * cbn in eget; unfold Ctx.singleton in eget. rewrite eget.
          unfold Ctx.elements in hexpand; cbn.
          now rewrite hexpand.

      + apply beta_rule_sound in esrch; destruct esrch as
          (l & l' & rec & eget & hin & esrch1 & esrch2); rewrite eget in eseq.
        destruct (expand_tableau_branch__aux _ _ _ _) eqn:hexpand; try easy.
        destruct (RuleTree_to_Sequence__aux _ _ _) eqn:eseq1; try easy.
        destruct (RuleTree_to_Sequence__aux (B ++ [Right])%list _ _) eqn:eseq2; try easy.
        injection eseq => eseq'; rewrite -eseq' nth_error_S nth_error_0 in esnd.
        have hs0 : s0 <> []. { eapply RuleTree_to_Sequence_not_nil; eauto. }
        destruct f; try easy. destruct s0; try easy.
        destruct s0.
        * erewrite RuleTree_to_Sequence_hd in esnd; eauto.
          cbn in esnd; injection esnd => <-.
          eapply expansion_Or; eauto.
          -- apply in_context_is_on_branch; eauto.
          -- cbn in eget; unfold Ctx.singleton in eget.
             injection eget => -> ->; cbn.
             rewrite hexpand.
             have h := RuleTree_to_Sequence_hd eseq1. injection h => -> //.
        * cbn in esnd. injection esnd => <-.
          have h := RuleTree_to_Sequence_hd eseq1. injection h => -> //.
          eapply expansion_Or; eauto.
          -- apply in_context_is_on_branch; eauto.
          -- cbn in eget; unfold Ctx.singleton in eget.
             injection eget => -> ->; cbn.
             rewrite hexpand //.

      + apply gamma_rule_sound in esrch; destruct esrch as (l & eget & hin & esrch);
          rewrite eget in eseq.
        destruct (expand_tableau_branch__aux _ _ _ _) eqn:hexpand; try easy.
        destruct (RuleTree_to_Sequence__aux _ _ _) eqn:eseq1; try easy.
        injection eseq => eseq'; rewrite -eseq' nth_error_S nth_error_0 in esnd.
        erewrite RuleTree_to_Sequence_hd in esnd; eauto.
        injection esnd => <-.
        destruct f; try easy.
        eapply expansion_All with (x := s0); eauto.
        * apply in_context_is_on_branch; eauto.
        * cbn in eget; injection eget => ->.
          cbn; now rewrite hexpand.

      + apply delta_rule_sound in esrch;
          destruct esrch as (f0 & F & eget & hin & hsko & esymb & esrch);
          rewrite eget esymb in eseq.
        destruct (expand_tableau_branch__aux _ _ _ _) eqn:hexpand; try easy.
        destruct (RuleTree_to_Sequence__aux _ _ _) eqn:eseq1; try easy.
        injection eseq => eseq'; rewrite -eseq' nth_error_S nth_error_0 in esnd.
        erewrite RuleTree_to_Sequence_hd in esnd; eauto.
        injection esnd => <-.
        do 2 (destruct f; try easy).
        have e := symbol_sound sko hsko.
        rewrite esymb in e; injection e => ->; eauto.
        eapply expansion_NegAll with (hsko := hsko); eauto.
        * apply in_context_is_on_branch; eauto.
        * cbn in eget. change (Neg f {0 \to t}) with ((Neg f) {0 \to t}); injection eget => ->.
          cbn; now rewrite hexpand.
  Qed.

  Lemma GuidedTableauSearch_Some_RuleTree_to_Sequence_is_expansion_sequence :
    forall {R : RuleTree} {sigma : Substitution string Term} {B : Branch}
      {T : Tableau} {record : sko_record sko} {s : Sequence sko},
      is_branch_of B T -> GuidedTableauSearch__aux sko (get_context B T) sigma (symbols T) R =
                           ret {| status := true; symbs := record |} ->
      RuleTree_to_Sequence__aux B T R = Some s ->
      is_expansion_sequence s.
  Proof using Type.
    intro R; induction R; intros ????? hbranchof esrch eseq.

    - cbn in eseq; injection eseq => <-.
      apply is_expansion_sequence_singleton.

    - destruct r.

      + have [ l [ eget [ hin esrch1 ] ] ] := alpha_rule_sound esrch.
        have heseq := eseq. have hesrch := esrch.
        cbn in eseq; rewrite eget in eseq.
        destruct (expand_tableau_branch__aux _ _ _ _) eqn:hexpand; try easy.
        destruct (RuleTree_to_Sequence__aux (B ++ [Left])%list _ _) eqn:eseq1; try easy.
        have ectx1 := get_context_extend_left hbranchof hexpand eq_refl.
        have hbranchof1 := is_branch_of_extend_left hbranchof hexpand.
        rewrite /Ctx.union /Ctx.elements in esrch1, ectx1; rewrite -ectx1 in esrch1.
        specialize (IHR1 sigma (B ++ [Left])%list {| tree := t; symbols := symbols T |}
                      record s0 hbranchof1 esrch1 eseq1).
        intros i Ti Ti' ei ei'; destruct i.
        * rewrite nth_error_0 in ei.
          erewrite RuleTree_to_Sequence_hd in ei; eauto.
          injection ei => <-.
          eapply RuleTree_to_Sequence_snd_expansion; eauto.
        * injection eseq => es0. rewrite -es0 nth_error_S in ei, ei'.
          eapply IHR1; eauto.

      + have [ l [ eget [ hin esrch1 ] ] ] := alpha_rule_sound esrch.
        have heseq := eseq. have hesrch := esrch.
        cbn in eseq; rewrite eget in eseq.
        destruct (expand_tableau_branch__aux _ _ _ _) eqn:hexpand; try easy.
        destruct (RuleTree_to_Sequence__aux (B ++ [Left])%list _ _) eqn:eseq1; try easy.
        have ectx1 := get_context_extend_left hbranchof hexpand eq_refl.
        have hbranchof1 := is_branch_of_extend_left hbranchof hexpand.
        rewrite /Ctx.union /Ctx.elements in esrch1, ectx1; rewrite -ectx1 in esrch1.
        specialize (IHR1 sigma (B ++ [Left])%list {| tree := t; symbols := symbols T |}
                      record s0 hbranchof1 esrch1 eseq1).
        intros i Ti Ti' ei ei'; destruct i.
        * rewrite nth_error_0 in ei.
          erewrite RuleTree_to_Sequence_hd in ei; eauto.
          injection ei => <-.
          eapply RuleTree_to_Sequence_snd_expansion; eauto.
        * injection eseq => es0. rewrite -es0 nth_error_S in ei, ei'.
          eapply IHR1; eauto.

      + have [ l [ l' [ symbs1 [ eget [ hin [ esrch1 esrch2 ] ] ] ] ] ] := beta_rule_sound esrch.
        have heseq := eseq. have hesrch := esrch.
        cbn in eseq; rewrite eget in eseq.
        destruct (expand_tableau_branch__aux _ _ _ _) eqn:hexpand; try easy.
        destruct (RuleTree_to_Sequence__aux (B ++ [Left])%list _ _) eqn:eseq1; try easy.
        destruct (RuleTree_to_Sequence__aux (B ++ [Right])%list _ _) eqn:eseq2; try easy.
        have ectx1 := get_context_extend_left hbranchof hexpand eq_refl.
        have ectx2 := get_context_extend_right hbranchof hexpand eq_refl.
        have hbranchof1 : is_branch_of (B ++ [Left])%list {| tree := t; symbols := symbols T |}
          := is_branch_of_extend_left hbranchof hexpand.
        have hbranchof2 := is_branch_of_extend_right hbranchof hexpand.
        rewrite /Ctx.union /Ctx.elements in esrch1, ectx1, esrch2, ectx2.
        rewrite -ectx1 in esrch1; rewrite -ectx2 in esrch2.

        specialize (IHR1 sigma (B ++ [Left])%list {| tree := t; symbols := symbols T |}
                      symbs1 s0 hbranchof1 esrch1 eseq1).

        have [T1' ereplace] := RuleTree_to_Sequence_branch hbranchof1 eseq1.
        have ebranch : (B ++ [Right])%list <> (B ++ [Left])%list.
        { clear; induction B; cbn; intro; congruence. }

        have hbranchof2' : is_branch_of (B ++ [Right])%list (last s0 (mkLeaf sko)).
        { eapply is_branch_of_replace_child_oth.
          3: eassumption.
          all: eauto. }
        have ectx2' : get_context (B ++ [Right])%list t = get_context (B ++ [Right])%list
                                                             (last s0 (mkLeaf sko)).
        { eapply get_context_replace_child_oth.
          3: eassumption.
          all: eauto.}
        rewrite ectx2' in esrch2; auto.
        have esymbs2 : symbols (last s0 (mkLeaf sko)) = symbs1.
        { symmetry; eapply RuleTree_to_Sequence_symbols.
          3: eauto.
          - apply hbranchof1.
          - cbn. apply esrch1. }

        rewrite -esymbs2 in esrch2.
        specialize (IHR2 sigma (B ++ [Right])%list (last s0 (mkLeaf sko))
                      record s1 hbranchof2' esrch2 eseq2).

        intros i Ti Ti' ei ei'.

        (* If [i] is [0], then we do as for the others cases *)
        destruct (i == 0).
        * subst; rewrite nth_error_0 in ei.
          erewrite RuleTree_to_Sequence_hd in ei; eauto.
          injection ei => <-.
          eapply RuleTree_to_Sequence_snd_expansion; eauto.
        * injection eseq => es; rewrite -es in ei, ei'.

          (* Otherwise, there are 3 cases: either [i < #|s0| - 1] and we get the property
             out of [s0], either [i > #|s0| - 1] and we get the property out of [s1], or
             [i = #|s0| - 1]. *)
          destruct (i == (#|s0| - 1)).

          -- subst. have hs0 : #|s0| > 0 by lia.
             rewrite PeanoNat.Nat.sub_1_r PeanoNat.Nat.succ_pred_pos // in ei'.
             rewrite app_comm_cons nth_error_app1 in ei.
             1: { cbn; rewrite removelast_length; lia. }
             rewrite app_comm_cons nth_error_app2 in ei'.
             1: { cbn; rewrite removelast_length; lia. }
             cbn in ei'; rewrite removelast_length PeanoNat.Nat.succ_pred_pos //
                           PeanoNat.Nat.sub_diag nth_error_0 in ei'.
             erewrite RuleTree_to_Sequence_hd in ei'; eauto.

             (* Then, here, either [#|s0| = 1] (and we go back to the earlier case), or
                [#|s0| > 1], in which case [Ti] is the second-to-last element of [s0],
                which reduces to the last one. *)
             destruct (#|s0| == 1).

             ++ injection ei' => <-. rewrite e in ei; cbn in ei. injection ei => <-.
                have e' : Some (last s0 (mkLeaf sko)) = s0.(0).
                { do 2 (destruct s0; try easy). }
                eapply RuleTree_to_Sequence_snd_expansion; eauto.
                have eremovelast : removelast s0 = [].
                { do 2 (destruct s0; try easy). }
                rewrite eremovelast nth_error_S app_nil_l; cbn[tl].
                rewrite nth_error_0; erewrite RuleTree_to_Sequence_hd; eauto.

             ++ have eremovelast : (T :: removelast s0).(#|s0| - 1) =
                                     s0.(#|s0| - 2).
                { replace (#|s0| - 1) with (S (#|s0| - 2)) by lia.
                  cbn; transitivity ((removelast s0 ++ [last s0 (mkLeaf sko)]).(#|s0| - 2)).
                  - rewrite nth_error_app1 //.
                    rewrite removelast_length; lia.
                  - rewrite -app_removelast_last //.
                    intro; subst. rewrite length_nil in hs0; auto. }
                rewrite eremovelast in ei.
                have elast : Some (last s0 (mkLeaf sko)) = s0.(#|s0| - 1).
                { rewrite -last_nth_error //; intro; subst; easy. }
                rewrite elast in ei'.
                eapply IHR1; eauto.
                now replace (S (#| s0 | - 2)) with (#|s0| - 1) by lia.

          (* Now, we check whether [i < #|s0| - 1] or [i > #|s0| - 1] and conclude. *)
          -- destruct (Compare_dec.le_gt_dec i (#|s0| - 1)) as [hle | hlt].
             ++ inversion hle; try easy.
                have hlt : i < #|s0| - 1 by lia.
                clear H H0 hle.
                rewrite app_comm_cons !nth_error_app1 in ei, ei'.
                1,2: cbn; rewrite removelast_length PeanoNat.Nat.succ_pred_pos; lia.
                rewrite nth_error_S in ei'.
                have hs0 : #|s0| > 1.
                { apply Compare_dec.not_le; intro hle; inversion hle; lia. }
                have eTi : (T :: removelast s0).(i) = s0.(i - 1).
                { replace i with (S (i - 1)) by lia; cbn.
                  rewrite PeanoNat.Nat.sub_0_r removelast_nth_error //.
                  transitivity i; auto; lia. }
                rewrite eTi in ei.
                rewrite removelast_nth_error in ei'; auto.
                eapply IHR1; eauto.
                rewrite PeanoNat.Nat.sub_1_r PeanoNat.Nat.succ_pred_pos //; lia.
             ++ rewrite app_comm_cons !nth_error_app2 in ei, ei'.
                1,2: cbn; rewrite removelast_length; lia.
                eapply IHR2; eauto.
                rewrite -PeanoNat.Nat.sub_succ_l //.
                cbn; rewrite removelast_length; lia.

      + have [ l [ eget [ hin esrch1 ] ] ] := gamma_rule_sound esrch.
        have heseq := eseq. have hesrch := esrch.
        cbn in eseq; rewrite eget in eseq.
        destruct (expand_tableau_branch__aux _ _ _ _) eqn:hexpand; try easy.
        destruct (RuleTree_to_Sequence__aux (B ++ [Left])%list _ _) eqn:eseq1; try easy.
        have ectx1 := get_context_extend_left hbranchof hexpand eq_refl.
        have hbranchof1 := is_branch_of_extend_left hbranchof hexpand.
        rewrite /Ctx.add /Ctx.elements in esrch1, ectx1. cbn in ectx1; rewrite -ectx1 in esrch1.
        specialize (IHR1 sigma (B ++ [Left])%list {| tree := t; symbols := symbols T |}
                      record s1 hbranchof1 esrch1 eseq1).
        intros i Ti Ti' ei ei'; destruct i.
        * rewrite nth_error_0 in ei.
          erewrite RuleTree_to_Sequence_hd in ei; eauto.
          injection ei => <-.
          eapply RuleTree_to_Sequence_snd_expansion; eauto.
        * injection eseq => es0. rewrite -es0 nth_error_S in ei, ei'.
          eapply IHR1; eauto.

      + have [ f0 [ l [ eget [ hin [ hsko [ esymb esrch1 ] ] ] ] ] ] := delta_rule_sound esrch.
        have heseq := eseq. have hesrch := esrch.
        cbn in eseq; rewrite eget esymb in eseq.
        destruct (expand_tableau_branch__aux _ _ _ _) eqn:hexpand; try easy.
        destruct (RuleTree_to_Sequence__aux (B ++ [Left])%list _ _) eqn:eseq1; try easy.
        have ectx1 := get_context_extend_left hbranchof hexpand eq_refl.
        have hbranchof1 := is_branch_of_extend_left hbranchof hexpand.
        rewrite /Ctx.add /Ctx.elements in esrch1, ectx1. cbn in ectx1; rewrite -ectx1 in esrch1.
        specialize (IHR1 sigma (B ++ [Left])%list
                         {| tree := t0; symbols := add_symbol f0 f (symbols T) |}
                      record s0 hbranchof1 esrch1 eseq1).
        intros i Ti Ti' ei ei'; destruct i.
        * rewrite nth_error_0 in ei.
          erewrite RuleTree_to_Sequence_hd in ei; eauto.
          injection ei => <-.
          eapply RuleTree_to_Sequence_snd_expansion; eauto.
        * injection eseq => es0. rewrite -es0 nth_error_S in ei, ei'.
          eapply IHR1; eauto.
  Qed.

  Lemma GuidedTableauSearch_Some_RuleTree_to_Sequence_closed :
    forall {R : RuleTree} {sigma : Substitution string Term} {B : Branch}
      {T T' : Tableau} {record record' : sko_record sko} {s : Sequence sko},
      (forall (B : Branch),
          is_branch_of B T ->
          GuidedTableauSearch__aux sko (get_context B T) sigma record R =
            ret {| status := true; symbs := record' |}) ->
      RuleTree_to_Sequence__aux B T R = Some s ->
      is_tableau_closed (last s (mkLeaf sko)) sigma.
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
      {record record' : sko_record sko} {s : Sequence sko},
      GuidedTableauSearch__aux sko Gamma sigma record R = ret {| status := true; symbs := record' |} ->
      RuleTree_to_Sequence Gamma R = Some s ->
      is_tableau_closed (last s (mkLeaf sko)) sigma.
  Proof.
    intros ????? e e'.
    have eGamma : get_context EmptyBranch (mkTableau sko Gamma) = Gamma by reflexivity.
    (* rewrite -eGamma in e. destruct R. *)
  Admitted.

  (** We can then conclude on the soundness of the algorithm. *)
  Lemma GuidedTableauSearch_sound :
    forall {Gamma : list Form} {sigma : Substitution string Term} {R : RuleTree},
      GuidedTableauSearch sko Gamma sigma R = ret true ->
      hasTableau sko Gamma sigma.
  Proof using Type.
    intros ??? e.

    cbn in e. destruct (GuidedTableauSearch__aux sko (Ctx.from_list Gamma) sigma empty_record R) eqn:esrch;
      try easy; cbn in *.
    destruct a; cbn in *. injection e => estatus el; subst.
    rewrite app_nil_r in estatus; subst.

    have [s esequence] := GuidedTableauSearch_Some_RuleTree_to_Sequence_Some esrch.
    exists s; split.

    - eapply GuidedTableauSearch_Some_RuleTree_to_Sequence_is_expansion_sequence; eauto.
      + apply is_branch_of_nil.
      + apply esrch.
    - split.
      + erewrite RuleTree_to_Sequence_hd; eauto.
      + eapply GuidedTableauSearch_Some_Sequence_closed; eauto.
  Qed.
End RuleTreeToSequence.

(** ** 3. The [tableaux] tactic *)

Ltac tableaux tree :=
  progress (apply (GuidedTableauSearch_sound _ _ _ tree); native_compute;
            lazymatch goal with
            | [ |- (false, [?err]) = (true, []) ] =>
                fail 0 "tableaux failed with the following error message: " err
            | _ => reflexivity
            end).

(** ** 4. Extended Syntax *)

Module Export ExtendedSyntax.
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
End ExtendedSyntax.
