(** * Reflect: sound and complete algorithm to "search" for tableaux proofs *)

From Tableaux Require Import Core.
From Tableaux Require Import ExtendedSyntax.

From Stdlib Require Import Lia.

(** In this file, we implement a tableau proof checker procedure.

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

  Lemma existsb_exists :
    forall (f : Form -> bool) (Gamma : t),
      existsb f Gamma = true <-> (exists F : Form, F \in Gamma /\ f F = true).
  Proof. apply existsb_exists. Qed.
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
    (eqb (Neg F)@[sigma] G@[sigma] || eqb (Neg G)@[sigma] F@[sigma]).

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
Section ProofCheckerAlgorithm.
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

  Definition CheckerAlgorithm :=
    Ctx.t -> Substitution string Term -> sko_record sko -> RuleTree -> result.

  Definition closure_rule (search_contradiction : Ctx.t -> Substitution string Term -> bool)
    (msg : string) (Gamma : Ctx.t) (sigma : Substitution string Term) (symbols : sko_record sko) : result :=
    if search_contradiction Gamma sigma
    then ret {| status := true; symbs := symbols |}
    else error ("No (" ++ msg ++ ") contradiction in the context: " ++
                  pr_list pr_form (Ctx.elements Gamma)@[sigma]).

  Definition alpha_rule (Gamma : Ctx.t) (sigma : Substitution string Term) (T : RuleTree)
    (record : sko_record sko) (F : Form) (getter : Form -> option Ctx.t) (err : string)
    (search : CheckerAlgorithm)  :=
    rule_wrapper Gamma F err getter (fun l => search (Ctx.union l Gamma) sigma record T).

  Definition beta_rule (Gamma : Ctx.t) (sigma : Substitution string Term) (T1 T2 : RuleTree)
    (record : sko_record sko) (F : Form) (getter : Form -> option (Ctx.t * Ctx.t))
    (err : string) (search : CheckerAlgorithm)  :=
    rule_wrapper Gamma F err getter
      (fun l =>
         r <- search (Ctx.union (fst l) Gamma) sigma record T1;
         if status r then search (Ctx.union (snd l) Gamma) sigma (symbs r) T2
         else ret r).

  Definition gamma_rule (Gamma : Ctx.t) (sigma : Substitution string Term) (T : RuleTree)
    (record : sko_record sko) (F : Form) (x : string) (getter : Form -> option Form)
    (err : string) (search : CheckerAlgorithm)  :=
    rule_wrapper Gamma F err getter
      (fun F => search (Ctx.add (F{0 \to Free x}) Gamma) sigma record T).

  Definition delta_rule (Gamma : Ctx.t) (sigma : Substitution string Term) (T : RuleTree)
    (record : sko_record sko) (F : Form) (t : Term) (getter : Form -> option Form)
    (err : string) (func_symbs : SetOfString) (search : CheckerAlgorithm) :=
    rule_wrapper Gamma F err getter
      (fun F0 => if sko t F record (fv Gamma) (func_symbs \union to_set record)
             then
               match get_symbol t with
               | None => error "This shouldn't ever happen."
               | Some f => search (Ctx.add (F0{0 \to t}) Gamma)  sigma (add_symbol f F record) T
               end
             else
               error ("The term " ++ pr_term t ++ " is not a valid Skolem symbol in the context "
                        ++ Ctx.pr Gamma)).

  (** The proof checking algorithm proceeds as follows:
      - on a leaf: it tries to search for a closure [Bot] or a contradiction using
        the supplied substitution ; returns [false] if no closure rule can be found ;
      - on a node: it tries to apply the given rule on the given formula, and calls the
        algorithm recursively. *)
  Fixpoint CheckProof__aux
    (func_symbols : SetOfString) (Gamma : Ctx.t) (sigma : Substitution string Term)
    (record : sko_record sko) (tree : RuleTree) : result :=
    match tree with
    | Leaf None => closure_rule (fun Gamma _ => trivial_contradiction Gamma) "trivial" Gamma sigma record

    | Leaf (Some (F, G)) =>
        closure_rule (formula_contradiction F G) (pr_form F ++ " <> " ++ pr_form G) Gamma sigma record

    | Node T1 rule T2 =>

        let alpha_rule (F : Form) (getter : Form -> option Ctx.t) (err : string) :=
          alpha_rule Gamma sigma T1 record F getter err (CheckProof__aux func_symbols) in

        let beta_rule (F : Form) (getter : Form -> option (Ctx.t * Ctx.t)) (err : string) :=
          beta_rule Gamma sigma T1 T2 record F getter err (CheckProof__aux func_symbols) in

        let gamma_rule (F : Form) (x : string) (getter : Form -> option Form) (err : string) :=
          gamma_rule Gamma sigma T1 record F x getter err (CheckProof__aux func_symbols) in

        let delta_rule (F : Form) (t : Term) (getter : Form -> option Form) (err : string) :=
          delta_rule Gamma sigma T1 record F t getter err func_symbols (CheckProof__aux func_symbols) in

        match rule with
        | AlphaNegNeg F => alpha_rule F get_neg_neg "double negation"
        | AlphaNegOr F => alpha_rule F get_neg_or "negated disjunction"

        | BetaOr F => beta_rule F get_or "disjunction"

        | GammaAll F x => gamma_rule F x get_all "universal formula"

        | DeltaNegAll F t => delta_rule F t get_neg_all "negated universal formula"
        end
    end.

  (** In this algorithm, we use the following trick: the function symbols of a tableau do
      not change as we only add subformulas, except for delta rules. Consequently, we precompute
      the set of function symbols, and simply check whether the Skolemization is valid or not
      w.r.t. the union of these function symbols and the introduced Skolem symbols. *)
  Definition CheckProof (Gamma : list Form) (sigma : Substitution string Term)
    (tree : RuleTree) : Result bool :=
    result <- CheckProof__aux (function_symbols Gamma) (Ctx.from_list Gamma) sigma empty_record tree;
    ret (status result).
End ProofCheckerAlgorithm.
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

  Lemma formula_contradiction_sound :
    forall {F G : Form} {Gamma : Ctx.t} {sigma : Substitution string Term},
      formula_contradiction F G Gamma sigma = true ->
      exists (P P' : Form), Ctx.In P Gamma /\ Ctx.In P' Gamma /\ P@[sigma] = (Neg P')@[sigma].
  Proof using Type.
    intros ???? ((hin & hin')%andb_prop & e)%andb_prop; unfold formula_contradiction in e.
    apply Bool.orb_prop in e; rewrite !eqbIsEq in e; destruct e as [e1 | e2].
    - exists G, F; repeat split; auto; now rewrite -Ctx.mem_spec.
    - exists F, G; repeat split; auto; now rewrite -Ctx.mem_spec.
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
      {getter : Form -> option Ctx.t} {func_symbs : SetOfString},
      alpha_rule sko Gamma sigma T record F getter err (CheckProof__aux sko func_symbs) =
        ret {| status := true; symbs := record' |} ->
      exists (l : Ctx.t),
        getter F = Some l /\ Ctx.In F Gamma /\
          CheckProof__aux sko func_symbs (Ctx.union l Gamma) sigma record T =
            ret {| status := true; symbs := record' |}.
  Proof using Type.
    intros ????????? e. unfold alpha_rule in e.
    now apply rule_wrapper_sound in e.
  Qed.

  Lemma beta_rule_sound :
    forall {Gamma : Ctx.t} {sigma : Substitution string Term}
      {record record' : sko_record sko} {T1 T2 : RuleTree} {F : Form} {err : string}
      {getter : Form -> option (Ctx.t * Ctx.t)} {func_symbs : SetOfString},
      beta_rule sko Gamma sigma T1 T2 record F getter err (CheckProof__aux sko func_symbs) =
        ret {| status := true; symbs := record' |} ->
      exists (l1 l2 : Ctx.t) (symbols : sko_record sko),
        getter F = Some (l1, l2) /\ Ctx.In F Gamma /\
          CheckProof__aux sko func_symbs (Ctx.union l1 Gamma) sigma record T1 =
            ret {| status := true; symbs := symbols |} /\
          CheckProof__aux sko func_symbs (Ctx.union l2 Gamma) sigma symbols T2 =
            ret {| status := true; symbs := record' |}.
  Proof using Type.
    intros ?????????? e. unfold beta_rule in e.
    apply rule_wrapper_sound in e. destruct e as ((l1 & l2) & eg & hin & hact).
    exists l1, l2; cbn[fst snd] in hact.
    destruct (CheckProof__aux sko func_symbs (Ctx.union l1 Gamma) sigma record T1); cbn in *.
    destruct a as (b & s). exists s; repeat split; cbn in *; destruct b; unfold ret in hact; cbn in *;
      auto.

    2,4: injection hact => _ _ contra; inversion contra.

    all: destruct (CheckProof__aux sko func_symbs (Ctx.union l2 Gamma) sigma s T2); cbn in *;
      destruct (status a); cbn in *; auto.

    all: injection hact => e _; apply app_eq_nil in e; destruct e as [el el']; subst; auto.
  Qed.

  Lemma gamma_rule_sound :
    forall {Gamma : Ctx.t} {sigma : Substitution string Term}
      {record record' : sko_record sko} {T : RuleTree} {F : Form} {x : string} {err : string}
      {getter : Form -> option Form} {func_symbs : SetOfString},
      gamma_rule sko Gamma sigma T record F x getter err (CheckProof__aux sko func_symbs) =
        ret {| status := true; symbs := record' |} ->
      exists (G : Form),
        getter F = Some G /\ Ctx.In F Gamma /\
          CheckProof__aux sko func_symbs (Ctx.add (G{0 \to Free x}) Gamma) sigma record T =
            ret {| status := true; symbs := record' |}.
  Proof using Type.
    intros ?????????? e. unfold gamma_rule in e.
    now apply rule_wrapper_sound in e.
  Qed.

  Lemma delta_rule_sound :
    forall {Gamma : Ctx.t} {sigma : Substitution string Term}
      {record record' : sko_record sko} {T : RuleTree} {F : Form} {t : Term} {err : string}
      {getter : Form -> option Form} {func_symbs : SetOfString},
      delta_rule sko Gamma sigma T record F t getter err func_symbs (CheckProof__aux sko func_symbs) =
        ret {| status := true; symbs := record' |} ->
      exists (f : string) (G : Form),
        getter F = Some G /\ F \in Gamma /\
          sko t F record (fv Gamma) (func_symbs \union to_set record) = true /\
          get_symbol t = Some f /\
          CheckProof__aux sko func_symbs (G{0 \to t} :: Gamma) sigma (add_symbol f F record) T =
            ret {| status := true; symbs := record' |}.
  Proof using Type.
    intros ?????????? e. unfold delta_rule in e.
    apply rule_wrapper_sound in e.
    destruct e as (G & eG & hin & e).
    destruct (sko t F _ _ _) eqn:hsko; try inversion e.
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
  Context {sko : Skolemization}.

  Let Tableau := Tableau sko.

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
      exists (T'' : TableauTree), T'' <> Proofs.Leaf /\
                               replace_child B T T'' = Some (tree (last s (mkLeaf sko))).
  Proof using Type.
    intros R. induction R as [ l | R1 IHR1 r R2 IHR2 ];
      intros ??? hbranchof e.

    - cbn in e. injection e => <-; cbn.
      have [ T'' [ hnleaf eT'' ] ] := is_branch_of_get_child_at hbranchof.
      exists T''. split; auto.
      now apply replace_child_get_child_at.

    (* TODO: factor out the boilerplate code *)
    - destruct r; cbn in e.

      + destruct (get_neg_neg f) eqn:ef; try easy.
        destruct (expand_tableau_branch__aux (Some (Ctx.elements t)) None B T) eqn:hexpand;
          try easy.
        destruct (RuleTree_to_Sequence__aux _ _ _) eqn:eseq1; try easy.
        have hbranchof0 := is_branch_of_extend_left hbranchof hexpand.
        injection e => <-.

        destruct (IHR1 (B ++ [Left])%list {| tree := t0; symbols := symbols T |}
                    s0 hbranchof0 eseq1) as (T'' & hnleaf & hreplace).
        rewrite last_cons.
        * eapply RuleTree_to_Sequence_not_nil; eauto.
        * rewrite -hreplace. eapply replace_expand_Left; eauto.

      + destruct (get_neg_or f) eqn:ef; try easy.
        destruct (expand_tableau_branch__aux (Some (Ctx.elements t)) None B T) eqn:hexpand;
          try easy.
        destruct (RuleTree_to_Sequence__aux _ _ _) eqn:eseq1; try easy.
        have hbranchof0 := is_branch_of_extend_left hbranchof hexpand.
        injection e => <-.

        destruct (IHR1 (B ++ [Left])%list {| tree := t0; symbols := symbols T |}
                    s0 hbranchof0 eseq1) as (T'' & hnleaf & hreplace).
        rewrite last_cons.
        * eapply RuleTree_to_Sequence_not_nil; eauto.
        * rewrite -hreplace. eapply replace_expand_Left; eauto.

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
          as (T1' & hnleaf1 & hreplace1).

        have hneq : (B ++ [Right])%list <> (B ++ [Left])%list.
        { clear. induction B; try easy.
          cbn; intro e; apply IHB; injection e => -> //. }
        have hbranchof2' := is_branch_of_replace_child_oth hbranchof2 hbranchof1 hneq hreplace1.

        (* The tree that replaces the right child. *)
        destruct (IHR2 (B ++ [Right])%list (last s0 (mkLeaf sko)) s1 hbranchof2' etree2)
          as (T2' & hnleaf2 & hreplace2).

        exists (Proofs.Node T1' Gamma T2'); split; try easy.
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
                    s1 hbranchof0 etree) as (T'' & hnleaf & hreplace).
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
                    s0 hbranchof0 etree) as (T'' & hnleaf & hreplace).
        rewrite last_cons.
        * eapply RuleTree_to_Sequence_not_nil; eauto.
        * rewrite -hreplace; eapply replace_expand_Left; eauto.
  Qed.

  (* TODO: Custom induction scheme to give all the hypotheses we can have. *)
  (* Lemma RuleTree_to_Sequence_ind : *)
  (*   forall (P : RuleTree -> Prop) {R : RuleTree} {B : Branch} {T : Tableau} {s : Sequence sko}, *)
  (*     RuleTree_to_Sequence__aux B T R = Some s -> is_branch_of B T -> *)
  (*     (forall (T : Tableau) (l : option (Form * Form)) (s : Sequence sko), s = [T] -> P (Leaf l)) -> *)
  (*     (forall (R1 R2 : RuleTree) (F : Form), *)
  (*         P R1 -> *)
  (*         (forall (Gamma Gamma' : Ctx.t) (T0 : TableauTree) (s s1 : Sequence sko) *)
  (*            (B : Branch) (T : Tableau), *)
  (*             get_context B T = Gamma' /\ *)
  (*             get_context (B ++ [Left])%list T0 = (Ctx.elements Gamma ++ Ctx.elements Gamma')%list /\ *)
  (*             RuleTree_to_Sequence__aux B T (Node R1 (AlphaNegNeg F) R2) = Some s /\ *)
  (*             get_neg_neg F = Some Gamma /\ *)
  (*             expand_tableau_branch__aux (Some (Ctx.elements Gamma)) None B T = Some T0 /\ *)
  (*             RuleTree_to_Sequence__aux (B ++ [Left])%list *)
  (*                                     {| tree := T0; symbols := symbols T |} R1 = Some s1 /\ *)
  (*             is_branch_of (B ++ [Left])%list T0) -> *)
  (*         P (Node R1 (AlphaNegNeg F) R2)) -> *)
  (*     (forall (R1 R2 : RuleTree) (F : Form) (Gamma Gamma' : Ctx.t) (T0 : TableauTree) (s s1 : Sequence sko) *)
  (*         (B : Branch) (T : Tableau), *)
  (*         P R1 -> get_context B T = Gamma' -> *)
  (*         get_context (B ++ [Left])%list T0 = (Ctx.elements Gamma ++ Ctx.elements Gamma')%list -> *)
  (*         RuleTree_to_Sequence__aux B T (Node R1 (AlphaNegOr F) R2) = Some s -> *)
  (*         get_neg_or F = Some Gamma -> *)
  (*         expand_tableau_branch__aux (Some (Ctx.elements Gamma)) None B T = Some T0 -> *)
  (*         RuleTree_to_Sequence__aux (B ++ [Left])%list *)
  (*                                 {| tree := T0; symbols := symbols T |} R1 = Some s1 -> *)
  (*         is_branch_of (B ++ [Left])%list T0 -> *)
  (*         P (Node R1 (AlphaNegOr F) R2)) -> *)
  (*     (forall (R1 R2 : RuleTree) (F : Form) (Gamma Gamma1 Gamma2 : Ctx.t) (T0 : TableauTree) *)
  (*        (s s1 s2 : Sequence sko) (B : Branch) (T : Tableau), *)
  (*         P R1 -> P R2 -> get_context B T = Gamma -> *)
  (*         get_context (B ++ [Left])%list T0 = (Ctx.elements Gamma1 ++ Ctx.elements Gamma)%list -> *)
  (*         get_context (B ++ [Right])%list T0 = get_context (B ++ [Right])%list *)
  (*                                                (last s1 (mkLeaf sko)) -> *)
  (*         RuleTree_to_Sequence__aux B T (Node R1 (BetaOr F) R2) = Some s -> *)
  (*         get_or F = Some (Gamma1, Gamma2) -> *)
  (*         expand_tableau_branch__aux (Some (Ctx.elements Gamma1)) *)
  (*           (Some (Ctx.elements Gamma2)) B T = Some T0 -> *)
  (*         RuleTree_to_Sequence__aux (B ++ [Left])%list *)
  (*                                 {| tree := T0; symbols := symbols T |} R1 = Some s1 -> *)
  (*         RuleTree_to_Sequence__aux (B ++ [Right])%list (last s1 (mkLeaf sko)) R2 = Some s2 -> *)
  (*        is_branch_of (B ++ [Left])%list T0 -> *)
  (*        is_branch_of (B ++ [Right])%list (last s1 (mkLeaf sko)) -> *)
  (*        P (Node R1 (BetaOr F) R2)) -> *)
  (*     (forall (R1 R2 : RuleTree) (F : Form) (G : Form) (T0 : TableauTree) (s s1 : Sequence sko) *)
  (*        (x : string) (B : Branch) (T : Tableau) (Gamma : Ctx.t), *)
  (*         P R1 -> get_context B T = Gamma -> *)
  (*         get_context (B ++ [Left])%list T0 = (G{0 \to Free x} :: Ctx.elements Gamma)%list -> *)
  (*         RuleTree_to_Sequence__aux B T (Node R1 (GammaAll F x) R2) = Some s -> *)
  (*         get_all F = Some G -> *)
  (*         expand_tableau_branch__aux (Some [G{0 \to Free x}]) None B T = Some T0 -> *)
  (*         RuleTree_to_Sequence__aux (B ++ [Left])%list *)
  (*                                 {| tree := T0; symbols := symbols T |} R1 = Some s1 -> *)
  (*         is_branch_of (B ++ [Left])%list T0 -> *)
  (*         P (Node R1 (GammaAll F x) R2)) -> *)
  (*     (forall (R1 R2 : RuleTree) (F : Form) (G : Form) (T0 : TableauTree) (s s1 : Sequence sko) *)
  (*        (t : Term) (f : string) (B : Branch) (T : Tableau) (Gamma : Ctx.t), *)
  (*         P R1 -> get_context B T = Gamma -> *)
  (*         get_context (B ++ [Left])%list T0 = (G{0 \to t} :: Ctx.elements Gamma)%list -> *)
  (*         RuleTree_to_Sequence__aux B T (Node R1 (DeltaNegAll F t) R2) = Some s -> *)
  (*         get_neg_all F = Some G -> get_symbol t = Some f -> *)
  (*         expand_tableau_branch__aux (Some [G{0 \to t}]) None B T = Some T0 -> *)
  (*         RuleTree_to_Sequence__aux (B ++ [Left])%list *)
  (*                                 {| tree := T0; symbols := add_symbol f F (symbols T) |} *)
  (*                                 R1 = Some s1 -> *)
  (*         is_branch_of (B ++ [Left])%list T0 -> *)
  (*         P (Node R1 (DeltaNegAll F t) R2)) -> *)
  (*     P R. *)
  (* Proof using Type. *)
  (*   intros ??; induction R; intros ??? etree hbranchof hleaf hnegneg hnegor hor hall hnegall. *)
  (*   - apply hleaf with (T := T) (s := s); cbn in etree. injection etree => -> //. *)
  (*   - destruct r. *)
  (*     + have etreesave := etree. *)
  (*       cbn in etree; destruct (get_neg_neg _) eqn:enegneg; try easy. *)
  (*       destruct (expand_tableau_branch__aux _ _ _ _) eqn:hexpand; try easy. *)
  (*       destruct (RuleTree_to_Sequence__aux _ _ _) eqn:eseq1; try easy. *)
  (*       eapply hnegneg; eauto. *)
  (*       * eapply IHR1; eauto. *)
  (*         eapply is_branch_of_extend_left; eauto. *)
  (*       * intros; repeat split; auto. *)
  (*       * have hbranchof' := is_branch_of_extend_left hbranchof hexpand. *)
  (*         have econ := get_context_extend_left hbranchof hexpand eq_refl. *)
  (*         auto. *)
  (*       * eapply is_branch_of_extend_left; eauto. *)
  (*     + have etreesave := etree. *)
  (*       cbn in etree; destruct (get_neg_or _) eqn:eget; try easy. *)
  (*       destruct (expand_tableau_branch__aux _ _ _ _) eqn:hexpand; try easy. *)
  (*       destruct (RuleTree_to_Sequence__aux _ _ _) eqn:eseq1; try easy. *)
  (*       eapply hnegor; eauto. *)
  (*       * eapply IHR1; eauto. *)
  (*         eapply is_branch_of_extend_left; eauto. *)
  (*       * have hbranchof' := is_branch_of_extend_left hbranchof hexpand. *)
  (*         have econ := get_context_extend_left hbranchof hexpand eq_refl. *)
  (*         auto. *)
  (*       * eapply is_branch_of_extend_left; eauto. *)
  (*     + have etreesave := etree. *)
  (*       cbn in etree; destruct (get_or _) eqn:eget; try easy. *)
  (*       destruct (expand_tableau_branch__aux _ _ _ _) eqn:hexpand; try easy. *)
  (*       destruct (RuleTree_to_Sequence__aux (B ++ [Left])%list _ _) eqn:eseq1; try easy. *)
  (*       destruct (RuleTree_to_Sequence__aux (B ++ [Right])%list _ _) eqn:eseq2; try easy. *)
  (*       have hbranchof1 : is_branch_of (B ++ [Left])%list {| tree := t; symbols := symbols T |} *)
  (*         := is_branch_of_extend_left hbranchof hexpand. *)
  (*       have hbranchof2 := is_branch_of_extend_right hbranchof hexpand. *)
  (*       have [ T1' [ hnleaf ereplace ] ] := RuleTree_to_Sequence_branch hbranchof1 eseq1. *)
  (*       have ebranch : (B ++ [Right])%list <> (B ++ [Left])%list. *)
  (*       { clear; induction B; cbn; intro; congruence. } *)

  (*       have hbranchof2' : is_branch_of (B ++ [Right])%list (last s0 (mkLeaf sko)). *)
  (*       { eapply is_branch_of_replace_child_oth. *)
  (*         3: eassumption. *)
  (*         all: eauto. } *)
  (*       have ectx2' : get_context (B ++ [Right])%list t = get_context (B ++ [Right])%list *)
  (*                                                            (last s0 (mkLeaf sko)). *)
  (*       { eapply get_context_replace_child_oth. *)
  (*         3: eassumption. *)
  (*         all: eauto. } *)
  (*       eapply hor; eauto. *)
  (*       * have econ := get_context_extend_left hbranchof hexpand eq_refl. *)
  (*         auto. *)
  (*       * now destruct p. *)
  (*     + have etreesave := etree. *)
  (*       cbn in etree; destruct (get_all _) eqn:eget; try easy. *)
  (*       destruct (expand_tableau_branch__aux _ _ _ _) eqn:hexpand; try easy. *)
  (*       destruct (RuleTree_to_Sequence__aux _ _ _) eqn:eseq1; try easy. *)
  (*       eapply hall; eauto. *)
  (*       * eapply IHR1; eauto. *)
  (*         eapply is_branch_of_extend_left; eauto. *)
  (*       * have hbranchof' := is_branch_of_extend_left hbranchof hexpand. *)
  (*         have econ := get_context_extend_left hbranchof hexpand eq_refl. *)
  (*         auto. *)
  (*       * eapply is_branch_of_extend_left; eauto. *)
  (*     + have etreesave := etree. *)
  (*       cbn in etree; destruct (get_neg_all _) eqn:eget; try easy. *)
  (*       destruct (get_symbol t) eqn:esymb; try easy. *)
  (*       destruct (expand_tableau_branch__aux _ _ _ _) eqn:hexpand; try easy. *)
  (*       destruct (RuleTree_to_Sequence__aux _ _ _) eqn:eseq1; try easy. *)
  (*       eapply hnegall; eauto. *)
  (*       * eapply IHR1; eauto. *)
  (*         eapply is_branch_of_extend_left; eauto. *)
  (*       * have hbranchof' := is_branch_of_extend_left hbranchof hexpand. *)
  (*         have econ := get_context_extend_left hbranchof hexpand eq_refl. *)
  (*         auto. *)
  (*       * eapply is_branch_of_extend_left; eauto. *)
  (* Qed. *)

  (** Then, we can show that whenever the [CheckProof__aux] algorithm finds a result,
      then the algorithm [RuleTree_to_Sequence__aux] converts the [RuleTree] to a [Sequence]
      successfully. *)
  Lemma CheckProof_Some_RuleTree_to_Sequence_Some__aux :
    forall {Gamma : list Form} {sigma : Substitution string Term} {R : RuleTree}
      {B : Branch} {T : Tableau} {record record' : sko_record sko} {func_symbs : SetOfString},
      CheckProof__aux sko func_symbs Gamma sigma record R = ret {| status := true; symbs := record' |} ->
      is_branch_of B T -> get_context B T = Gamma ->
      exists (s : Sequence sko), RuleTree_to_Sequence__aux B T R = Some s.
  Proof using Type.
    intros ???????? e hbranchof econ. generalize dependent Gamma. generalize dependent T.
    revert B record record' func_symbs. induction R; intros ????? hbranchof ? e econ.

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

        destruct (IHR1 (B ++ [Left])%list record record' func_symbs T0 hbranchof0
                    (Ctx.union l Gamma) hnext ectx) as (s & hseq).
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

        destruct (IHR1 (B ++ [Left])%list record record' func_symbs T0 hbranchof0
                    (Ctx.union l Gamma) hnext ectx) as (s & hseq).
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
        destruct (IHR1 (B ++ [Left])%list record symbs func_symbs T0 hbranchof1
                    (Ctx.union l Gamma) hnext1 ectx1) as (s1 & hseq1).

        have [ T1' [ hnleaf ereplace ] ] := RuleTree_to_Sequence_branch hbranchof1 hseq1.
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
          all: eauto. }
        rewrite ectx2' in ectx2; auto.

        destruct (IHR2 (B ++ [Right])%list symbs record' func_symbs (last s1 (mkLeaf sko))
                    hbranchof2' (Ctx.union l' Gamma) hnext2 ectx2) as (s2 & hseq2).

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

        destruct (IHR1 (B ++ [Left])%list record record' func_symbs T0 hbranchof0
                    (Ctx.add (F{0 \to Free s}) Gamma) hnext ectx) as (seq & hseq).
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

        destruct (IHR1 (B ++ [Left])%list (add_symbol f0 f record) record' func_symbs
                       {| tree := T0; symbols := (add_symbol f0 f (symbols T0)) |}
                       hbranchof0 (Ctx.add (F{0 \to t}) Gamma) hnext ectx) as (seq & hseq).
        exists (T :: seq); cbn.
        rewrite eget (expand_tableau_branch_Some__aux sko hexpand) esymbol esymbs hseq.
        reflexivity.
  Qed.

  (** Of course, we can make a [Sequence] out of a first tableau which has the single node [Gamma] *)
  Definition RuleTree_to_Sequence (Gamma : list Form) (R : RuleTree) : option (Sequence sko) :=
    RuleTree_to_Sequence__aux EmptyBranch (mkTableau sko Gamma) R.

  Lemma CheckProof_Some_RuleTree_to_Sequence_Some :
    forall {Gamma : list Form} {sigma : Substitution string Term} {R : RuleTree}
      {record record' : sko_record sko} {func_symbs : SetOfString},
      CheckProof__aux sko func_symbs Gamma sigma record R = ret {| status := true; symbs := record' |} ->
      exists (s : Sequence sko), RuleTree_to_Sequence Gamma R = Some s.
  Proof using Type.
    intros ?????? e. cbn.
    eapply CheckProof_Some_RuleTree_to_Sequence_Some__aux; eauto.
    apply is_branch_of_nil.
  Qed.

  (** The set of symbols returned by the [CheckProof__aux] algorithm is exactly the
      set of symbols of the last tableau of the sequence returned by
      [RuleTree_to_Sequence__aux]. *)
  Lemma RuleTree_to_Sequence_symbols :
    forall {R : RuleTree} {sigma : Substitution string Term} {B : Branch}
      {T : Tableau} {record : sko_record sko} {func_symbs : SetOfString} {s : Sequence sko},
      is_branch_of B T ->
      CheckProof__aux sko func_symbs (get_context B T) sigma (symbols T) R =
        ret {| status := true; symbs := record |} ->
      RuleTree_to_Sequence__aux B T R = Some s ->
      record = symbols (last s (mkLeaf sko)).
  Proof using Type.
    intro R; induction R; intros ?????? hbranchof esrch eseq.

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
        rewrite (IHR1 sigma (B ++ [Left])%list _ _ _ s0 hbranchof1 esrch1 eseq1).
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
        rewrite (IHR1 sigma (B ++ [Left])%list _ _ _ s0 hbranchof1 esrch1 eseq1).
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

        have [ T1' [ hnleaf ereplace ] ] := RuleTree_to_Sequence_branch hbranchof1 eseq1.
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
          all: eauto. }

        eapply IHR2; eauto.
        rewrite -ectx2'; eauto.

      + apply gamma_rule_sound in esrch; destruct esrch as (F & eget & hin & esrch1).
        rewrite eget in eseq.
        destruct (expand_tableau_branch__aux _ _ _) eqn:hexpand; try easy.
        destruct (RuleTree_to_Sequence__aux _ _ _) eqn:eseq1; try easy.
        have ectx1 := get_context_extend_left hbranchof hexpand eq_refl.
        have hbranchof1 : is_branch_of (B ++ [Left])%list {| tree := t; symbols := symbols T |} :=
          is_branch_of_extend_left hbranchof hexpand.
        rewrite /Ctx.add /Ctx.elements in esrch1, ectx1; cbn in ectx1; rewrite -ectx1 in esrch1.
        rewrite (IHR1 sigma (B ++ [Left])%list _ _ _ s1 hbranchof1 esrch1 eseq1).
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
        rewrite (IHR1 sigma (B ++ [Left])%list _ _ _ s0 hbranchof1 esrch1 eseq1).
        have hs0 : s0 <> [] by eapply RuleTree_to_Sequence_not_nil; eauto.
        injection eseq => <-; cbn. destruct s0; easy.
  Qed.
End RuleTreeToSequence.

Section Soundness.
  Context (sko : Skolemization).

  Let Tableau := Tableau sko.

  (** Now, we show that, in the same setting, the sequence gotten from [RuleTree_to_Sequence]
      is actually an expansion sequence. A small lemma that will be useful later on is that
      the tableau with which we call the auxiliary function and the second element of the
      sequence (if it exists) give an expansion step. *)
  Lemma RuleTree_to_Sequence_snd_expansion :
    forall {R : RuleTree} {sigma : Substitution string Term} {B : Branch}
      {T T' : Tableau} {record : sko_record sko} {s : Sequence sko} {func_symbs : SetOfString},
      is_branch_of B T -> preserves_function_symbols T func_symbs ->
      CheckProof__aux sko func_symbs (get_context B T) sigma (symbols T) R =
        ret {| status := true; symbs := record |} ->
      RuleTree_to_Sequence__aux B T R = Some s -> s.(1) = Some T' ->
      T |> T'.
  Proof using Type.
    intro R; destruct R; intros ??????? hbranchof hpres esrch eseq esnd.

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
        have hsko' : sko t (Neg (All f)) (symbols T) (fv (get_context B T))
                       (function_symbols (get_all_formulas T)) = true.
        { rewrite hpres //. }
        eapply expansion_NegAll with (hsko := hsko'); eauto.
        * apply in_context_is_on_branch; eauto.
        * cbn in eget. change (Neg f {0 \to t}) with ((Neg f) {0 \to t}); injection eget => ->.
          cbn; now rewrite hexpand.
        * cbn. have esymb1 := symbol_sound sko hsko.
          have esymb2 := symbol_sound sko hsko'.
          rewrite esymb1 in esymb2; injection esymb2 => -> //.
  Qed.

  Lemma preserves_function_symbols_None :
    forall (T : Tableau) (func_symbs : SetOfString),
      function_symbols (@None (list Form)) \subseteq func_symbs \union to_set (symbols T).
  Proof using Type. intros ?? f contra. now apply empty_spec in contra. Qed.

  Lemma preserves_function_symbols_get_neg_neg :
    forall {F : Form} {l : Ctx.t} {B : Branch} {T : Tableau} {func_symbs : SetOfString},
      preserves_function_symbols T func_symbs -> is_branch_of B T -> get_neg_neg F = Some l ->
      F \in get_context B T ->
      function_symbols (Some (Ctx.elements l)) \subseteq func_symbs \union to_set (symbols T).
  Proof using Type.
    intros ????? hpres hbranchof hnegneg hin f hin'.
    destruct F; try easy. destruct F; try easy.
    cbn in hnegneg; injection hnegneg => el. rewrite -el /Ctx.singleton in hin'.
    rewrite union_spec in hin'; destruct hin' as [contra | hin'].
    - now apply empty_spec in contra.
    - change (set_in f (function_symbols (Neg (Neg F)))) in hin'.
      red in hpres. rewrite -hpres. eapply GetFunctSymbols_in; eauto.
      eapply in_get_ctx_in_all_formulas; eauto.
  Qed.

  Lemma preserves_function_symbols_get_neg_or :
    forall {F : Form} {l : Ctx.t} {B : Branch} {T : Tableau} {func_symbs : SetOfString},
      preserves_function_symbols T func_symbs -> is_branch_of B T -> get_neg_or F = Some l ->
      F \in get_context B T ->
      function_symbols (Some (Ctx.elements l)) \subseteq func_symbs \union to_set (symbols T).
  Proof using Type.
    intros ????? hpres hbranchof hnegor hin f hin'.
    destruct F; try easy. destruct F; try easy.
    cbn in hnegor; injection hnegor => el.
    rewrite -el /Ctx.elements /Ctx.add /Ctx.singleton in hin'.
    change (set_in f (function_symbols (Neg (Or F1 F2)))) in hin'.
    red in hpres. rewrite -hpres. eapply GetFunctSymbols_in; eauto.
    eapply in_get_ctx_in_all_formulas; eauto.
  Qed.

  Lemma preserves_function_symbols_get_or1 :
    forall {F : Form} {l1 l2 : Ctx.t} {B : Branch} {T : Tableau} {func_symbs : SetOfString},
      preserves_function_symbols T func_symbs -> is_branch_of B T -> get_or F = Some (l1, l2) ->
      F \in get_context B T ->
      function_symbols (Some (Ctx.elements l1)) \subseteq func_symbs \union to_set (symbols T).
  Proof using Type.
    intros ?????? hpres hbranchof hor hin f hin'.
    destruct F; try easy. cbn in hor; injection hor => el2 el1.
    rewrite -el1 /Ctx.singleton in hin'.
    change (set_in f (function_symbols F1)) in hin'.
    have hin'' : set_in f (function_symbols (Or F1 F2)).
    { rewrite union_spec; now left. }
    red in hpres. rewrite -hpres. eapply GetFunctSymbols_in; eauto.
    eapply in_get_ctx_in_all_formulas; eauto.
  Qed.

  Lemma preserves_function_symbols_get_or2 :
    forall {F : Form} {l1 l2 : Ctx.t} {B : Branch} {T : Tableau} {func_symbs : SetOfString},
      preserves_function_symbols T func_symbs -> is_branch_of B T -> get_or F = Some (l1, l2) ->
      F \in get_context B T ->
      function_symbols (Some (Ctx.elements l2)) \subseteq func_symbs \union to_set (symbols T).
  Proof using Type.
    intros ?????? hpres hbranchof hor hin f hin'.
    destruct F; try easy. cbn in hor; injection hor => el2 el1.
    rewrite -el2 /Ctx.singleton in hin'.
    change (set_in f (function_symbols F2)) in hin'.
    have hin'' : set_in f (function_symbols (Or F1 F2)).
    { rewrite union_spec; now right. }
    red in hpres. rewrite -hpres. eapply GetFunctSymbols_in; eauto.
    eapply in_get_ctx_in_all_formulas; eauto.
  Qed.

  Lemma preserves_function_symbols_get_all :
    forall {F G : Form} {B : Branch} {T : Tableau} {func_symbs : SetOfString} (x : string),
      preserves_function_symbols T func_symbs -> is_branch_of B T -> get_all F = Some G ->
      F \in get_context B T ->
      function_symbols (Some [G{0 \to Free x}]) \subseteq func_symbs \union to_set (symbols T).
  Proof using Type.
    intros ?????? hpres hbranchof hall hin f hin'.
    destruct F; try easy.
    cbn in hall; injection hall => el.
    rewrite -el in hin'.
    have h : function_symbols (All F) = function_symbols (F {0 \to Free x}) by admit.
    change (set_in f (function_symbols (F {0 \to Free x}))) in hin'.
    rewrite -h in hin'. red in hpres. rewrite -hpres. eapply GetFunctSymbols_in; eauto.
    eapply in_get_ctx_in_all_formulas; eauto.
  Admitted.

  Lemma preserves_function_symbols_get_neg_all :
    forall {F G : Form} {B : Branch} {T : Tableau} {func_symbs : SetOfString} (t : Term)
      (f : string),
      preserves_function_symbols T func_symbs -> is_branch_of B T -> get_neg_all F = Some G ->
      F \in get_context B T -> function_symbols t = singleton f ->
      function_symbols (Some [G{0 \to t}]) \subseteq func_symbs \union to_set (add_symbol f F (symbols T)).
  Proof using Type.
    intros ??????? hpres hbranchof hnegall hin esymb f hin'.
    destruct F; try easy. destruct F; try easy.
    cbn in hnegall; injection hnegall => el.
    rewrite -el in hin'.
    have h : function_symbols (Neg (All F)) \union function_symbols t =
               function_symbols (Neg F{0 \to t}) by admit.
    change (set_in f (function_symbols (Neg F {0 \to t}))) in hin'.
    rewrite -h in hin'. red in hpres.
    have hsko : to_set (add_symbol f0 (Neg (All F)) (symbols T)) =
                  add f0 (to_set (symbols T)) by admit.
    rewrite hsko; rewrite !union_spec in hin' |- *; destruct hin'.
    - enough (h0 : set_in f (function_symbols (get_all_formulas T))).
      { rewrite hpres in h0; rewrite union_spec in h0; destruct h0.
        - now left.
        - now do 2 right. }
      eapply GetFunctSymbols_in; eauto.
      eapply in_get_ctx_in_all_formulas; eauto.
    - right; left. now rewrite -esymb.
  Admitted.

  Lemma RuleTree_to_Sequence_preserves_function_symbols_last :
  forall {R : RuleTree} {sigma : Substitution string Term} {B : Branch}
      {T : Tableau} {record : sko_record sko} {s : Sequence sko} {func_symbs : SetOfString},
      is_branch_of B T -> preserves_function_symbols T func_symbs ->
      RuleTree_to_Sequence__aux B T R = Some s ->
      CheckProof__aux sko func_symbs (get_context B T) sigma (symbols T) R =
        ret {| status := true; symbs := record |} ->
      preserves_function_symbols (last s (mkLeaf sko)) func_symbs.
  Proof.
    intros R; induction R as [ l | R1 IHR1 r R2 IHR2 ];
      intros ?????? hbranchof hpres eseq echk.

    - cbn in eseq; injection eseq => es. rewrite -es; now cbn.

    - destruct r; cbn in eseq.

      + have [ l [ eget [ hin esrch1 ] ] ] := alpha_rule_sound echk.
        rewrite eget in eseq.
        destruct (expand_tableau_branch__aux _ _ _ _) eqn:hexpand; try easy.
        destruct (RuleTree_to_Sequence__aux _ _ _) eqn:hseq; try easy.
        injection eseq => <-. rewrite last_cons.
        * eapply RuleTree_to_Sequence_not_nil; eauto.
        * eapply IHR1 with (B := (B ++ [Left])%list) (T := {| tree := t; symbols := symbols T |});
            eauto.
          -- eapply is_branch_of_extend_left; eauto.
          -- eapply extend_subset_preserves_function_symbols with
               (l := Some (Ctx.elements l)) (l' := None); eauto.
             ++ eapply preserves_function_symbols_get_neg_neg; eauto.
             ++ apply preserves_function_symbols_None.
             ++ cbn; now rewrite hexpand.
          -- cbn; erewrite get_context_extend_left; eauto.

      + have [ l [ eget [ hin esrch1 ] ] ] := alpha_rule_sound echk.
        rewrite eget in eseq.
        destruct (expand_tableau_branch__aux _ _ _ _) eqn:hexpand; try easy.
        destruct (RuleTree_to_Sequence__aux _ _ _) eqn:hseq; try easy.
        injection eseq => <-. rewrite last_cons.
        * eapply RuleTree_to_Sequence_not_nil; eauto.
        * eapply IHR1 with (B := (B ++ [Left])%list) (T := {| tree := t; symbols := symbols T |});
            eauto.
          -- eapply is_branch_of_extend_left; eauto.
          -- eapply extend_subset_preserves_function_symbols with
               (l := Some (Ctx.elements l)) (l' := None); eauto.
             ++ eapply preserves_function_symbols_get_neg_or; eauto.
             ++ apply preserves_function_symbols_None.
             ++ cbn; now rewrite hexpand.
          -- cbn; erewrite get_context_extend_left; eauto.

      + have [ l [ l' [ symbs1 [ eget [ hin [ esrch1 esrch2 ] ] ] ] ] ] := beta_rule_sound echk.
        rewrite eget in eseq.
        destruct (expand_tableau_branch__aux _ _ _ _) eqn:hexpand; try easy.
        destruct (RuleTree_to_Sequence__aux _ _ _) eqn:hseq1; try easy.
        destruct (RuleTree_to_Sequence__aux (B ++ [Right])%list _ _) eqn:hseq2; try easy.
        injection eseq => <-. rewrite app_comm_cons last_app.
        * eapply RuleTree_to_Sequence_not_nil; eauto.
        * eapply IHR2 with (B := (B ++ [Right])%list) (T := last s0 (mkLeaf sko)).
          -- admit. (* already done in other places *)
          -- eapply IHR1 with (B := (B ++ [Left])%list)
                              (T := {| tree := t; symbols := symbols T |});
               eauto.
             ++ eapply is_branch_of_extend_left; eauto.
             ++ eapply extend_subset_preserves_function_symbols with
                  (l := Some (Ctx.elements l)) (l' := Some (Ctx.elements l')); eauto.
                ** eapply preserves_function_symbols_get_or1; eauto.
                ** eapply preserves_function_symbols_get_or2; eauto.
                ** cbn; now rewrite hexpand.
             ++ cbn; erewrite get_context_extend_left; eauto.
          -- exact hseq2.
          -- erewrite <-esrch2; f_equal.
             ++ admit. (* already done in other places *)
             ++ admit. (* already done in other places. *)

      + have [ G [ eget [ hin esrch1 ] ] ] := gamma_rule_sound echk.
        rewrite eget in eseq.
        destruct (expand_tableau_branch__aux _ _ _ _) eqn:hexpand; try easy.
        destruct (RuleTree_to_Sequence__aux _ _ _) eqn:hseq; try easy.
        injection eseq => <-. rewrite last_cons.
        * eapply RuleTree_to_Sequence_not_nil; eauto.
        * eapply IHR1 with (B := (B ++ [Left])%list) (T := {| tree := t; symbols := symbols T |});
            eauto.
          -- eapply is_branch_of_extend_left; eauto.
          -- eapply extend_subset_preserves_function_symbols with
               (l := Some [G{0 \to Free s0}]) (l' := None); eauto.
             ++ eapply preserves_function_symbols_get_all; eauto.
             ++ apply preserves_function_symbols_None.
             ++ cbn; now rewrite hexpand.
          -- cbn; erewrite get_context_extend_left; eauto.
             rewrite /Ctx.add in esrch1; cbn. eassumption.

      + have [ f0 [ G [ eget [ hin [ hsko [ esymb esrch1 ] ] ] ] ] ] := delta_rule_sound echk.
        rewrite eget in eseq. destruct (get_symbol _) eqn:esymb'; try easy.
        destruct (expand_tableau_branch__aux _ _ _ _) eqn:hexpand; try easy.
        destruct (RuleTree_to_Sequence__aux _ _ _) eqn:hseq; try easy.
        injection eseq => <-. rewrite last_cons.
        * eapply RuleTree_to_Sequence_not_nil; eauto.
        * eapply IHR1 with (B := (B ++ [Left])%list)
                           (T := {| tree := t0; symbols := add_symbol a f (symbols T) |}); eauto.
          -- eapply is_branch_of_extend_left; eauto.
          -- eapply extend_subset_preserves_function_symbols' with
               (l := Some [G{0 \to t}]) (l' := None); eauto.
             ++ eapply preserves_function_symbols_get_neg_all; eauto.
                rewrite (is_func hsko); rewrite (symbol_sound sko hsko) in esymb'.
                injection esymb' => ->.
                cbn; rewrite set_fold_left; apply set_ext; intros g; split; intros hin0.
                ** rewrite union_spec in hin0; destruct hin0; auto.
                   (* todo: args sound i.e. only free variables *) admit.
                ** rewrite union_spec; now left.
             ++ apply preserves_function_symbols_None.
          -- cbn; erewrite get_context_extend_left; eauto.
             rewrite /Ctx.add in esrch1; cbn. injection esymb => ->.
             eassumption.
  Admitted.

  Lemma CheckProof_Some_RuleTree_to_Sequence_is_expansion_sequence :
    forall {R : RuleTree} {sigma : Substitution string Term} {B : Branch}
      {T : Tableau} {record : sko_record sko} {s : Sequence sko} {func_symbs : SetOfString},
      is_branch_of B T -> preserves_function_symbols T func_symbs ->
      CheckProof__aux sko func_symbs (get_context B T) sigma (symbols T) R =
        ret {| status := true; symbs := record |} ->
      RuleTree_to_Sequence__aux B T R = Some s ->
      is_expansion_sequence s.
  Proof using Type.
    intro R; induction R; intros ?????? hbranchof hpres esrch eseq.

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
        have hsubl := preserves_function_symbols_get_neg_neg hpres hbranchof eget hin.
        have hpres1 := extend_subset_preserves_function_symbols sko func_symbs hbranchof hpres
                         hsubl (preserves_function_symbols_None T func_symbs).
        specialize (hpres1 {| tree := t; symbols := symbols T |}); cbn in hpres1.
        rewrite hexpand in hpres1; specialize (hpres1 eq_refl).
        rewrite /Ctx.union /Ctx.elements in esrch1, ectx1; rewrite -ectx1 in esrch1.
        specialize (IHR1 sigma (B ++ [Left])%list {| tree := t; symbols := symbols T |}
                      record s0 func_symbs hbranchof1 hpres1 esrch1 eseq1).
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
        have hsubl := preserves_function_symbols_get_neg_or hpres hbranchof eget hin.
        have hpres1 := extend_subset_preserves_function_symbols sko func_symbs hbranchof hpres
                         hsubl (preserves_function_symbols_None T func_symbs).
        specialize (hpres1 {| tree := t; symbols := symbols T |}); cbn in hpres1.
        rewrite hexpand in hpres1; specialize (hpres1 eq_refl).
        rewrite /Ctx.union /Ctx.elements in esrch1, ectx1; rewrite -ectx1 in esrch1.
        specialize (IHR1 sigma (B ++ [Left])%list {| tree := t; symbols := symbols T |}
                      record s0 func_symbs hbranchof1 hpres1 esrch1 eseq1).
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
        have hsubl1 := preserves_function_symbols_get_or1 hpres hbranchof eget hin.
        have hsubl2 := preserves_function_symbols_get_or2 hpres hbranchof eget hin.
        have hpres1 := extend_subset_preserves_function_symbols sko func_symbs hbranchof hpres
                         hsubl1 hsubl2.
        specialize (hpres1 {| tree := t; symbols := symbols T |}); cbn in hpres1.
        rewrite hexpand in hpres1; specialize (hpres1 eq_refl).

        specialize (IHR1 sigma (B ++ [Left])%list {| tree := t; symbols := symbols T |}
                      symbs1 s0 func_symbs hbranchof1 hpres1 esrch1 eseq1).

        have [T1' [ hnleaf ereplace ] ] := RuleTree_to_Sequence_branch hbranchof1 eseq1.
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
          all: eauto. }
        rewrite ectx2' in esrch2; auto.
        have esymbs2 : symbols (last s0 (mkLeaf sko)) = symbs1.
        { symmetry; eapply RuleTree_to_Sequence_symbols.
          3: eauto.
          - apply hbranchof1.
          - cbn. apply esrch1. }
        have hpres2 := RuleTree_to_Sequence_preserves_function_symbols_last
                         hbranchof1 hpres1 eseq1 esrch1.

        rewrite -esymbs2 in esrch2.
        specialize (IHR2 sigma (B ++ [Right])%list (last s0 (mkLeaf sko))
                      record s1 func_symbs hbranchof2' hpres2 esrch2 eseq2).

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
        have hsubl := preserves_function_symbols_get_all s0 hpres hbranchof eget hin.
        have hsubl' := preserves_function_symbols_None T func_symbs.
        have hpres1 := extend_subset_preserves_function_symbols sko func_symbs hbranchof hpres
                         hsubl hsubl'.
        specialize (hpres1 {| tree := t; symbols := symbols T |}); cbn in hpres1.
        rewrite hexpand in hpres1; specialize (hpres1 eq_refl).
        rewrite /Ctx.add /Ctx.elements in esrch1, ectx1. cbn in ectx1; rewrite -ectx1 in esrch1.
        specialize (IHR1 sigma (B ++ [Left])%list {| tree := t; symbols := symbols T |}
                      record s1 func_symbs hbranchof1 hpres1 esrch1 eseq1).
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
        have hapi : function_symbols t = singleton f0 by admit.
        have hsubl := preserves_function_symbols_get_neg_all t f0 hpres hbranchof eget hin hapi.
        have hsubl' := preserves_function_symbols_None
                         {| tree := t0; symbols := add_symbol f0 f (symbols T) |} func_symbs.
        change (to_set (add_symbol f0 f (symbols T))) with
          (to_set (symbols {| tree := t0; symbols := add_symbol f0 f (symbols T) |})) in hsubl.
        have hpres1 := extend_subset_preserves_function_symbols'
                         sko func_symbs hbranchof hpres hsubl hsubl'.
        cbn in hpres1; rewrite hexpand in hpres1; specialize (hpres1 eq_refl).
        rewrite /Ctx.add /Ctx.elements in esrch1, ectx1. cbn in ectx1; rewrite -ectx1 in esrch1.
        specialize (IHR1 sigma (B ++ [Left])%list
                         {| tree := t0; symbols := add_symbol f0 f (symbols T) |}
                      record s0 func_symbs hbranchof1 hpres1 esrch1 eseq1).
        intros i Ti Ti' ei ei'; destruct i.
        * rewrite nth_error_0 in ei.
          erewrite RuleTree_to_Sequence_hd in ei; eauto.
          injection ei => <-.
          eapply RuleTree_to_Sequence_snd_expansion; eauto.
        * injection eseq => es0. rewrite -es0 nth_error_S in ei, ei'.
          eapply IHR1; eauto.
  Admitted.

  Lemma CheckProof_Some_RuleTree_to_Sequence_closed :
    forall {R : RuleTree} {sigma : Substitution string Term} {B B' : Branch}
      {T : Tableau} {record : sko_record sko} {s : Sequence sko} {func_symbs : SetOfString},
      is_branch_of B T -> is_branch_of (B ++ B')%list (last s (mkLeaf sko)) ->
      CheckProof__aux sko func_symbs (get_context B T) sigma (symbols T) R =
        ret {| status := true; symbs := record |} ->
      RuleTree_to_Sequence__aux B T R = Some s ->
      is_branch_closed sko (last s (mkLeaf sko)) sigma (B ++ B')%list.
  Proof using Type.
    intros R; induction R; intros ??????? hbranchof hbranchof' esrch eseq.

    (* Case: [Leaf] *)
    - destruct o.
      + cbn in eseq; injection eseq => <-; subst.
        destruct p as (F & G); cbn in esrch.
        unfold closure_rule in esrch;
          destruct (formula_contradiction _ _ _ _) eqn:econtr;
          try easy.
        right; eapply @formula_contradiction_sound with (F := F) (G := G); cbn; eauto.
        unfold formula_contradiction in econtr |- *.
        apply andb_prop in econtr; destruct econtr as [hmem heq];
          apply andb_prop in hmem; destruct hmem as [hmemF hmemG].
        apply andb_true_intro; split; auto.
        apply andb_true_intro; split; rewrite !Ctx.mem_spec in hmemF, hmemG |- *;
          now apply get_context_app_fst.
      + cbn in eseq; injection eseq => <-; subst; cbn in esrch.
        unfold closure_rule in esrch;
          destruct (trivial_contradiction _) eqn:econtr;
          try easy.
        left; eapply trivial_contradiction_sound; cbn; eauto.
        unfold trivial_contradiction in econtr |- *; cbn.
        rewrite !Ctx.existsb_exists in econtr |- *.
        destruct econtr as (F & hin & e'); exists F; split; auto.
        now apply get_context_app_fst.

    (* Case: [AlphaNegNeg] *)
    - destruct r.
      + have eseq0 := eseq; have echk := esrch.
        apply alpha_rule_sound in esrch; destruct esrch as (l & eget & hin & esrch1).
        cbn in eseq; rewrite eget in eseq.
        destruct (expand_tableau_branch__aux _ _ _ _) eqn:hexpand; try easy.
        destruct (RuleTree_to_Sequence__aux (B ++ [Left])%list _ _) eqn:eseq1; try easy.
        have es : last s (mkLeaf sko) = last s0 (mkLeaf sko).
        { injection eseq => <-.
          rewrite last_cons //. eapply RuleTree_to_Sequence_not_nil; eauto. }
        rewrite !es in hbranchof' |- *.
        have hbranchof1 : is_branch_of (B ++ [Left])%list {| tree := t; symbols := symbols T |}
          := is_branch_of_extend_left hbranchof hexpand.
        have [T0 [ hnleaf e ] ] := RuleTree_to_Sequence_branch hbranchof1 eseq1.
        have ectx1 := get_context_extend_left hbranchof hexpand eq_refl.
        destruct B' as [|b' B'].
        * rewrite app_nil_r in hbranchof'; exfalso.
          have [ T'' [ hnleaf0 erepl ] ] := RuleTree_to_Sequence_branch hbranchof1 eseq1.
          have contra := replace_expanded_child_not_branch_Left hbranchof hnleaf0 hexpand erepl.
          easy.
        * destruct b'.
          -- change (B ++ Left :: B')%list with (B ++ [Left] ++ B')%list.
             rewrite app_assoc; eapply IHR1; eauto.
             ++ rewrite -app_assoc; auto.
             ++ rewrite ectx1; eauto.
          -- have [ T'' [ hnleaf0 erepl ] ] := RuleTree_to_Sequence_branch hbranchof1 eseq1.
             have contra := replace_expanded_child_not_subbranch hbranchof hnleaf0 hexpand erepl.
             have contra' := not_subbranch_no_ext_is_branch B' contra.
             rewrite -app_assoc in contra'; exfalso; now apply contra'.

      (* Case: [AlphaNegOr] *)
      + apply alpha_rule_sound in esrch; destruct esrch as (l & eget & hin & esrch1).
        have eseq0 := eseq.
        cbn in eseq; rewrite eget in eseq.
        destruct (expand_tableau_branch__aux _ _ _ _) eqn:hexpand; try easy.
        destruct (RuleTree_to_Sequence__aux (B ++ [Left])%list _ _) eqn:eseq1; try easy.
        have es : last s (mkLeaf sko) = last s0 (mkLeaf sko).
        { injection eseq => <-.
          rewrite last_cons //. eapply RuleTree_to_Sequence_not_nil; eauto. }
        rewrite !es in hbranchof' |- *.
        have hbranchof1 : is_branch_of (B ++ [Left])%list {| tree := t; symbols := symbols T |}
          := is_branch_of_extend_left hbranchof hexpand.
        have [T0 [ hnleaf e ] ] := RuleTree_to_Sequence_branch hbranchof1 eseq1.
        have ectx1 := get_context_extend_left hbranchof hexpand eq_refl.
        destruct B' as [|b' B'].
        * rewrite app_nil_r in hbranchof'; exfalso.
          have [ T'' [ hnleaf0 erepl ] ] := RuleTree_to_Sequence_branch hbranchof1 eseq1.
          have contra := replace_expanded_child_not_branch_Left hbranchof hnleaf0 hexpand erepl.
          easy.
        * destruct b'.
          -- change (B ++ Left :: B')%list with (B ++ [Left] ++ B')%list.
             rewrite app_assoc; eapply IHR1; eauto.
             ++ rewrite -app_assoc; auto.
             ++ rewrite ectx1; eauto.
          -- have [ T'' [ hnleaf0 erepl ] ] := RuleTree_to_Sequence_branch hbranchof1 eseq1.
             have contra := replace_expanded_child_not_subbranch hbranchof hnleaf0 hexpand erepl.
             have contra' := not_subbranch_no_ext_is_branch B' contra.
             rewrite -app_assoc in contra'; exfalso; now apply contra'.

      (* Case: [BetaOr] *)
      + apply beta_rule_sound in esrch; destruct esrch as
          (l1 & l2 & symbs & eget & hin & esrch1 & esrch2).
        have eseq0 := eseq.
        cbn in eseq; rewrite eget in eseq.
        destruct (expand_tableau_branch__aux _ _ _ _) eqn:hexpand; try easy.
        destruct (RuleTree_to_Sequence__aux (B ++ [Left])%list _ _) eqn:eseq1; try easy.
        destruct (RuleTree_to_Sequence__aux (B ++ [Right])%list _ _) eqn:eseq2; try easy.
        have es : last s (mkLeaf sko) = last s1 (mkLeaf sko).
        { injection eseq => <-.
          rewrite app_comm_cons. rewrite last_app //.
          eapply RuleTree_to_Sequence_not_nil; eauto. }
        rewrite !es in hbranchof' |- *.
        have hbranchof1 : is_branch_of (B ++ [Left])%list {| tree := t; symbols := symbols T |}
          := is_branch_of_extend_left hbranchof hexpand.
        have hbranchof2 := is_branch_of_extend_right hbranchof hexpand.
        have [T0 [ hnleaf e ] ] := RuleTree_to_Sequence_branch hbranchof1 eseq1.
        have ectx1 := get_context_extend_left hbranchof hexpand eq_refl.
        have ectx2 := get_context_extend_right hbranchof hexpand eq_refl.

        have [ T1' [ hnleaf1 ereplace ] ] := RuleTree_to_Sequence_branch hbranchof1 eseq1.
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
          all: eauto. }
        rewrite ectx2' in ectx2; auto.

        destruct B' as [|b' B'].
        * rewrite app_nil_r in hbranchof'; exfalso.
          have [ T'' [ hnleaf0 erepl ] ] := RuleTree_to_Sequence_branch hbranchof1 eseq1.
          have [ T2' [ hnleaf2 erepl2 ] ] := RuleTree_to_Sequence_branch hbranchof2' eseq2.
          cbn in ereplace.
          have contra := replace_expanded_child_not_branch_Right
                           hbranchof hnleaf1 hnleaf2 hexpand ereplace erepl2.
          easy.
        * destruct b'.
          -- have hbranchof0 : is_branch_of (B ++ Left :: B')%list (last s0 (mkLeaf sko)).
             { have [ T2' [ hnleaf2 erepl2 ] ] := RuleTree_to_Sequence_branch hbranchof2' eseq2.
               eapply is_branch_of_replace_child_oth_inv; eauto.
               now intro. }
            enough (hclosed0 :
                     is_branch_closed sko (last s0 (mkLeaf sko)) sigma (B ++ [Left] ++ B')%list).
            { have [ T2' [ hnleaf2 erepl2 ] ] := RuleTree_to_Sequence_branch hbranchof2' eseq2.
              destruct hclosed0 as [htriv | hcontr].
              - left. erewrite <-get_context_replace_child_oth.
                5: exact erepl2.
                all: eauto.
                intro. rewrite app_inv_head_iff in H.
                inversion H.
               - destruct hcontr as (F & G & econF & econG & esig).
                 right; exists F, G; repeat split; auto.
                 + erewrite <-get_context_replace_child_oth.
                   5: exact erepl2.
                   all: eauto.
                   intro. rewrite app_inv_head_iff in H.
                   inversion H.
                 + erewrite <-get_context_replace_child_oth.
                   5: exact erepl2.
                   all: eauto.
                   intro. rewrite app_inv_head_iff in H.
                   inversion H. }
            rewrite app_assoc; eapply IHR1; eauto.
            ++ rewrite -app_assoc; auto.
            ++ rewrite ectx1; eauto.
          -- change (B ++ Right :: B')%list with (B ++ [Right] ++ B')%list.
             rewrite app_assoc; eapply IHR2; eauto.
             ++ rewrite -app_assoc; auto.
             ++ rewrite ectx2; eauto; cbn.
                cbn in ectx1. rewrite /Ctx.union -ectx1 in esrch1.
                have esymbs := RuleTree_to_Sequence_symbols hbranchof1 esrch1 eseq1.
                rewrite -esymbs; eauto.

      (* Case: [GammaAll] *)
      + apply gamma_rule_sound in esrch; destruct esrch as (l & eget & hin & esrch1).
        have eseq0 := eseq.
        cbn in eseq; rewrite eget in eseq.
        destruct (expand_tableau_branch__aux _ _ _ _) eqn:hexpand; try easy.
        destruct (RuleTree_to_Sequence__aux (B ++ [Left])%list _ _) eqn:eseq1; try easy.
        have es : last s (mkLeaf sko) = last s1 (mkLeaf sko).
        { injection eseq => <-.
          rewrite last_cons //. eapply RuleTree_to_Sequence_not_nil; eauto. }
        rewrite !es in hbranchof' |- *.
        have hbranchof1 : is_branch_of (B ++ [Left])%list {| tree := t; symbols := symbols T |}
          := is_branch_of_extend_left hbranchof hexpand.
        have [T0 [ hnleaf e ] ] := RuleTree_to_Sequence_branch hbranchof1 eseq1.
        have ectx1 := get_context_extend_left hbranchof hexpand eq_refl.
        destruct B' as [|b' B'].
        * rewrite app_nil_r in hbranchof'; exfalso.
          have [ T'' [ hnleaf0 erepl ] ] := RuleTree_to_Sequence_branch hbranchof1 eseq1.
          have contra := replace_expanded_child_not_branch_Left hbranchof hnleaf0 hexpand erepl.
          easy.
        * destruct b'.
          -- change (B ++ Left :: B')%list with (B ++ [Left] ++ B')%list.
             rewrite app_assoc; eapply IHR1; eauto.
             ++ rewrite -app_assoc; auto.
             ++ rewrite ectx1; eauto.
          -- have [ T'' [ hnleaf0 erepl ] ] := RuleTree_to_Sequence_branch hbranchof1 eseq1.
             have contra := replace_expanded_child_not_subbranch hbranchof hnleaf0 hexpand erepl.
             have contra' := not_subbranch_no_ext_is_branch B' contra.
             rewrite -app_assoc in contra'; exfalso; now apply contra'.

      (* Case: [DeltaNegAll] *)
      + apply delta_rule_sound in esrch; destruct esrch as
          (f0 & G & eget & hmem & hsko & esymb & esrch1).
        have eseq0 := eseq.
        cbn in eseq; rewrite eget esymb in eseq.
        destruct (expand_tableau_branch__aux _ _ _ _) eqn:hexpand; try easy.
        destruct (RuleTree_to_Sequence__aux (B ++ [Left])%list _ _) eqn:eseq1; try easy.
        have es : last s (mkLeaf sko) = last s0 (mkLeaf sko).
        { injection eseq => <-.
          rewrite last_cons //. eapply RuleTree_to_Sequence_not_nil; eauto. }
        rewrite !es in hbranchof' |- *.
        have hbranchof1 : is_branch_of (B ++ [Left])%list
                                       {| tree := t0; symbols := add_symbol f0 f (symbols T) |}
          := is_branch_of_extend_left hbranchof hexpand.
        have [T0 [ hnleaf e ] ] := RuleTree_to_Sequence_branch hbranchof1 eseq1.
        have ectx1 := get_context_extend_left hbranchof hexpand eq_refl.
        destruct B' as [|b' B'].
        * rewrite app_nil_r in hbranchof'; exfalso.
          have [ T'' [ hnleaf0 erepl ] ] := RuleTree_to_Sequence_branch hbranchof1 eseq1.
          have contra := replace_expanded_child_not_branch_Left hbranchof hnleaf0 hexpand erepl.
          easy.
        * destruct b'.
          -- change (B ++ Left :: B')%list with (B ++ [Left] ++ B')%list.
             rewrite app_assoc; eapply IHR1; eauto.
             ++ rewrite -app_assoc; auto.
             ++ rewrite ectx1; eauto.
          -- have [ T'' [ hnleaf0 erepl ] ] := RuleTree_to_Sequence_branch hbranchof1 eseq1.
             have contra := replace_expanded_child_not_subbranch hbranchof hnleaf0 hexpand erepl.
             have contra' := not_subbranch_no_ext_is_branch B' contra.
             rewrite -app_assoc in contra'; exfalso; now apply contra'.
  Qed.

  Lemma CheckProof_Some_Sequence_closed :
    forall {R : RuleTree} {Gamma : list Form} {sigma : Substitution string Term}
      {record : sko_record sko} {s : Sequence sko},
      CheckProof__aux sko (function_symbols Gamma) Gamma sigma empty_record R =
        ret {| status := true; symbs := record |} ->
      RuleTree_to_Sequence Gamma R = Some s ->
      is_tableau_closed (last s (mkLeaf sko)) sigma.
  Proof using Type.
    intros ????? esrch eseq B hbranchof. change B with (EmptyBranch ++ B)%list.
    eapply CheckProof_Some_RuleTree_to_Sequence_closed; eauto.
    - apply is_branch_of_nil.
    - cbn; eauto.
  Qed.

  (** We can then conclude on the soundness of the algorithm. *)
  Lemma CheckProof_sound :
    forall {Gamma : list Form} {sigma : Substitution string Term} {R : RuleTree},
      CheckProof sko Gamma sigma R = ret true ->
      hasTableau sko Gamma sigma.
  Proof using Type.
    intros ??? e.

    cbn in e. destruct (CheckProof__aux sko (function_symbols Gamma)
                          (Ctx.from_list Gamma) sigma empty_record R) eqn:esrch; try easy; cbn in *.
    destruct a; cbn in *. injection e => estatus el; subst.
    rewrite app_nil_r in estatus; subst.

    have [s esequence] := CheckProof_Some_RuleTree_to_Sequence_Some esrch.
    exists s; split.

    - eapply CheckProof_Some_RuleTree_to_Sequence_is_expansion_sequence; eauto.
      1: apply is_branch_of_nil.
      2: apply esrch.
      red; cbn. rewrite app_nil_r.
      have hapi : to_set empty_record = \{\} by admit.
      rewrite hapi empty_unitr //.
    - split.
      + erewrite RuleTree_to_Sequence_hd; eauto. now cbn.
      + eapply CheckProof_Some_Sequence_closed; eauto.
  Admitted.
End Soundness.

(** ** 3. Extended Syntax *)

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

  Inductive ExtendedRuleTree : Type :=
  | Leaf : option (Form * Form) -> ExtendedRuleTree
  | Node : ExtendedRuleTree -> ExtendedRule -> ExtendedRuleTree -> ExtendedRuleTree.

  Definition mkTrivialClosure : ExtendedRuleTree := Leaf None.

  Definition mkClosure (F G : Form) : ExtendedRuleTree :=
    Leaf (Some (F, G)).

  Definition mkUnaryNode (rule : ExtendedRule) (T1 : ExtendedRuleTree) : ExtendedRuleTree :=
    Node T1 rule (Leaf None).

  Definition mkBinaryNode (rule : ExtendedRule) (T1 T2 : ExtendedRuleTree) : ExtendedRuleTree :=
    Node T1 rule T2.

  Definition get_neg_neg (F : Form) : Result Form :=
    match F with
    | Neg (Neg G) => ret G
    | _ => (Neg Bot, ["Error: the formula " ++ pr_form F ++ " is not a double negation."])
    end.

  Definition get_neg_or (F : Form) : Result (list Form) :=
    match F with
    | Neg (Or F1 F2) => ret [Neg F1 ; Neg F2]
    | _ => ([], ["Error: the formula " ++ pr_form F ++ " is not a negated disjunction."])
    end.

  Definition get_and (F : Form) : Result (list Form) :=
    match F with
    | Neg (Or (Neg F1) (Neg F2)) => ret [F1 ; F2 ; Neg (Neg F1) ; Neg (Neg F2)]
    | _ => ([], ["Error: the formula " ++ pr_form F ++ " is not a conjunction."])
    end.

  Definition get_neg_imp (F : Form) : Result (list Form) :=
    match F with
    | Neg (Or (Neg F1) F2) => ret [F1 ; Neg F2 ; Neg (Neg F1)]
    | _ => ([], ["Error: the formula " ++ pr_form F ++ " is not a negated implication."])
    end.

  Definition get_or (F : Form) : Result (Form * Form) :=
    match F with
    | Or F1 F2 => ret (F1, F2)
    | _ => ((Neg Bot, Neg Bot), ["Error: the formula " ++ pr_form F ++ " is not a disjunction."])
    end.

  Definition get_imp (F : Form) : Result (Form * Form) :=
    match F with
    | Or (Neg F1) F2 => ret (Neg F1, F2)
    | _ => ((Neg Bot, Neg Bot), ["Error: the formula " ++ pr_form F ++ " is not an implication."])
    end.

  Definition get_neg_and (F : Form) : Result (list Form * list Form) :=
    match F with
    | Neg (Neg (Or (Neg F1) (Neg F2))) => ret ([Neg F1 ; Or (Neg F1) (Neg F2)], [Neg F2 ; Or (Neg F1) (Neg F2)])
    | _ => (([], []), ["Error: the formula " ++ pr_form F ++ " is not a negated conjunction."])
    end.

  Definition get_equ (F : Form) :
    Result (list Form * list Form * list Form * list Form * list Form) :=
    let err := (([], [], [], [], []),
                 ["Error: the formula " ++ pr_form F ++ " is not an equivalence."]) in
    match F with
    | Neg (Or (Neg (Or (Neg F1) F2)) (Neg (Or (Neg F3) F4))) =>
        if negb (eqb F1 F4 && eqb F2 F3) then err
        else
          ret ([Neg F1 ; Neg F2], [F1 ; Neg F1], [Neg F2 ; F2], [F1 ; F2],
              [(Or (Neg F2) F1) ; (Or (Neg F1) F2) ; Neg (Neg (Or (Neg F1) F2)) ; Neg (Neg (Or (Neg F2) F1))])
    | _ => err
    end.

  Definition get_neg_equ (F : Form) : Result (list Form * list Form * Form) :=
    let err := (([], [], Neg Bot),
                 ["Error: the formula " ++ pr_form F ++ " is not an equivalence."]) in
    match F with
    | Neg (Neg (Or (Neg (Or (Neg F1) F2)) (Neg (Or (Neg F3) F4)))) =>
        if negb (eqb F1 F4 && eqb F2 F3) then err
        else ret ([F1 ; Neg (Neg F1) ; Neg F2 ; Neg (Or (Neg F1) F2)],
                 [F2 ; Neg (Neg F2) ; Neg F1 ; Neg (Or (Neg F2) F1)],
                 Or (Neg (Or (Neg F1) F2)) (Neg (Or (Neg F2) F1)))
    | _ => err
    end.

  Definition get_all (F : Form) : Result Form :=
    match F with
    | All G => ret G
    | _ => (Neg Bot, ["Error: the formula " ++ pr_form F ++ " is not a universal quantifier."])
    end.

  Definition get_neg_ex (F : Form) : Result Form :=
    match F with
    | Neg (Neg (All (Neg G))) => ret G
    | _ => (Neg Bot, ["Error: the formula " ++ pr_form F ++
                   " is not a negated existential quantifier."])
    end.

  Definition get_ex (F : Form) : Result Form :=
    match F with
    | Neg (All (Neg G)) => ret G
    | _ => (Neg Bot, ["Error: the formula " ++ pr_form F ++ " is not an existential quantifier."])
    end.

  Definition get_neg_all (F : Form) : Result Form :=
    match F with
    | Neg (All G) => ret G
    | _ => (Neg Bot, ["Error: the formula " ++ pr_form F ++ " is not a negated universal quantifier."])
    end.

  (* We provide a compilation of the [ExtendedRuleTree] to a [RuleTree]. *)
  Fixpoint compile__aux (Gamma : list Form) (T : ExtendedRuleTree) : Result RuleTree :=
    match T with
    | Leaf None => if Ctx.mem [[ ENeg ETop ]] Gamma
                  then ret (Checker.Node (Checker.Leaf None)
                              (Checker.AlphaNegNeg [[ ENeg ETop ]]) (Checker.Leaf None))
                  else ret (Checker.Leaf None)
    | Leaf (Some (F, G)) => ret (Checker.Leaf (Some (F, G)))
    | Node T1 r T2 =>
        match r with
        | AlphaNegNeg F =>
            G <- get_neg_neg F;
            T1' <- compile__aux (G :: Gamma) T1;
            ret (Checker.Node T1' (Checker.AlphaNegNeg F) (Checker.Leaf None))
        | AlphaNegOr F =>
            l <- get_neg_or F;
            T1' <- compile__aux (l ++ Gamma)%list T1;
            ret (Checker.Node T1' (Checker.AlphaNegOr F) (Checker.Leaf None))
        | AlphaAnd F =>
            l <- get_and F;
            T1' <- compile__aux (l ++ Gamma)%list T1;
            ret (Checker.Node
                   (Checker.Node (Checker.Node T1' (Checker.AlphaNegNeg (last l (Neg Bot)))
                                    (Checker.Leaf None))
                      (Checker.AlphaNegNeg (hd (Neg Bot) (tl (tl l)))) (Checker.Leaf None))
                   (Checker.AlphaNegOr F) (Checker.Leaf None))
        | AlphaNegImp F =>
            l <- get_neg_imp F;
            T1' <- compile__aux (l ++ Gamma)%list T1;
            ret (Checker.Node
                   (Checker.Node T1' (Checker.AlphaNegNeg (last l (Neg Bot))) (Checker.Leaf None))
                   (Checker.AlphaNegOr F)
                   (Checker.Leaf None))
        | BetaOr F =>
            fs <- get_or F;
            T1' <- compile__aux (fst fs :: Gamma)%list T1;
            T2' <- compile__aux (snd fs :: Gamma)%list T2;
            ret (Checker.Node T1' (Checker.BetaOr F) T2')
        | BetaImp F =>
            fs <- get_imp F;
            T1' <- compile__aux (fst fs :: Gamma)%list T1;
            T2' <- compile__aux (snd fs :: Gamma)%list T2;
            ret (Checker.Node T1' (Checker.BetaOr F) T2')
        | BetaNegAnd F =>
            fs <- get_neg_and F;
            T1' <- compile__aux (fst fs ++ Gamma)%list T1;
            T2' <- compile__aux (snd fs ++ Gamma)%list T2;
            ret (Checker.Node (Checker.Node T1' (Checker.BetaOr (last (fst fs) (Neg Bot))) T2')
                              (Checker.AlphaNegNeg F) (Checker.Leaf None))
        | BetaEqu F =>
            fs <- get_equ F;
            match fs, snd fs, snd (fst fs) with
            | (fnegs, contr1, contr2, fpos, prefix), [nF2 ; nF1 ; nnF1 ; nnF2], [F1 ; F2] =>
                T1' <- compile__aux (fnegs ++ prefix ++ Gamma)%list T1;
                T2' <- compile__aux (fpos ++ prefix ++ Gamma)%list T2;
                ret (Checker.Node
                       (Checker.Node
                          (Checker.Node
                             (Checker.Node
                                (Checker.Node
                                   T1'
                                   (Checker.BetaOr nF2)
                                   (Checker.Leaf (Some (F1, Neg F1))))
                                (Checker.BetaOr nF1)
                                (Checker.Node
                                   (Checker.Leaf (Some (F2, Neg F2)))
                                   (Checker.BetaOr nF2)
                                   T2'))
                             (Checker.AlphaNegNeg nnF2) (Checker.Leaf None))
                          (Checker.AlphaNegNeg nnF1) (Checker.Leaf None))
                       (Checker.AlphaNegOr F) (Checker.Leaf None))
             | _, _, _ => (Checker.Leaf None, ["Anomaly: please report to the developers."])
             end
        | BetaNegEqu F =>
            fs <- get_neg_equ F;
            T1' <- compile__aux (fst (fst fs) ++ Gamma)%list T1;
            T2' <- compile__aux (snd (fst fs) ++ Gamma)%list T2;
            ret (Checker.Node
                   (Checker.Node
                      (Checker.Node
                         (Checker.Node T1'
                            (Checker.AlphaNegNeg (hd (Neg Bot) (tl (fst (fst fs)))))
                            (Checker.Leaf None))
                         (Checker.AlphaNegOr (last (fst (fst fs)) (Neg Bot)))
                         (Checker.Leaf None))
                      (Checker.BetaOr (snd fs))
                      (Checker.Node
                         (Checker.Node T1'
                            (Checker.AlphaNegNeg (hd (Neg Bot) (tl (snd (fst fs)))))
                            (Checker.Leaf None))
                         (Checker.AlphaNegOr (last (snd (fst fs)) (Neg Bot)))
                         (Checker.Leaf None)))
                   (Checker.AlphaNegNeg F)
                   (Checker.Leaf None))
        | GammaAll F x =>
            G <- get_all F;
            T1' <- compile__aux (G{0 \to Free x} :: Gamma) T1;
            ret (Checker.Node T1' (Checker.GammaAll F x) (Checker.Leaf None))
        | GammaNegEx F x =>
            G <- get_neg_ex F;
            T1' <- compile__aux (Neg G{0 \to Free x} :: All (Neg G) :: Gamma) T1;
            ret (Checker.Node
                   (Checker.Node T1' (Checker.GammaAll (All (Neg G)) x) (Checker.Leaf None))
                   (Checker.AlphaNegNeg F) (Checker.Leaf None))
        | DeltaEx F t =>
            G <- get_ex F;
            T1' <- compile__aux (G{0 \to t} :: Neg (Neg G{0 \to t}) :: Gamma) T1;
            ret (Checker.Node
                   (Checker.Node T1' (Checker.AlphaNegNeg (Neg (Neg G{0 \to t}))) (Checker.Leaf None))
                   (Checker.DeltaNegAll F t) (Checker.Leaf None))
        | DeltaNegAll F t =>
            G <- get_neg_all F;
            T1' <- compile__aux (G{0 \to t} :: Gamma) T1;
            ret (Checker.Node T1' (Checker.DeltaNegAll F t) (Checker.Leaf None))
        end
    end.

  Definition compile (Gamma : list Form) (T : ExtendedRuleTree) : Result RuleTree := compile__aux Gamma T.

  Lemma Extended_CheckProof_sound :
    forall {sko : Skolemization} {Gamma : list Form} {sigma : Substitution string Term} (R : ExtendedRuleTree),
      (T <- compile Gamma R;
       CheckProof sko Gamma sigma T) = ret true ->
      hasTableau sko Gamma sigma.
  Proof.
    intros ???? echk.
    destruct (compile Gamma R) eqn:comp; try easy.
    unshelve eapply CheckProof_sound; eauto.
    cbn in echk |- *.
    have el : l = [].
    { injection echk => els _. apply app_eq_nil in els; easy. }
    rewrite el in echk; now cbn in echk.
  Qed.
End ExtendedSyntax.

(** ** 4. The [tableaux] tactic *)

Ltac tableaux tree :=
  apply (Extended_CheckProof_sound tree); native_compute;
  lazymatch goal with
  | [ |- (false, ?err :: _) = (true, []) ] =>
      fail 0 "tableaux failed with the following error message: " err
  | _ => reflexivity
  end.
