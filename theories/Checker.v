(** * Checker: sound algorithm to check a tableau proof *)

From Tableaux Require Import Core.
From Tableaux Require Import ExtendedSyntax.

From Stdlib Require Import Lia.

(** In this file, we implement a tableau proof checker procedure.

    It returns true if the tableau is closed. We show that this procedure
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

Class Pr (A : Type) :=
  pr : A -> string.

#[global] Instance pr_bool : Pr bool :=
  fun b =>
    match b with
    | true => "true"
    | false => "false"
    end.

#[global] Instance pr_term : Pr Term :=
  fix F (t : Term) : string :=
    match t with
    | Bound n => "x@" ++ nat_to_string n
    | Free x => x
    | Fun f l => f ++ "(" ++ pr_list F l ++ ")"
    end.

#[global] Instance pr_form : Pr Form :=
  fix rec (F : Form) : string :=
    match F with
    | Bot => "$false"
    | Pred p l => p ++ "(" ++ pr_list pr l ++ ")"
    | Neg F => "~(" ++ rec F ++ ")"
    | Or F1 F2 => "(" ++ rec F1 ++ " | " ++ rec F2 ++ ")"
    | All F => "! (" ++ rec F ++ ")"
    end.

(* TODO: declare a [Ctx] in the [Proofs] file and share the definitions *)
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
  #[global] Instance pr_ctx : Pr t := fun Gamma => "[" ++ pr_list pr Gamma ++ "]".

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
    then error ("Formula " ++ pr_form F ++ " not found in the context " ++ pr Gamma)
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
                        ++ pr Gamma)).

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
End RuleTreeToSequence.

(** We start by importing the tactics that automate some data inference from proof trees. *)
Import TreeTactics.

(** We define tactics to automate the case analysis on the recursive calls of the algorithms &
    to select the relevant subcases. *)
Ltac simplify_seq_rec_call :=
  let eget := fresh "eget" in
  let eexp := fresh "eexp" in
  match goal with
  | [ e : RuleTree_to_Sequence__aux ?B ?T (Node ?R1 (AlphaNegNeg ?f) ?R2) = Some _ |- _ ] =>
      cbn in e; destruct (get_neg_neg f) eqn:eget
  | [ e : RuleTree_to_Sequence__aux ?B ?T (Node ?R1 (AlphaNegOr ?f) ?R2) = Some _ |- _ ] =>
      cbn in e; destruct (get_neg_or f) eqn:eget
  | [ e : RuleTree_to_Sequence__aux ?B ?T (Node ?R1 (BetaOr ?f) ?R2) = Some _ |- _ ] =>
      cbn in e; destruct (get_or f) eqn:eget
  | [ e : RuleTree_to_Sequence__aux ?B ?T (Node ?R1 (GammaAll ?f ?x) ?R2) = Some _ |- _ ] =>
      cbn in e; destruct (get_all f) eqn:eget
  | [ e : RuleTree_to_Sequence__aux ?B ?T (Node ?R1 (DeltaNegAll ?f ?t) ?R2) = Some _ |- _ ] =>
      cbn in e; destruct (get_neg_all f) eqn:eget
  | _ => fail 0 "Cannot extract any equation from an auxiliary call to RuleTree_to_Sequence in the context"
  end; try easy;
  destruct (expand_tableau_branch__aux _ _ _ _) eqn:eexp; try easy;
  match goal with
  | [ e : context [get_symbol ?t] |- _ ] =>
      let esymb := fresh "esymb" in
      destruct (get_symbol t) eqn:esymb; try easy
  | _ => idtac
  end;
  match goal with
  | [ e : context [RuleTree_to_Sequence__aux (?B ++ [Left])%list ?T ?R] |- _ ] =>
      let eseq := fresh "eseq" in
      destruct (RuleTree_to_Sequence__aux (B ++ [Left])%list T R) eqn:eseq; try easy
  | _ => idtac
  end;
  match goal with
   | [ e : context [RuleTree_to_Sequence__aux (?B ++ [Right])%list ?T ?R] |- _ ] =>
       let eseq := fresh "eseq" in
       destruct (RuleTree_to_Sequence__aux (B ++ [Right])%list T R) eqn:eseq; try easy
  | _ => idtac
  end; cbn in *.

Ltac on_unary_cases tac :=
  (* apply tac on the unary cases; update this tactic when updating the algorithm *)
  only 1-2,4-5: tac;
  (* swaps back the binary case at the 3rd position. *)
  swap 4 5; swap 3 4.

Ltac on_alpha_neg_neg tac :=
  only 1: tac.

Ltac on_alpha_neg_or tac :=
  only 2: tac.

Ltac on_alpha_cases tac :=
  only 1-2: tac.

Ltac on_beta_case tac :=
  only 3 : tac.

Ltac on_gamma_case tac :=
  only 4: tac.

Ltac on_delta_case tac :=
  only 5: tac.

Ltac simplify_chk_rec_call :=
  let rf := fresh "rf" in
  let eg := fresh "eget" in
  let hin := fresh "hin" in
  let echk := fresh "echk" in
  let G := fresh "G" in
  match goal with
  | [ e : CheckProof__aux ?sko ?s ?Gamma ?sigma ?r (Node ?R1 (AlphaNegNeg ?f) ?R2) =
            ret {| status := true; symbs := ?s' |} |- _ ] =>
      apply alpha_rule_sound in e; destruct e as (rf & eg & hin & echk)
  | [ e : CheckProof__aux ?sko ?s ?Gamma ?sigma ?r (Node ?R1 (AlphaNegOr ?f) ?R2) =
            ret {| status := true; symbs := ?s' |} |- _ ] =>
      apply alpha_rule_sound in e; destruct e as (rf & eg & hin & echk)
  | [ e : CheckProof__aux ?sko ?s ?Gamma ?sigma ?r (Node ?R1 (BetaOr ?f) ?R2) =
            ret {| status := true; symbs := ?s' |} |- _ ] =>
      let rf' := fresh "rf" in
      let echk' := fresh "echk" in
      let symbs' := fresh "symbs" in
      let eget := fresh "eget" in
      apply beta_rule_sound in e; destruct e as (rf & rf' & symbs & eget & hin & echk & echk')
  | [ e : CheckProof__aux ?sko ?s ?Gamma ?sigma ?r (Node ?R1 (GammaAll ?F ?x) ?R2) =
            ret {| status := true; symbs := ?s' |} |- _ ] =>
      apply gamma_rule_sound in e; destruct e as (G & eget & hin & echk)
  | [ e : CheckProof__aux ?sko ?s ?Gamma ?sigma ?r (Node ?R1 (DeltaNegAll ?F ?t) ?R2) =
            ret {| status := true; symbs := ?s' |} |- _ ] =>
      let f := fresh "f" in
      let hsko := fresh "hsko" in
      let esymb := fresh "esymb" in
      apply delta_rule_sound in e; destruct e as (f & G & eget & hin & hsko & esymb & echk)
  | _ => fail 0 "Cannot extract any equation from an auxiliary call to CheckProof in the context"
  end; try easy.

Ltac infer_replace_child_ctx := fail 0 "Not yet implemented".

Section RuleTreeToSequence_Lemmas.
  Context {sko : Skolemization}.

  Let Tableau := Tableau sko.

  (** The [Sequence] gotten from [RuleTree_to_Sequence] is never [nil]. *)
  Lemma RuleTree_to_Sequence_not_nil :
    forall {R : RuleTree} {B : Branch} {T : Tableau} {s : Sequence sko},
      RuleTree_to_Sequence__aux B T R = Some s -> s <> [].
  Proof using Type.
    intro R; induction R; intros ??? e.
    - cbn in e; injection e => <-; now intro.
    - destruct r;
        simplify_seq_rec_call;
        injection e => <-; easy.
  Qed.

  Lemma RuleTree_to_Sequence_hd :
    forall {R : RuleTree} {B : Branch} {T : Tableau} {s : Sequence sko},
      RuleTree_to_Sequence__aux B T R = Some s -> hd_error s = Some T.
  Proof using Type.
    intro R; induction R; intros ??? e.
    - injection e => <- //.
    - destruct r;
        simplify_seq_rec_call;
        injection e => <-; easy.
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

    - destruct r;
        simplify_seq_rec_call;
        infer_branch_infos.

      all: injection e => <-.

      (** In the unary cases: directly call the induction hypothesis on the left branch. *)
      all:
        on_alpha_cases
          ltac:(destruct (IHR1 (B ++ [Left])%list {| tree := t0; symbols := symbols T |}
                            s0 hbranchof0 eseq) as (T'' & hnleaf'' & hreplace));
        on_gamma_case
          ltac:(destruct (IHR1 (B ++ [Left])%list {| tree := t; symbols := symbols T |}
                            s1 hbranchof0 eseq) as (T'' & hnleaf'' & hreplace));
        on_delta_case
          ltac:(destruct (IHR1 (B ++ [Left])%list
                               {| tree := t0; symbols := add_symbol a f (symbols T) |}
                               s0 hbranchof0 eseq) as (T'' & hnleaf'' & hreplace)).

      (** Still in the unary cases, as the sequence of the left child cannot be empty,
          it suffices to say that we replace the left child. *)
      all:
        on_unary_cases
          ltac:(rewrite last_cons; [eapply RuleTree_to_Sequence_not_nil; eauto|
                                     rewrite -hreplace; eapply replace_expand_Left; eauto]).

      (** In the binary case: we replace the _current_ node.
          To do so, we first get the two trees yielded by the induction hypotheses. *)
      have [Gamma eGamma] := is_subbranch_of_has_label hbranchof.
      revert eseq; set T0' := {| tree := t; symbols := symbols T |}; intro eseq.
      change (is_branch_of (B ++ [Left])%list T0') in hbranchof0.
      change (is_branch_of (B ++ [Right])%list T0') in hbranchof1.

      (** Get the tree that replaces the left child. *)
      destruct (IHR1 (B ++ [Left])%list T0' s0 hbranchof0 eseq)
        as (T1' & hnleaf1 & hreplace1).
      have hbranchof2' := is_branch_of_replace_child_oth hbranchof1 hbranchof0
                            (not_eq_sym (branch_extend_left_right B)) hreplace1.

      (** Get the tree that replaces the right child. *)
      destruct (IHR2 (B ++ [Right])%list (last s0 (mkLeaf sko)) s1 hbranchof2' eseq0)
        as (T2' & hnleaf2 & hreplace2).

      (** Conclude by giving the replaced node. *)
      exists (Proofs.Node T1' Gamma T2'); split; try easy.

      rewrite replace_child_Node; auto.
      erewrite replace_child_sequence_expand; eauto.
      rewrite hreplace1; etransitivity; [now cbn|].
      rewrite hreplace2 app_comm_cons last_app //.
      eapply RuleTree_to_Sequence_not_nil; eauto.
  Qed.
End RuleTreeToSequence_Lemmas.

Ltac infer_replace_child_helper tmp :=
  let T0 := fresh "T" in
  let hnl := fresh "hnleaf" in
  let erepl := fresh "ereplace" in
  match goal with
  | [ hb : is_branch_of (?B ++ ?B')%list ?T |- _ ] =>
      match goal with
      | [ e : RuleTree_to_Sequence__aux _ _ _ = Some _ |- _ ] =>
          have [ T0 [ hnl erepl ] ] := RuleTree_to_Sequence_branch hb e;
                                       have tmp := (not_eq_sym (branch_extend_left_right B))
                                                | _ => fail 0 "Cannot infer replacement infos in this context: missing RuleTree_to_Sequence__aux equation"
      end
  | _ => fail 0 "Cannot infer replacement infos in this context: missing is_branch_of"
  end.

Ltac infer_replace_child_ctx ::=
  let tmp := fresh "tmp" in
  infer_replace_child_helper tmp; infer_replace_child_infos; clear tmp.

Section RuleTreeToSequence_Lemmas2.
  Context {sko : Skolemization}.

  Let Tableau := Tableau sko.

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

    (* Case: [Node]. *)
    - destruct r;
        simplify_chk_rec_call.

      (** On unary rules, we start by expanding the tableau as we expect. *)
      all:
        on_alpha_cases
          ltac:(have [ T0 hexpand ] := is_branch_of_expand_tableau_branch sko
                                         (Some rf) None hbranchof);
        on_beta_case
          ltac:(have [ T0 hexpand ] := is_branch_of_expand_tableau_branch sko
                                         (Some rf) (Some rf0) hbranchof);
        on_gamma_case
          ltac:(have [ T0 hexpand ] := is_branch_of_expand_tableau_branch sko
                                         (Some [opening_form 0 (Free s) G]) None hbranchof);
        on_delta_case
          ltac:(have [ T0 hexpand ] := is_branch_of_expand_tableau_branch sko
                                         (Some [opening_form 0 t G]) None hbranchof);
        infer_branch_infos; infer_ctx_infos.

      (** Then, we can almost directly conclude by getting the sequence yielded by the
          inductive hypothesis. *)
      all:
        on_alpha_cases
          ltac:(destruct (IHR1 (B ++ [Left])%list record record' func_symbs T0 hbranchof0
                            (Ctx.union rf Gamma) echk ectx) as (seq & hseq));
        on_gamma_case
          ltac:(destruct (IHR1 (B ++ [Left])%list record record' func_symbs T0 hbranchof0
                            (Ctx.add (G{0 \to Free s}) Gamma) echk ectx) as (seq & hseq));
        on_delta_case
          ltac:(destruct (IHR1 (B ++ [Left])%list (add_symbol f0 f record) record' func_symbs
                               {| tree := T0; symbols := (add_symbol f0 f (symbols T0)) |}
                               hbranchof0 (Ctx.add (G{0 \to t}) Gamma) echk ectx) as (seq & hseq)).

      (** It suffices to giving the current tableau (T) followed by the sequence given by
          the previous step. *)
      all:
        on_unary_cases
          ltac:(exists (T :: seq); cbn;
                  rewrite eget eexpand (expand_tableau_branch_Some_symbs sko hexpand));
        on_delta_case
          ltac:(rewrite esymb);
        on_unary_cases
          ltac:(by rewrite hseq).

      (** On binary rules, the sequence yielded is [T :: removelast (sequence of left child) ++
          sequence of right child]. Let's start by getting the sequence of the left child
          and infer some branching and context information out of this. *)
      destruct (IHR1 (B ++ [Left])%list record symbs func_symbs T0 hbranchof0
                  (Ctx.union rf Gamma) echk ectx) as (s1 & hseq1).

      (** Replace the context of [T0] to the context of the last element of [s1]. *)
      infer_replace_child_ctx.
      rewrite ectx1 in ectx0; auto.

      (** Using the inferred context fact, we can get the sequence given by the right child. *)
      destruct (IHR2 (B ++ [Right])%list symbs record' func_symbs (last s1 (mkLeaf sko))
                  hbranchof2 (Ctx.union rf0 Gamma) echk0 ectx0) as (s2 & hseq2).

      (** And conclude by giving the expected sequence. *)
      exists (T :: removelast s1 ++ s2); cbn.
      rewrite eget0 eexpand (expand_tableau_branch_Some_symbs sko hexpand) hseq1 hseq2 //.
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

    - destruct r;
        simplify_chk_rec_call;
        simplify_seq_rec_call;
        infer_branch_infos.

      (** In order to use the induction hypothesis, we add a small lemma on contexts. *)
      all:
        have ectx1 := get_context_extend_left hbranchof eexp eq_refl;
        on_unary_cases
          ltac:(rewrite /Ctx.union /Ctx.elements /Ctx.add in echk, ectx1;
                injection eget => eget1; subst; cbn in ectx1; rewrite -ectx1 in echk).

      (** Moreover, as the induction hypothesis depends on tableaux, we must specify the
          symbols in each case. *)
      all:
        on_alpha_cases
          ltac:(change (is_branch_of
                          (B ++ [Left])%list
                          {| tree := t0; symbols := symbols T |}) in hbranchof0);
        on_gamma_case
          ltac:(change (is_branch_of
                          (B ++ [Left])%list
                          {| tree := t; symbols := symbols T |}) in hbranchof0);
        on_delta_case
          ltac:(injection esymb => esymb'; subst;
                change (is_branch_of
                          (B ++ [Left])%list
                          {| tree := t0; symbols := add_symbol f0 f (symbols T) |})
                                    in hbranchof0).

      (** Then, we can apply the induction hypothesis in the unary cases. *)
      all:
        on_unary_cases
          ltac:(rewrite (IHR1 sigma (B ++ [Left])%list _ _ _ _ hbranchof0 echk eseq0);
                injection eseq => <-; cbn; set sequence := (x in symbols (last x (mkLeaf sko)))).

      (** And we can conclude as the sequence cannot be empty. *)
      all:
        on_unary_cases
          ltac:(fold sequence;
                have hsequence : sequence <> [] by eapply RuleTree_to_Sequence_not_nil; eauto);
        on_unary_cases
          ltac:(destruct sequence; easy).

      (** We do the same work for the other branch in the binary case. *)
      have ectx2 := get_context_extend_right hbranchof eexp eq_refl.
      rewrite /Ctx.union /Ctx.elements in echk, ectx1, echk0, ectx2;
        injection eget0 => eget0'; subst; rewrite -ectx1 in echk; rewrite -ectx2 in echk0.

      (** By induction hypothesis, we directly get that symbs are the symbols of the last
          tableau of the sequence of the left child. *)
      have esymbs' : symbs = symbols (last s0 (mkLeaf sko)).
      { eapply IHR1; [| |apply eseq0]; eauto. }

      rewrite esymbs' in echk0.
      injection eseq => <-; rewrite app_comm_cons last_app.
      { eapply RuleTree_to_Sequence_not_nil; eauto. }

      change (is_branch_of (B ++ [Left])%list {| tree := t; symbols := symbols T |})
        in hbranchof0.
      change (is_branch_of (B ++ [Right])%list {| tree := t; symbols := symbols T |})
        in hbranchof1.
      infer_replace_child_ctx.

      eapply IHR2; eauto.
      rewrite -ectx; eauto.
  Qed.
End RuleTreeToSequence_Lemmas2.

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

    - destruct r;
        simplify_chk_rec_call;
        simplify_seq_rec_call.

      (** Get the two tableaux to relate in the conclusion. *)
      all:
        destruct s; try easy;
        destruct s; try easy;
        injection eseq => eseq' eseq''; injection esnd => esnd';
        rewrite eseq'' -esnd'.

      (** Get the real formula. *)
      all:
        on_alpha_cases
          ltac:(do 2 (destruct f; try easy));
        on_beta_case
          ltac:(destruct f; try easy);
        on_gamma_case
          ltac:(destruct f; try easy);
        on_delta_case
          ltac:(do 2 (destruct f; try easy));
        subst.

      (** Apply the respective expansion rules on easy (alpha and gamma) cases. *)
      all:
        on_alpha_neg_neg
          ltac:(eapply expansion_NegNeg; eauto; [apply in_context_is_on_branch; eauto|]; cbn);
        on_alpha_neg_or
          ltac:(eapply expansion_NegOr; eauto; [apply in_context_is_on_branch; eauto|]; cbn);
        on_gamma_case
          ltac:(eapply expansion_All with (x := s0); eauto;
                [apply in_context_is_on_branch; eauto|]; cbn).

      (** In the unfolded cases, we can use [eexp] to simplify the goal. *)
      all:
        on_alpha_cases
          ltac:(cbn in eget0; rewrite /Ctx.singleton /Ctx.elements in eget0, eexp;
                rewrite eget0 eexp);
        on_gamma_case
          ltac:(cbn in eget0; injection eget0 => ->; cbn; rewrite eexp).

      (** And we can conclude by applying [RuleTree_to_Sequence_hd] in [eseq0]. *)
      all:
        try (apply RuleTree_to_Sequence_hd in eseq0; by cbn in eseq0).

      (** Case: beta rule. This case is a bit tricky as we remove the last element of the
          sequence of the left child. Consequently, there are two cases:
          - either [s0] has exactly one element, and in this case we have to show that
            [t0 |> head s1]. This is done by showing that [T'] is the head of [s1].
          - either [s0] has more than one element, and in this case we have to show that
            [t0 |> head s0], which is similar as the previous easy cases. *)
      + have hs0 : s0 <> [] by eapply RuleTree_to_Sequence_not_nil; eauto.
        destruct s0; try easy; destruct s0.

        (** In both cases, we apply the [expansion_Or] rule and use [eexp]
            to simplify the goal. *)
        all:
          eapply expansion_Or; eauto; [apply in_context_is_on_branch; eauto|];
          destruct p as [f1s f2s]; cbn in eget; unfold Ctx.singleton in eget;
            injection eget => -> ->; cbn; rewrite eexp.

        (** Case 1: [s0] has exactly one element. *)
        * apply RuleTree_to_Sequence_hd in eseq0, eseq1; cbn in eseq0, eseq', eseq1;
            rewrite eseq' in eseq1; cbn in eseq1; congruence.
        (** Case 2: [s0] has more than one element. *)
        * apply RuleTree_to_Sequence_hd in eseq0; cbn in eseq0, eseq'.
          injection eseq' => _ eseq''; congruence.

      (** Case: delta rules. In this case, we have to manage the Skolem symbols stored.
          Hence, we start by deriving the Skolemization condition on the first tableau. *)
      + have hsko' : sko t (Neg (All f)) (symbols t1) (fv (get_context B t1))
                       (function_symbols (get_all_formulas t1)) = true by
          (have e := symbol_sound sko hsko); rewrite esymb0 in e; eapply is_sko_consistent; eauto.

        eapply expansion_NegAll with (hsko := hsko'); eauto;
          [apply in_context_is_on_branch; eauto| |].

        (** We then use the same techniques as in the previous cases to conclude the first
            branch. *)
        * cbn in eget0; change (Neg f {0 \to t}) with ((Neg f) {0 \to t}); injection eget0 => ->;
            rewrite eexp.
          apply RuleTree_to_Sequence_hd in eseq0; cbn in eseq0;
            destruct T'; injection eseq0; intros; cbn; congruence.

        (** Finally, we conclude this last branch by using the soundness of the symbols of a
            Skolemization process. *)
        * apply RuleTree_to_Sequence_hd in eseq0; cbn in eseq0;
            injection eseq0 => ->; cbn.
          
          (have esymb1 := symbol_sound sko hsko);
          (have esymb2 := symbol_sound sko hsko');
          congruence.
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
      red in hpres. apply hpres. eapply GetFunctSymbols_in; eauto.
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
    red in hpres. apply hpres. eapply GetFunctSymbols_in; eauto.
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
    red in hpres. apply hpres. eapply GetFunctSymbols_in; eauto.
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
    red in hpres. apply hpres. eapply GetFunctSymbols_in; eauto.
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
    have e : function_symbols (All F) = function_symbols (F {0 \to Free x}) by
      now rewrite function_symbols_opening_all_free.
     change (set_in f (function_symbols (F {0 \to Free x}))) in hin'.
    rewrite -e in hin'. red in hpres. apply hpres. eapply GetFunctSymbols_in; eauto.
    eapply in_get_ctx_in_all_formulas; eauto.
  Qed.

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
    have h : function_symbols (Neg F{0 \to t}) \subseteq
               function_symbols (Neg (All F)) \union function_symbols t.
    { cbn; apply function_symbols_opening. }
    change (set_in f (function_symbols (Neg F {0 \to t}))) in hin'.
    specialize (h f hin'). rewrite union_spec in h. destruct h as [hF | ht].
    - rewrite join_to_set union_comm union_assoc !union_spec.
      right; rewrite -union_spec union_comm; apply hpres.
      eapply GetFunctSymbols_in; eauto.
      eapply in_get_ctx_in_all_formulas; eauto.
    - rewrite join_to_set !union_spec. right; left.
      rewrite single_to_set. rewrite -esymb //.
  Qed.

  Lemma RuleTree_to_Sequence_preserves_function_symbols_last :
  forall {R : RuleTree} {sigma : Substitution string Term} {B : Branch}
      {T : Tableau} {record : sko_record sko} {s : Sequence sko} {func_symbs : SetOfString},
      is_branch_of B T -> preserves_function_symbols T func_symbs ->
      RuleTree_to_Sequence__aux B T R = Some s ->
      CheckProof__aux sko func_symbs (get_context B T) sigma (symbols T) R =
        ret {| status := true; symbs := record |} ->
      preserves_function_symbols (last s (mkLeaf sko)) func_symbs.
  Proof using Type.
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
               (l := Some (Ctx.elements l)) (l' := None) (T := T); eauto.
             ++ reflexivity.
             ++ cbn; eapply preserves_function_symbols_get_neg_neg; eauto.
             ++ apply preserves_function_symbols_None.
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
             ++ reflexivity.
             ++ cbn; eapply preserves_function_symbols_get_neg_or; eauto.
             ++ apply preserves_function_symbols_None.
          -- cbn; erewrite get_context_extend_left; eauto.

      + have [ l [ l' [ symbs1 [ eget [ hin [ esrch1 esrch2 ] ] ] ] ] ] := beta_rule_sound echk.
        rewrite eget in eseq.
        destruct (expand_tableau_branch__aux _ _ _ _) eqn:hexpand; try easy.
        destruct (RuleTree_to_Sequence__aux _ _ _) eqn:hseq1; try easy.
        destruct (RuleTree_to_Sequence__aux (B ++ [Right])%list _ _) eqn:hseq2; try easy.
        have hbranchof1 :
          is_branch_of (B ++ [Left])%list {| tree := t; symbols := symbols T |} :=
          is_branch_of_extend_left hbranchof hexpand.
        have [ T1' [ hnleaf ereplace ] ] := RuleTree_to_Sequence_branch hbranchof1 hseq1.
        have ebranch : (B ++ [Right])%list <> (B ++ [Left])%list.
        { clear; induction B; cbn; intro; congruence. }

        have hbranchof2 : is_branch_of (B ++ [Right])%list (last s0 (mkLeaf sko)).
        { eapply is_branch_of_replace_child_oth.
          3: eassumption.
          all: eauto.
          eapply is_branch_of_extend_right; eauto. }

        have ectx2' : get_context (B ++ [Right])%list t = get_context (B ++ [Right])%list
                                                             (last s0 (mkLeaf sko)).
        { eapply get_context_replace_child_oth.
          3: eassumption.
          all: eauto.
          eapply is_branch_of_extend_right; eauto. }

        injection eseq => <-. rewrite app_comm_cons last_app.
        * eapply RuleTree_to_Sequence_not_nil; eauto.
        * eapply IHR2 with (B := (B ++ [Right])%list) (T := last s0 (mkLeaf sko)).
          -- assumption.
          -- eapply IHR1 with (B := (B ++ [Left])%list)
                              (T := {| tree := t; symbols := symbols T |});
               eauto.
             ++ eapply extend_subset_preserves_function_symbols with
                  (l := Some (Ctx.elements l)) (l' := Some (Ctx.elements l'))
                  (T := T); eauto.
                ** reflexivity.
                ** cbn; eapply preserves_function_symbols_get_or1; eauto.
                ** cbn; eapply preserves_function_symbols_get_or2; eauto.
             ++ cbn; erewrite get_context_extend_left; eauto.
          -- exact hseq2.
          -- erewrite <-esrch2; f_equal.
             ++ rewrite -ectx2'.
                erewrite get_context_extend_right; eauto.
             ++ symmetry; eapply RuleTree_to_Sequence_symbols.
                3: apply hseq1.
                all: eauto.
                rewrite -esrch1.
                unfold Ctx.union. erewrite <-get_context_extend_left; eauto.

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
             ++ reflexivity.
             ++ cbn; eapply preserves_function_symbols_get_all; eauto.
             ++ apply preserves_function_symbols_None.
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
          -- eapply extend_subset_preserves_function_symbols with
               (l := Some [G{0 \to t}]) (l' := None); eauto.
             ++ cbn. rewrite join_to_set. intros g hing.
                rewrite union_spec; now right.
             ++ eapply preserves_function_symbols_get_neg_all; eauto.
                erewrite (sko_function_symbols_sound sko hsko); eauto.
                erewrite (symbol_sound sko hsko) in esymb'.
                injection esymb' => -> //.
             ++ apply preserves_function_symbols_None.
          -- cbn; erewrite get_context_extend_left; eauto.
             rewrite /Ctx.add in esrch1; cbn. injection esymb => ->.
             eassumption.
  Qed.

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
        have hsubset : to_set (symbols T) \subseteq to_set (symbols {| tree := t; symbols := symbols T |})
          by reflexivity.
        have hpres1 := extend_subset_preserves_function_symbols sko func_symbs hbranchof hpres
                         hsubset hsubl (preserves_function_symbols_None T func_symbs) hexpand.
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
        have hsubset : to_set (symbols T) \subseteq to_set (symbols {| tree := t; symbols := symbols T |})
          by reflexivity.
        have hpres1 := extend_subset_preserves_function_symbols sko func_symbs hbranchof hpres
                         hsubset hsubl (preserves_function_symbols_None T func_symbs) hexpand.
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
        have hsubset : to_set (symbols T) \subseteq to_set (symbols {| tree := t; symbols := symbols T |})
          by reflexivity.
        have hpres1 := extend_subset_preserves_function_symbols sko func_symbs hbranchof hpres
                         hsubset hsubl1 hsubl2 hexpand.

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
        have hsubset : to_set (symbols T) \subseteq to_set (symbols {| tree := t; symbols := symbols T |})
          by reflexivity.
        have hpres1 := extend_subset_preserves_function_symbols sko func_symbs hbranchof hpres
                         hsubset hsubl (preserves_function_symbols_None T func_symbs) hexpand.
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
        have hskosymb : function_symbols t = singleton f0.
        { erewrite (sko_function_symbols_sound sko hsko); eauto.
          erewrite (symbol_sound sko hsko) in esymb; eauto.
          injection esymb => -> //. }
        have hsubl := preserves_function_symbols_get_neg_all t f0 hpres hbranchof eget hin
                        hskosymb.
        have hsubl' := preserves_function_symbols_None
                         {| tree := t0; symbols := add_symbol f0 f (symbols T) |} func_symbs.
        change (to_set (add_symbol f0 f (symbols T))) with
          (to_set (symbols {| tree := t0; symbols := add_symbol f0 f (symbols T) |})) in hsubl.
        have hsubset : to_set (symbols T) \subseteq
                         to_set (symbols
                                   {| tree := t0; symbols := add_symbol f0 f (symbols T) |}).
        { cbn. rewrite join_to_set; intros g hing; rewrite union_spec; now right. }
        have hpres1 := extend_subset_preserves_function_symbols
                         sko func_symbs hbranchof hpres hsubset hsubl hsubl' hexpand.
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
  Qed.

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
      red; cbn. rewrite app_nil_r empty_to_set empty_unitr //.
    - split.
      + erewrite RuleTree_to_Sequence_hd; eauto.
      + eapply CheckProof_Some_Sequence_closed; eauto.
  Qed.
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
                         (Checker.Node T2'
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
