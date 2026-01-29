(** * Reflect: sound and complete algorithm to "search" for tableaux proofs *)

From Tableaux Require Import Core.
From Tableaux Require Import ATPCompat.

(** In this file, we implement a guided tableau proof-search procedure. It is named
    "guided" as the rules to apply and the substitution are given.

    It returns a boolean if the tableau is closed. We show that this procedure
    is sound, which makes it possible to output proof certificates from this
    algorithm. *)

(** ** 1. The algorithm *)

(** *** Data-structures *)

(** We start by giving a data-structure that reflects the rules in [Proofs] extended for a
    use with the extended syntax. *)
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

(** As we want a proof tree, we will take a tree of extended rules as an input of the algorithm.
    Unary rules can be implemented by ignoring the *2nd* child of the tree. *)
Inductive ExtendedRuleTree : Type :=
| Leaf : ExtendedRuleTree
| Node : ExtendedRuleTree -> ExtendedRule -> ExtendedRuleTree -> ExtendedRuleTree.

Definition mkUnaryNode (rule : ExtendedRule) (T1 : ExtendedRuleTree) : ExtendedRuleTree :=
  Node T1 rule Leaf.

Definition mkBinaryNode (rule : ExtendedRule) (T1 T2 : ExtendedRuleTree) : ExtendedRuleTree :=
  Node T1 rule T2.

(** A small [Result] monad that stores the issues. *)
Definition Result (A : Type) : Type := A * list string.

Definition ret {A : Type} (x : A) : Result A := (x, []).

Definition bind {A B : Type} (r : Result A) (f : A -> Result B) : Result B :=
  let (x, s) := f (fst r) in
  (x, List.app (snd r) s).

Definition error (s : string) : Result bool := (false, [s]).

Notation "r >>= f" := (bind r f) (at level 50).

(** Returns true iff [Bot] or [Neg ETop] is in the list. *)
Definition trivial_contradiction (Gamma : list Form) : bool :=
  List.existsb (fun F => orb (eqb F Bot) (eqb F [[ ENeg ETop ]])) Gamma.

Fixpoint is_negative (F : Form) : bool :=
  match F with
  | Neg F => negb (is_negative F)
  | _ => false
  end.

Definition is_positive (F : Form) : bool := negb (is_negative F).

(** Returns true iff there exists two formulas [F] and [F'] such that [Neg P@[sigma] = P'@[sigma]] in [Gamma]. *)
Definition formula_contradiction (Gamma : list Form) (sigma : Substitution string Term) : bool :=
  let Gamma__pos := List.filter is_positive Gamma in
  let Gamma__neg := List.filter is_negative Gamma in
  List.existsb (fun F => List.existsb (fun G => eqb ((Neg F)@[sigma]) (G@[sigma])) Gamma__neg) Gamma__pos.

Definition get_neg_neg (F : Form) : option (list Form) :=
  match F with
  | Neg (Neg F) => Some [F]
  | _ => None
  end.

Definition get_or (F : Form) : option (list Form * list Form) :=
  match F with
  | Or F1 F2 => Some ([F1], [F2])
  | _ => None
  end.

Definition get_and (F : Form) : option (list Form) :=
  match F with
  | Neg (Or (Neg F1) (Neg F2)) => Some [F1 ; F2]
  | _ => None
  end.

Definition get_neg_or (F : Form) : option (list Form) :=
  match F with
  | Neg F => Utils.bind (get_or F) (fun l => Some (List.map (fun F => Neg F) (List.app (snd l) (fst l))))
  | _ => None
  end.

Definition get_neg_imp (F : Form) : option (list Form) :=
  match F with
  | Neg (Or (Neg F1) F2)  => Some [F1 ; Neg F2]
  | _ => None
  end.

Definition get_imp (F : Form) : option (list Form * list Form) :=
  match get_or F with
  | Some ([Neg F1], [F2]) as l => l
  | _ => None
  end.

Definition get_neg_and (F : Form) : option (list Form * list Form) :=
  match get_neg_neg F with
  | Some [F] => match get_or F with
               | Some ([Neg F1], [Neg F2]) as l => l
               | _ => None
               end
  | _ => None
  end.

Definition get_equ (F : Form) : option (list Form * list Form) :=
  match get_and F with
  | Some [F1 ; F2] =>
      match get_imp F1, get_imp F2 with
      | Some ([nF], [G]), Some ([nG], [F]) =>
          match nF, nG with
          | Neg F0, Neg G0 =>
              if (eqb F0 F && eqb G0 G)
              then Some ([nF ; nG], [G ; F])
              else None
          | _, _ => None
          end
      | _, _ => None
      end
  | _ => None
  end.

Definition get_neg_equ (F : Form) : option (list Form * list Form) :=
  match F with
  | Neg F => match get_equ F with
          | Some ([nF ; nG], [G ; F]) => Some ([nG ; F], [nF ; G])
          | _ => None
          end
  | _ => None
  end.

Definition get_all (F : Form) : option Form :=
  match F with
  | All F => Some F
  | _ => None
  end.

Definition get_ex (F : Form) : option Form :=
  match F with
  | Neg (All (Neg F)) => Some F
  | _ => None
  end.

Definition get_neg_ex (F : Form) : option Form :=
  match F with
  | Neg (Neg (All (Neg F))) => Some (Neg F)
  | _ => None
  end.

Definition get_neg_all (F : Form) : option Form :=
  match F with
  | Neg (All F) => Some (Neg F)
  | _ => None
  end.

Definition pr_list {A : Type} (pr_A : A -> string) (l : list A) : string :=
  let fix F (l : list A) : string :=
    match l with
    | [] => ""
    | [x] => pr_A x
    | x :: xs => pr_A x ++ " ; " ++ F xs
    end in
  F l.

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

Definition pr_context (Gamma : list Form) : string :=
  "[ " ++ pr_list pr_form Gamma ++ " ]".

Definition pr_bool (b : bool) : string :=
  match b with
  | true => "true"
  | false => "false"
  end.

Section GuidedTableauSearchAlgorithm.
  Context (sko : Skolemization).

  Definition rule_wrapper {A : Type} (Gamma : Con) (F : Form) (err : string)
    (getter : Form -> option A) (action : A -> Result bool) : Result bool :=
    if negb (mem_ctx F Gamma)
    then error ("Formula " ++ pr_form F ++ " not found in the context " ++ pr_context Gamma)
    else
      match getter F with
      | None => error ("The formula " ++ pr_form F ++ " is not a " ++ err)
      | Some x => action x
      end.

  Definition SearchAlgorithm :=
    Con -> Substitution string Term -> sko_record sko -> ExtendedRuleTree -> Result bool.

  Definition alpha_rule (Gamma : Con) (sigma : Substitution string Term) (T : ExtendedRuleTree)
    (record : sko_record sko) (F : Form) (getter : Form -> option (list Form)) (err : string)
    (search : SearchAlgorithm)  :=
    rule_wrapper Gamma F err getter (fun l => search (List.app l Gamma) sigma record T).

  Definition beta_rule (Gamma : Con) (sigma : Substitution string Term) (T1 T2 : ExtendedRuleTree)
    (record : sko_record sko) (F : Form) (getter : Form -> option (list Form * list Form))
    (err : string) (search : SearchAlgorithm)  :=
    rule_wrapper Gamma F err getter
      (fun l => search (List.app (fst l) Gamma) sigma record T1 >>=
               (fun b => if b then search (List.app (snd l) Gamma) sigma record T2
                      else ret b)).

  Definition gamma_rule (Gamma : Con) (sigma : Substitution string Term) (T : ExtendedRuleTree)
    (record : sko_record sko) (F : Form) (x : string) (getter : Form -> option Form)
    (err : string) (search : SearchAlgorithm)  :=
    rule_wrapper Gamma F err getter
      (fun F => search (F{0 \to Free x} :: Gamma) sigma record T).

  Definition delta_rule (Gamma : Con) (sigma : Substitution string Term) (T : ExtendedRuleTree)
    (record : sko_record sko) (F : Form) (t : Term) (getter : Form -> option Form)
    (err : string) (search : SearchAlgorithm)  :=
    rule_wrapper Gamma F err getter
      (fun F0 => if sko t F (fv Gamma) record
             then
               match get_symbol t with
               | None => error "This shouldn't ever happen."
               | Some f => search (F0{0 \to t} :: Gamma) sigma (add_symbol f F record) T
               end
             else
               error ("The term " ++ pr_term t ++ " is not a valid Skolem symbol in the context "
                        ++ pr_context Gamma)).

  (** The guided proof-search is the following algorithm:
      - on a leaf: it tries to search for a closure [Bot] or [Neg Top] or a contradiction using
        the supplied substitution ; returns [false] if no closure rule can be found ;
      - on a node: it tries to apply the given rule on the given formula, and calls the
        algorithm recursively. *)
  Fixpoint GuidedTableauSearch__aux
    (Gamma : Con) (sigma : Substitution string Term)
    (record : sko_record sko) (tree : ExtendedRuleTree) : Result bool :=
    match tree with
    | Leaf =>
        if trivial_contradiction Gamma
        then ret true
        else if formula_contradiction Gamma sigma
             then ret true
             else error ("No contradiction in the context: " ++ pr_context (Gamma@[sigma]))

    | Node T1 rule T2 =>

        let alpha_rule (F : Form) (getter : Form -> option (list Form)) (err : string) :=
          alpha_rule Gamma sigma T1 record F getter err GuidedTableauSearch__aux in

        let beta_rule (F : Form) (getter : Form -> option (list Form * list Form)) (err : string) :=
          beta_rule Gamma sigma T1 T2 record F getter err GuidedTableauSearch__aux in

        let gamma_rule (F : Form) (x : string) (getter : Form -> option Form) (err : string) :=
          gamma_rule Gamma sigma T1 record F x getter err GuidedTableauSearch__aux in

        let delta_rule (F : Form) (t : Term) (getter : Form -> option Form) (err : string) :=
          delta_rule Gamma sigma T1 record F t getter err GuidedTableauSearch__aux in

        match rule with
        | AlphaNegNeg F => alpha_rule F get_neg_neg "double negation"
        | AlphaAnd F => alpha_rule F get_and "conjunction"
        | AlphaNegOr F => alpha_rule F get_neg_or "negated disjunction"
        | AlphaNegImp F => alpha_rule F get_neg_imp "negated implication"

        | BetaOr F => beta_rule F get_or "disjunction"
        | BetaImp F => beta_rule F get_imp "implication"
        | BetaNegAnd F => beta_rule F get_neg_and "negated conjunction"
        | BetaEqu F => beta_rule F get_equ "equivalence"
        | BetaNegEqu F => beta_rule F get_neg_equ "negated equivalence"

        | GammaAll F x => gamma_rule F x get_all "universal formula"
        | GammaNegEx F x => gamma_rule F x get_neg_ex "negated existential formula"

        | DeltaEx F t => delta_rule F t get_ex "existential formula"
        | DeltaNegAll F t => delta_rule F t get_neg_all "negated universal formula"
        end
    end.

  Definition GuidedTableauSearch (Gamma : list Form) (sigma : Substitution string Term)
    (tree : ExtendedRuleTree) : Result bool :=
    GuidedTableauSearch__aux Gamma sigma empty_record tree.
End GuidedTableauSearchAlgorithm.

(** ** 2. Soundness *)

(** *** The [Leaf] Case *)
Lemma trivial_contradiction_sound :
  forall (Gamma : Con),
    trivial_contradiction Gamma = true -> Bot \in Gamma \/ [[ ENeg ETop ]] \in Gamma.
Proof using Type.
  intro Gamma; induction Gamma as [|F Fs IHFs]; cbn.
  - now intro.
  - intros [ [e1 | e2]%Bool.orb_prop | e3]%Bool.orb_prop.
    + do 2 left. now rewrite eqbIsEq in e1.
    + right. left. now rewrite eqbIsEq in e2.
    + specialize (IHFs e3). destruct IHFs.
      * left. now right.
      * right. now right.
Qed.

Lemma formula_contradiction_sound :
  forall (Gamma : Con) (sigma : Substitution string Term),
    formula_contradiction Gamma sigma = true ->
    exists (P P' : Form), P \in Gamma /\ P' \in Gamma /\ P@[sigma] = (Neg P')@[sigma].
Proof.
  intros ?? e. unfold formula_contradiction in e.
  rewrite existsb_exists in e. destruct e as (F & hin & e).
  rewrite existsb_exists in e. destruct e as (F' & hin' & e').
  rewrite eqbIsEq in e'. exists F', F. repeat split; auto.
  - now rewrite filter_In in hin'.
  - now rewrite filter_In in hin.
Qed.

Lemma auxiliary_GuidedTableauSearch_Leaf_sound :
  forall {sko : Skolemization} {Gamma : Con} {sigma : Substitution string Term}
    {record : sko_record sko},
    GuidedTableauSearch__aux sko Gamma sigma record Leaf = ret true ->
    Bot \in Gamma \/ [[ ENeg ETop ]] \in Gamma \/
      exists (P P' : Form), P \in Gamma /\ P' \in Gamma /\ P@[sigma] = (Neg P')@[sigma].
Proof.
  intros ???? e. cbn in e.
  destruct (trivial_contradiction Gamma) eqn:e0.
  - apply trivial_contradiction_sound in e0. destruct e0.
    + now left.
    + right; now left.
  - destruct (formula_contradiction Gamma sigma) eqn:e1.
    + apply formula_contradiction_sound in e1. now do 2 right.
    + inversion e.
Qed.

(** *** Soundness of rule wrapper *)
Lemma rule_wrapper_sound :
  forall {A : Type} (Gamma : Con) (F : Form) (err : string) (getter : Form -> option A)
    (action : A -> Result bool),
    rule_wrapper Gamma F err getter action = ret true ->
    exists (x : A), getter F = Some x /\ F \in Gamma /\ action x = ret true.
Proof.
  intros ?????? e. unfold rule_wrapper in e.
  destruct (negb (mem_ctx F Gamma)) eqn:ein.
  - inversion e.
  - destruct (getter F) eqn:egetter.
    + rewrite Bool.negb_false_iff mem_ctx_in_ctx in ein. now exists a.
    + inversion e.
Qed.

(** *** alpha rules *)
Lemma alpha_rule_sound :
  forall (sko : Skolemization) (Gamma : Con) (sigma : Substitution string Term)
    (record : sko_record sko) (T : ExtendedRuleTree) (F : Form) (err : string)
    (getter : Form -> option (list Form)),
    alpha_rule sko Gamma sigma T record F getter err (GuidedTableauSearch__aux sko) = ret true ->
    exists (l : list Form), getter F = Some l /\ F \in Gamma /\
                         GuidedTableauSearch__aux sko (List.app l Gamma) sigma record T = ret true.
Proof.
  intros ???????? e. unfold alpha_rule in e.
  now apply rule_wrapper_sound in e.
Qed.

(** *** alpha-rules getters *)
Lemma getter_neg_neg_sound :
  forall (F : Form) (l : list Form),
    get_neg_neg F = Some l -> exists (G : Form), l = [G] /\ F = Neg (Neg G).
Proof.
  intros ?? e. unfold get_neg_neg in e. destruct F; try inversion e.
  destruct F; try inversion e.
  now exists F.
Qed.

Lemma getter_and_sound :
  forall (F : Form) (l : list Form),
    get_and F = Some l -> exists (F1 F2 : Form), l = [F1 ; F2] /\ F = Neg (Or (Neg F1) (Neg F2)).
Proof.
  intros ?? e. unfold get_and in e. destruct F eqn:eF; try inversion e.
  destruct f eqn:ef; try inversion e.
  destruct f0_1 eqn:f1; try inversion e.
  destruct f0_2 eqn:f2; try inversion e.
  exists f0, f3; auto.
Qed.

Lemma getter_neg_or_sound :
  forall (F : Form) (l : list Form),
    get_neg_or F = Some l -> exists (F1 F2 : Form), l = [Neg F2 ; Neg F1] /\ F = Neg (Or F1 F2).
Proof.
  intros ?? e. unfold get_neg_or in e. destruct F eqn:eF; try inversion e.
  unfold Utils.bind in e.
  have h : exists F1 F2, get_or f = Some ([F1], [F2]).
  { destruct (get_or f) eqn:ef; try inversion e.
    destruct f; try inversion ef. cbn in ef. now exists f1, f2. }
  destruct h as (F1 & F2 & h). rewrite h in e.
  cbn in e. exists F1, F2; split.
  - now injection e => ->.
  - destruct f; try inversion h; auto.
Qed.

Lemma getter_neg_imp_sound :
  forall (F : Form) (l : list Form),
    get_neg_imp F = Some l -> exists (F1 F2 : Form), l = [F1 ; Neg F2] /\ F = Neg (Or (Neg F1) F2).
Proof.
  intros ?? e. unfold get_neg_imp in e. destruct F eqn:eF; try inversion e.
  destruct f eqn:ef; try inversion e.
  destruct f0_1 eqn:ef1; try inversion e.
  now exists f0, f0_2.
Qed.

(** *** beta rules *)
Lemma beta_rule_sound :
  forall (sko : Skolemization) (Gamma : Con) (sigma : Substitution string Term)
    (record : sko_record sko) (T1 T2 : ExtendedRuleTree) (F : Form) (err : string)
    (getter : Form -> option (list Form * list Form)),
    beta_rule sko Gamma sigma T1 T2 record F getter err (GuidedTableauSearch__aux sko) = ret true ->
    exists (l1 l2 : list Form),
      getter F = Some (l1, l2) /\ F \in Gamma /\
        GuidedTableauSearch__aux sko (List.app l1 Gamma) sigma record T1 = ret true /\
        GuidedTableauSearch__aux sko (List.app l2 Gamma) sigma record T2 = ret true.
Proof.
  intros ????????? e. unfold beta_rule in e.
  apply rule_wrapper_sound in e. destruct e as ((l1 & l2) & eg & hin & hact).
  exists l1, l2; repeat split; auto; unfold bind in hact; cbn in hact.

  all: destruct (GuidedTableauSearch__aux sko (l1 ++ Gamma)%list sigma record T1); cbn in *;
    destruct b; unfold ret in hact; cbn in *.

  2,4: injection hact => _ contra; inversion contra.

  all: destruct (GuidedTableauSearch__aux sko (l2 ++ Gamma)%list sigma record T2); cbn in *;
    destruct b; cbn in *.

  2,4: injection hact => _ contra; inversion contra.

  all: injection hact => e; apply app_eq_nil in e; destruct e as [el el'].

  - now rewrite el.
  - now rewrite el'.
Qed.

(** *** beta-rules getters *)

Lemma get_or_sound :
  forall (F : Form) (l : list Form * list Form),
    get_or F = Some l -> exists (F1 F2 : Form), l = ([F1], [F2]) /\ F = Or F1 F2.
Proof.
  intros ?? e. destruct F eqn:eF; cbn in *; try inversion e.
  now exists f1, f2.
Qed.

Lemma get_imp_sound :
  forall (F : Form) (l : list Form * list Form),
    get_imp F = Some l -> exists (F1 F2 : Form), l = ([Neg F1], [F2]) /\ F = Or (Neg F1) F2.
Proof.
  intros ?? e. destruct F eqn:eF; cbn in *; try inversion e.
  destruct f1 eqn:ef1; try inversion e.
  now exists f, f2.
Qed.

Lemma get_neg_and_sound :
  forall (F : Form) (l : list Form * list Form),
    get_neg_and F = Some l -> exists (F1 F2 : Form), l = ([Neg F1], [Neg F2]) /\ F = Neg (Neg (Or (Neg F1) (Neg F2))).
Proof.
  intros ?? e. destruct F eqn:eF; cbn in *; try inversion e.
  destruct f eqn:ef; cbn in *; try inversion e.
  destruct f0 eqn:ef0; cbn in *; try inversion e.
  destruct f1_1 eqn:ef1_1; cbn in *; try inversion e.
  destruct f1_2 eqn:ef1_2; cbn in *; try inversion e.
  now exists f1, f2.
Qed.

Lemma get_equ_sound :
  forall (F : Form) (l : list Form * list Form),
    get_equ F = Some l -> exists (F1 F2 : Form), l = ([Neg F1 ; Neg F2], [F2 ; F1]) /\
                                             F = Neg (Or (Neg (Or (Neg F1) F2)) (Neg (Or (Neg F2) F1))).
Proof.
  intros ?? e. destruct F eqn:eF; cbn in *; try inversion e.
  destruct f eqn:ef; cbn in *; try inversion e.
  destruct f0_1; cbn in *; try inversion e.
  destruct f0_2; cbn in *; try inversion e.
  destruct f0_1; cbn in *; try inversion e.
  destruct f0_1_1; cbn in *; try inversion e.
  destruct f0_2; cbn in *; try inversion e.
  destruct f0_2_1; cbn in *; try inversion e.
  destruct (eqb f0_1_1 f0_2_2) eqn:ef0;
    destruct (eqb f0_2_1 f0_1_2) eqn:ef1; cbn in e; try inversion e.
  rewrite !eqbIsEq in ef0, ef1. subst.
  exists f0_2_2, f0_1_2; split; auto.
Qed.

Lemma get_neg_equ_sound :
  forall (F : Form) (l : list Form * list Form),
    get_neg_equ F = Some l ->
    exists (F1 F2 : Form), l = ([Neg F2 ; F1], [Neg F1 ; F2]) /\
                        F = Neg (Neg (Or (Neg (Or (Neg F1) F2)) (Neg (Or (Neg F2) F1)))).
Proof.
  intros ?? e. destruct F eqn:eF; try inversion e.
  have e0 : exists l0, get_equ f = Some l0. { destruct (get_equ f) eqn:eequ; [now exists p|inversion H0]. }
  destruct e0 as (l0 & el0).
  have el0' := get_equ_sound _ _ el0. destruct el0' as (F1 & F2 & el0' & eF').
  rewrite el0 el0' in H0. exists F1, F2; split.
  - now injection H0 => <-.
  - now apply f_equal.
Qed.

(** *** Gamma rules *)

Lemma gamma_rule_sound :
  forall (sko : Skolemization) (Gamma : Con) (sigma : Substitution string Term)
    (record : sko_record sko) (T : ExtendedRuleTree) (F : Form) (x : string) (err : string)
    (getter : Form -> option Form),
    gamma_rule sko Gamma sigma T record F x getter err (GuidedTableauSearch__aux sko) = ret true ->
    exists (G : Form), getter F = Some G /\ F \in Gamma /\
                         GuidedTableauSearch__aux sko (G{0 \to Free x} :: Gamma) sigma record T = ret true.
Proof.
  intros ????????? e. unfold gamma_rule in e.
  now apply rule_wrapper_sound in e.
Qed.

(** *** Gamma rules getters *)

Lemma get_all_sound :
  forall (F G : Form),
    get_all F = Some G -> F = All G.
Proof.
  intros ?? e. destruct F eqn:eF; cbn in *; try inversion e; auto.
Qed.

Lemma get_neg_ex_sound :
  forall (F G : Form),
    get_neg_ex F = Some G -> exists (H : Form), G = Neg H /\ F = Neg (Neg (All (Neg H))).
Proof.
  intros ?? e. destruct F eqn:eF; cbn in *; try inversion e.
  destruct f eqn:ef; try inversion e.
  destruct f0 eqn:ef0; try inversion e.
  destruct f1 eqn:ef1; try inversion e.
  now exists f2.
Qed.

(** *** Delta rules *)

Lemma delta_rule_sound :
  forall (sko : Skolemization) (Gamma : Con) (sigma : Substitution string Term)
    (record : sko_record sko) (T : ExtendedRuleTree) (F : Form) (t : Term) (err : string)
    (getter : Form -> option Form),
    delta_rule sko Gamma sigma T record F t getter err (GuidedTableauSearch__aux sko) = ret true ->
    exists (f : string) (G : Form),
      getter F = Some G /\ F \in Gamma /\ sko t F (fv Gamma) record = true /\ get_symbol t = Some f /\
        GuidedTableauSearch__aux sko (G{0 \to t} :: Gamma) sigma (add_symbol f F record) T = ret true.
Proof.
  intros ????????? e. unfold delta_rule in e.
  apply rule_wrapper_sound in e.
  destruct e as (G & eG & hin & e).
  destruct (sko t F (fv Gamma) record) eqn:hsko; try inversion e.
  destruct (get_symbol t) eqn:esym; try inversion e.
  exists a, G; repeat split; auto.
Qed.

(** *** Delta rules getters *)

Lemma get_ex_sound :
  forall (F G : Form),
    get_ex F = Some G -> F = Neg (All (Neg G)).
Proof.
  intros ?? e; destruct F eqn:eF; try inversion e.
  destruct f eqn:ef; try inversion e.
  now destruct f0 eqn:ef0; try inversion e.
Qed.

Lemma get_neg_all_sound :
  forall (F G : Form),
    get_neg_all F = Some G -> exists (H : Form), G = Neg H /\ F = Neg (All H).
Proof.
  intros ?? e; destruct F eqn:eF; try inversion e.
  destruct f eqn:ef; try inversion e.
  now exists f0.
Qed.

(** *** Soundness of the auxiliary algorithm. *)

Lemma auxiliary_GuidedTableauSearch_sound :
  forall (sko : Skolemization) (Gamma : Con) (sigma : Substitution string Term)
    (record : sko_record sko) (tree : ExtendedRuleTree),
    GuidedTableauSearch__aux sko Gamma sigma record tree = ret true ->
    hasTableau_ sko Gamma record sigma.
Proof.
  intros ????? e. generalize dependent Gamma. revert record. induction tree as [|T1 IHT1 r T2 IHT2];
    intros record Gamma e.

  (* Case: [Leaf] *)
  - destruct (auxiliary_GuidedTableauSearch_Leaf_sound e) as [hin | h].
    + now apply hasTableauBot.
    + destruct h as [ hin | [ P [ P' [ hin [ hin' e' ] ] ] ] ].
      * apply In_nth_error in hin. destruct hin as (n & e').
        eapply ExtendedRules.hasTableauNegTop; eauto.
      * eapply hasTableauContr.
        -- apply hin'.
        -- apply hin.
        -- auto.

  (* Case: [Node] *)
  - destruct r.

    (* The first 4 goals are alpha rules. *)
    1-4: cbn in e; apply alpha_rule_sound in e; destruct e as (l & e & hin & e1).

    (* The 5 next goals are beta rules. *)
    5-9: cbn in e; apply beta_rule_sound in e; destruct e as (l1 & l2 & e & hin & e1 & e2).

    (* The next two are gamma rules. *)
    10,11: cbn in e; apply gamma_rule_sound in e; destruct e as (G & e & hin & e1).

    (* The last two cases are delta rules. *)
    12,13: cbn in e; apply delta_rule_sound in e;
      destruct e as (g & G & e & hin & hsko & esym & e1).

    (* Case: [AlphaNegNeg] *)
    + apply getter_neg_neg_sound in e; destruct e as (G & el & e); rewrite e in hin.
      eapply hasTableauNegNeg; eauto.
      rewrite el in e1; now apply IHT1.

    (* Case: [AlphaAnd] *)
    + apply getter_and_sound in e; destruct e as (F1 & F2 & el & e); rewrite e in hin.
      eapply hasTableauNegOr; eauto. eapply hasTableauNegNeg.
      * now left.
      * eapply hasTableauNegNeg.
        -- do 2 right; now left.
        -- apply weakening with (Gamma := Gamma ,, F2 ,, F1).
           ++ cbn. symmetry; etransitivity; [apply f_equal; now rewrite -union_assoc union_idemp|].
              etransitivity; [apply f_equal;
                              now rewrite -union_assoc (union_comm (fv F2) (fv F1)) union_assoc|];
                rewrite -!union_assoc union_idemp //.
           ++ do 2 apply extend_sub_ctx; do 2 apply cons_sub_ctx; apply sub_ctx_refl.
           ++ rewrite el in e1; now apply IHT1.

    (* Case: [AlphaNegOr] *)
    + apply getter_neg_or_sound in e; destruct e as (F1 & F2 & el & e); rewrite e in hin.
      eapply hasTableauNegOr; eauto.
      rewrite el in e1; now apply IHT1.

    (* Case: [AlphaNegImp] *)
    + apply getter_neg_imp_sound in e; destruct e as (F1 & F2 & el & e); rewrite e in hin.
      eapply hasTableauNegOr; eauto.
      eapply hasTableauNegNeg.
      * right; now left.
      * apply weakening with (Gamma := Gamma ,, Neg F2 ,, F1).
        ++ now cbn; rewrite -!union_assoc (union_comm (fv F1) (fv F2));
             symmetry; etransitivity; [refine (f_equal (fun s => s \union fv Gamma) _);
                                       rewrite union_assoc union_idemp //|].
        ++ do 2 apply extend_sub_ctx. apply cons_sub_ctx, sub_ctx_refl.
        ++ rewrite el in e1; now apply IHT1.

    (* Case: [BetaOr] *)
    + apply get_or_sound in e; destruct e as (F1 & F2 & el & e); rewrite e in hin.
      eapply hasTableauOr; eauto.
      * injection el => e2' e1'; rewrite e1' in e1; now apply IHT1.
      * injection el => e2' e1'; rewrite e2' in e2; now apply IHT2.

    (* Case: [BetaImp] *)
    + apply get_imp_sound in e; destruct e as (F1 & F2 & el & e); rewrite e in hin.
      eapply hasTableauOr; eauto.
      * injection el => e2' e1'; rewrite e1' in e1; now apply IHT1.
      * injection el => e2' e1'; rewrite e2' in e2; now apply IHT2.

    (* Case: [BetaNegAnd] *)
    + apply get_neg_and_sound in e; destruct e as (F1 & F2 & el & e); rewrite e in hin.
      eapply hasTableauNegNeg; eauto.
      have efv1 : @fv_list string _ _ (Gamma ,, Or (Neg F1) (Neg F2)) =
                    @fv_list string _ _ (Gamma ,, Neg (Neg (Or (Neg F1) (Neg F2)))) by reflexivity.
      have efv2 : @fv_list string _ _ (Gamma ,, Neg (Neg (Or (Neg F1) (Neg F2)))) =
                    @fv_list string _ _ Gamma by symmetry; apply fv_list_in.
      eapply hasTableauOr.
      * now left.
      * apply weakening with (Gamma := Gamma ,, Neg F1).
        -- now etransitivity; [cbn; unfold fv, fv_ctx; now rewrite -efv2|].
        -- apply extend_sub_ctx, cons_sub_ctx, sub_ctx_refl.
        -- injection el => e2' e1'; rewrite e1' in e1; now apply IHT1.
      * apply weakening with (Gamma := Gamma ,, Neg F2).
        -- now etransitivity; [cbn; unfold fv, fv_ctx; now rewrite -efv2|].
        -- apply extend_sub_ctx, cons_sub_ctx, sub_ctx_refl.
        -- injection el => e2' e1'; rewrite e2' in e2; now apply IHT2.

    (* Case: [BetaEqu] *)
    + apply get_equ_sound in e; destruct e as (F1 & F2 & el & e); rewrite e in hin.
      eapply hasTableauNegOr; eauto.
      do 2 (eapply hasTableauNegNeg; [right; now left|]).
      eapply hasTableauOr; [now left| |].
      * eapply hasTableauOr; [do 2 right; now left| |].
        -- apply weakening with (Gamma := Gamma ,, Neg F2 ,, Neg F1).
           ++ cbn; do 2 apply union_congl;
              symmetry; rewrite !union_assoc; etransitivity;
                [apply f_equal; rewrite -!union_assoc union_idemp !union_assoc;
                 apply f_equal; rewrite -!union_assoc union_idemp !union_assoc;
                 apply f_equal; rewrite -!union_assoc union_idemp // |].
              have efv : fv Gamma = ((fv F1 \union fv F2) \union (fv F2 \union fv F1)) \union @fv_list string _ _ Gamma.
              { rewrite (fv_list_in f); rewrite e; auto. }
              symmetry; etransitivity; [apply efv|]; rewrite -!union_assoc;
                refine (f_equal (fun s => s \union fv Gamma) _).
              rewrite (union_comm (fv F1) (fv F2)); rewrite !union_assoc; do 2 f_equal;
                do 2 rewrite (union_comm (fv F1) (fv F2)); rewrite -union_assoc union_idemp //.
           ++ do 2 apply extend_sub_ctx; do 4 apply cons_sub_ctx; apply sub_ctx_refl.
           ++ injection el => e2' e1'; rewrite e1' in e1; now apply IHT1.
        -- apply hasTableauContr with (P := F2) (P' := Neg F2); auto.
           ++ now left.
           ++ right; now left.
      * eapply hasTableauOr; [do 2 right; now left| |].
        -- apply hasTableauContr with (P := F1) (P' := Neg F1); auto.
           ++ right; now left.
           ++ now left.
        -- apply weakening with (Gamma := Gamma ,, F1 ,, F2).
           ++ cbn; do 2 apply union_congl;
                have efv : fv Gamma = ((fv F1 \union fv F2) \union (fv F2 \union fv F1)) \union @fv_list string _ _ Gamma.
              { rewrite (fv_list_in f); rewrite e; auto. }
              etransitivity; [apply efv|]; rewrite -!union_assoc;
                refine (f_equal (fun s => s \union fv Gamma) _); symmetry; etransitivity;
                [now do 2 (rewrite !union_assoc; apply f_equal;
                           rewrite -!union_assoc union_idemp)|].
              rewrite union_comm !union_assoc; do 2 f_equal;
                rewrite union_idemp -union_assoc union_idemp union_comm //.
           ++ do 2 apply extend_sub_ctx; do 4 apply cons_sub_ctx; apply sub_ctx_refl.
           ++ injection el => e2' e1'; rewrite e2' in e2; now apply IHT2.

    (* Case: [BetaNegEqu] *)
    + apply get_neg_equ_sound in e; destruct e as (F1 & F2 & el & e); rewrite e in hin.
      eapply hasTableauNegNeg; eauto.
      eapply hasTableauOr; [now left| |].
      -- eapply hasTableauNegOr; [now left|].
         eapply hasTableauNegNeg; [right; now left|].
         apply weakening with (Gamma := Gamma ,, F1 ,, Neg F2).
         ++ cbn; rewrite -!union_assoc; apply union_congr; symmetry; etransitivity;
              [apply union_congr; rewrite !union_assoc union_idemp; do 2 apply union_congl;
               rewrite -!union_assoc union_idemp //|].
            etransitivity; [apply union_congr; rewrite union_comm; apply union_congr;
                            apply union_congl; rewrite union_comm //|];
              rewrite !union_assoc !union_idemp -!union_assoc union_idemp;
              rewrite (union_comm (fv F2 \union fv F1) (fv F2)) -!union_assoc union_idemp
                !union_assoc union_idemp //.
         ++ apply sub_ctx_cong, extend_sub_ctx. do 3 apply cons_sub_ctx; apply sub_ctx_refl.
         ++ injection el => e2' e1'; rewrite e1' in e1; now apply IHT1.
      -- eapply hasTableauNegOr; [now left|].
         eapply hasTableauNegNeg; [right; now left|].
         apply weakening with (Gamma := Gamma ,, F2 ,, Neg F1).
         ++ cbn; rewrite -!union_assoc; apply union_congr; symmetry; etransitivity;
              [now do 3 (apply union_congr; rewrite !union_assoc union_idemp;
                         rewrite -!union_assoc)|].
            etransitivity; [now do 2 (apply union_congr;
                                      rewrite union_comm -!union_assoc union_idemp)|];
              rewrite !union_assoc !union_idemp union_comm //.
         ++ apply sub_ctx_cong, extend_sub_ctx. do 3 apply cons_sub_ctx; apply sub_ctx_refl.
         ++ injection el => e2' e1'; rewrite e2' in e2; now apply IHT2.

    (* Case: [GammaAll] *)
    + apply get_all_sound in e; rewrite e in hin.
      eapply hasTableauAll; eauto.

    (* Case: [GammaNegEx] *)
    + apply get_neg_ex_sound in e; destruct e as (F & eF & e); rewrite e in hin.
      subst. eapply hasTableauNegNeg; eauto.
      eapply hasTableauAll with (x := s); [now left|].
      apply weakening with (Gamma := Gamma ,, (Neg F){0 \to Free s}).
      * have efv : fv Gamma = @fv_list string _ _ (Gamma ,, All (Neg F)).
        { now rewrite (fv_list_in (Neg (Neg (All (Neg F)))) Gamma). }
        now cbn; rewrite efv; cbn; symmetry;
          etransitivity; [rewrite union_comm -!union_assoc union_idemp union_comm //|].
      * apply extend_sub_ctx, cons_sub_ctx, sub_ctx_refl.
      * now apply IHT1.

    (* Case: [DeltaEx] *)
    + apply get_ex_sound in e; rewrite !e in hin hsko.
      eapply hasTableauNegAll with (t := t) (Hsko := hsko); eauto.
      eapply hasTableauNegNeg; [now left|].
      change (hasTableau_ sko ((Gamma ,, Neg (Neg G) {0 \to t}) ,, G {0 \to t})
                (add_symbol (symbol sko t hsko) (Neg (All (Neg G))) record) sigma).
      apply weakening with (Gamma := Gamma ,, G {0 \to t}).
      * cbn; rewrite -union_assoc union_idemp //.
      * apply extend_sub_ctx, cons_sub_ctx, sub_ctx_refl.
      * rewrite (symbol_sound hsko) in esym; injection esym => ->.
        rewrite -e; now apply IHT1.

    (* Case: [DeltaNegAll] *)
    + apply get_neg_all_sound in e; destruct e as (F & eF & e); rewrite e in hin hsko.
      eapply hasTableauNegAll with (t := t) (Hsko := hsko); eauto.
      rewrite (symbol_sound hsko) in esym; injection esym => ->.
      rewrite -e; rewrite eF in e1; now apply IHT1.
Qed.

Theorem GuidedTableauSearch_sound :
  forall (sko : Skolemization) (Gamma : Con) (sigma : Substitution string Term)
    (tree : ExtendedRuleTree),
    GuidedTableauSearch sko Gamma sigma tree = ret true ->
    hasTableau sko Gamma sigma.
Proof. intros. eapply auxiliary_GuidedTableauSearch_sound; eauto. Qed.

(** ** 3. Tactic *)

(** Using the algorithm together with the soundness theorem, we provide a tactic [tableaux]
    that gives a proof [hasTableau sko Gamma sigma] if possible, or fails with an error otherwise. *)
Ltac tableaux tree :=
  try (apply (GuidedTableauSearch_sound _ _ _ tree); native_compute;
       match goal with
       | [ |- (false, [?err]) = (true, []) ] =>
           idtac "tableaux failed with the following error message: " err; fail
       | _ => reflexivity
       end).
