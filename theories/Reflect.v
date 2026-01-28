(** * Reflect: sound and complete algorithm to "search" for tableaux proofs *)

From Tableaux Require Import Core.
From Tableaux Require Import ATPCompat.

(** In this file, we implement a guided tableau proof-search procedure. It is named
    "guided" as the rules to apply and the substitution are given.

    It returns a boolean if the tableau is closed. The goal is to show that this procedure
    is correct and complete, to make it possible to output proof certificates from this
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
  | Neg F => Utils.bind (get_or F) (fun l => Some (List.map (fun F => Neg F) (List.app (fst l) (snd l))))
  | _ => None
  end.

Definition get_neg_imp (F : Form) : option (list Form) :=
  match F with
  | Neg (Or (Neg F1) F2)  => Some [F1 ; Neg F2]
  | _ => None
  end.

Definition get_imp (F : Form) : option (list Form * list Form) := get_or F.

Definition get_neg_and (F : Form) : option (list Form * list Form) :=
  Utils.bind (get_neg_neg F) (fun l => get_or (List.hd Bot l)).

Definition get_equ (F : Form) : option (list Form * list Form) :=
  match get_and F with
  | Some [F1 ; F2] =>
      match get_imp F1, get_imp F2 with
      | Some ([nF], [G]), Some ([nG], [F]) => Some ([nF ; nG], [G ; F])
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
  | Neg F => Utils.bind (get_ex F) (fun F => Some (Neg F))
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
      (fun F => if @is_sko _ _ _ sko t F (fv Gamma) record
             then
               match get_symbol t with
               | None => error "This shouldn't ever happen."
               | Some f => search (F{0 \to t} :: Gamma) sigma (add_symbol f F record) T
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
    (Gamma : list Form) (sigma : Substitution string Term)
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

Lemma trivial_contradiction_sound :
  forall (Gamma : list Form),
    trivial_contradiction Gamma = true -> List.In Bot Gamma \/ List.In [[ ENeg ETop ]] Gamma.
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

Lemma litteral_contradiction_sound :
  forall (Gamma : list Form) (sigma : Substitution string Term),
    formula_contradiction Gamma sigma = true ->
    exists (P P' : Form), List.In P Gamma /\ List.In (Neg P') Gamma /\ P@[sigma] = (Neg P')@[sigma].
  Admitted.
