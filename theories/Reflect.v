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
| AlphaNegNeg : EForm -> ExtendedRule
| AlphaAnd : EForm -> ExtendedRule
| AlphaNegOr : EForm -> ExtendedRule
| AlphaNegImp : EForm -> ExtendedRule
| BetaOr : EForm -> ExtendedRule
| BetaImp : EForm -> ExtendedRule
| BetaNegAnd : EForm -> ExtendedRule
| BetaEqu : EForm -> ExtendedRule
| BetaNegEqu : EForm -> ExtendedRule
| GammaAll : EForm -> ExtendedRule
| GammaNegEx : EForm -> ExtendedRule
| DeltaEx : EForm -> ExtendedRule
| DeltaNegAll : EForm -> ExtendedRule.

(** As we want a proof tree, we will take a tree of extended rules as an input of the algorithm.
    Unary rules can be implemented by ignoring the *2nd* child of the tree. *)
Inductive ExtendedRuleTree : Type :=
| Leaf : ExtendedRuleTree
| Node : ExtendedRuleTree -> ExtendedRule -> ExtendedRuleTree -> ExtendedRuleTree.

(** A small [Result] monad that stores the issues. *)
Definition Result (A : Type) : Type := A * list string.

Definition ret {A : Type} (x : A) : Result A := (x, []).

Definition bind {A B : Type} (r : Result A) (f : A -> Result B) : Result B :=
  let (x, s) := f (fst r) in
  (x, List.app (snd r) s).

Definition error {A : Type} (x : A) (s : string) : Result A := (x, [s]).

Notation "r >>= f" := (bind r f) (at level 50).

(** Returns true iff [Bot] or [Neg ETop] is in the list. *)
Definition trivial_contradiction (Gamma : list Form) : bool :=
  List.existsb (fun F => orb (eqb F Bot) (eqb F [[ ENeg ETop ]])) Gamma.

Definition is_positive_litteral (F : Form) : bool :=
  match F with
  | Pred _ _ => true
  | _ => false
  end.

Definition is_negative_litteral (F : Form) : bool :=
  match F with
  | Neg F => is_positive_litteral F
  | _ => false
  end.

(** Returns true iff there exists two litterals [P] and [P'] such that [Neg P@[sigma] = P'@[sigma]] in
    [Gamma]. *)
Definition litteral_contradiction (Gamma : list Form) (sigma : Substitution string Term) : bool :=
  let Gamma__pos := List.filter is_positive_litteral Gamma in
  let Gamma__neg := List.filter is_negative_litteral Gamma in
  List.existsb (fun F => List.existsb (fun G => eqb ((Neg F)@[sigma]) (G@[sigma])) Gamma__neg) Gamma__pos.

Definition get_neg_neg (F : Form) : option (list Form) :=
  match F with
  | Neg F => match F with
          | Neg F => Some [F]
          | _ => None
          end
  | _ => None
  end.

Definition get_or (F : Form) : option (list Form * list Form) :=
  match F with
  | Or F1 F2 => Some ([F1], [F2])
  | _ => None
  end.

Definition get_and (F : Form) : option (list Form) :=
  match F with
  | Neg F =>
      Utils.bind (get_or F)
        (fun l =>
           match l with
           | ([F1], [F2]) =>
               match F1, F2 with
               | Neg F1, Neg F2 => Some [F1 ; F2]
               | _, _ => None
               end
           | _ => None
           end)
  | _ => None
  end.

Definition get_neg_or (F : Form) : option (list Form) :=
  match F with
  | Neg F => Utils.bind (get_or F) (fun l => Some (List.map (fun F => Neg F) (List.app (fst l) (snd l))))
  | _ => None
  end.

Definition get_neg_imp (F : Form) : option (list Form) :=
  match F with
  | Neg F => Utils.bind (get_or F)
            (fun l => match l with
                   | ([F1], [F2]) =>
                       match F1 with
                       | Neg F1 => Some [ F1 ; Neg F2 ]
                       | _ => None
                       end
                   | _ => None
                   end)
  | _ => None
  end.

Definition get_imp (F : Form) : option (list Form * list Form) := get_or F.

Definition get_neg_and (F : Form) : option (list Form * list Form) :=
  Utils.bind (get_neg_neg F) (fun l => get_or (List.hd Bot l)).

Definition get_equ (F : Form) : option (list Form * list Form) :=
  match get_neg_or F with
  | Some [F1 ; F2] =>
      match get_or F1, get_or F2 with
      | Some ([nF], [G]), Some ([nG], [F]) => Some ([nF ; nG], [G ; F])
      | _, _ => None
      end
  | _ => None
  end.

Definition get_neg_equ (F : Form) : option (list Form * list Form) :=
  match get_neg_neg F with
  | Some [F] =>
      match get_or F with
      | Some ([F1], [F2]) =>
          match get_neg_or F1, get_neg_or F2 with
          | Some l, Some l' => Some (l, l')
          | _, _ => None
          end
      | _ => None
      end
  | _ => None
  end.

Definition get_all (F : Form) : option Form :=
  match F with
  | All F => Some F
  | _ => None
  end.

Definition get_neg_ex (F : Form) : option Form :=
  match F with
  | Neg (All (Neg F)) => Some F
  | _ => None
  end.

Definition pr_form (F : Form) : string := "*not yet implemented*".
Definition pr_context (Gamma : list Form) : string := "*not yet implemented*".

(** The guided proof-search is the following algorithm:
    - on a leaf: it tries to search for a closure [Bot] or [Neg Top] or a contradiction using
      the supplied substitution ; returns [false] if no closure rule can be found ;
    - on a node: it tries to apply the given rule on the given formula, and calls the
      algorithm recursively.

    /!\ it requires that the string "@" does not appear in the identifiers to work properly /!\ *)
Fixpoint GuidedTableauSearch__aux
  (i : nat) (j : nat)
  (Gamma : list Form) (sigma : Substitution string Term) (tree : ExtendedRuleTree) : Result bool :=
  match tree with
  | Leaf =>
      if trivial_contradiction Gamma
      then ret true
      else if litteral_contradiction Gamma sigma
           then ret true
           else error false ("No contradiction in the context: " ++ pr_context Gamma)
  | Node T1 rule T2 =>

      let alpha_rule (getter : Form -> option (list Form)) (err : string) (F : Form) :=
        match getter F with
        | None => error false ("The formula " ++ pr_form F ++ " is not a " ++ err)
        | Some l => GuidedTableauSearch__aux i j (List.app l Gamma) sigma T1
        end in

      let beta_rule (getter : Form -> option (list Form * list Form)) (err : string) (F : Form) :=
        match getter F with
        | None => error false ("The formula " ++ pr_form F ++ " is not a " ++ err)
        | Some (l1, l2) =>
            GuidedTableauSearch__aux i j (List.app l1 Gamma) sigma T1 >>=
              (fun b => if b then GuidedTableauSearch__aux i j (List.app l2 Gamma) sigma T2
                     else ret b)
        end in

      let gamma_rule (getter : Form -> option Form) (err : string) (F : Form) :=
        match getter F with
        | None => error false ("The formula " ++ pr_form F ++ " is not a " ++ err)
        | Some F => GuidedTableauSearch__aux (i + 1) j (F{0 \to Free ("X@" ++ nat_to_string i)} :: Gamma)
                     sigma T1
        end in

      match rule with
      | AlphaNegNeg F => alpha_rule get_neg_neg "double negation" F
      | AlphaAnd F => alpha_rule get_and "conjunction" F
      | AlphaNegOr F => alpha_rule get_neg_or "negated disjunction" F
      | AlphaNegImp F => alpha_rule get_neg_imp "negated implication" F

      | BetaOr F => beta_rule get_or "disjunction" F
      | BetaImp F => beta_rule get_imp "implication" F
      | BetaNegAnd F => beta_rule get_neg_and "negated conjunction" F
      | BetaEqu F => beta_rule get_equ "equivalence" F
      | BetaNegEqu F => beta_rule get_neg_equ "negated equivalence" F

      | GammaAll F => gamma_rule get_all "universal formula" F
      | GammaNegEx F => gamma_rule get_neg_ex "negated existential formula" F

      | _ => error false "Not yet implemented"
      end
  end.

(* | DeltaEx : EForm -> ExtendedRule *)
(* | DeltaNegAll : EForm -> ExtendedRule. *)
(* |  *)

(** ** 2. Soundness *)

Lemma trivial_contradiction_sound :
  forall (Gamma : list Form),
    trivial_contradiction Gamma = true -> List.In Bot Gamma \/ List.In [[ ENeg ETop ]] Gamma.
Proof.
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
    litteral_contradiction Gamma sigma = true ->
    exists (P P' : Form), List.In P Gamma /\ List.In (Neg P') Gamma /\ P@[sigma] = (Neg P')@[sigma].
  Admitted.
