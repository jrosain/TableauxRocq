From Tableaux Require Import Prelude.All.
From Tableaux Require Export Proofs.

From Tableaux Require Export SyntaxInstance.
From Tableaux Require Export SkolemizationInstances.

Definition Tableau := @Tableau string string string _ _ _.

(* XXX: This data structure should be shared with Tableaux.
          We want a RuleTree and a TableauTree to coincide (actually, they almost already do so it should
          be easy to unify them). *)

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

