Set Warnings "-native-compiler".
From Tableaux Require Import All.
Import ExtendedSyntaxNotation.

Definition Axiom0 : EForm := "p" ''().
Definition Axiom1 : EForm := "q" ''().
Definition conjecture : EForm := ("p" ''()) '<=> ("q" ''()).
Definition subst := translate_substitution [].

Definition proof : ExtendedRuleTree :=
  mkBinaryNode
    (BetaNegEqu (Neg [[ conjecture ]]))
    (mkClosure (Neg [[ "q" ''() ]]) [[ "q" ''() ]])
    (mkClosure (Neg [[ "p" ''() ]]) [[ "p" ''() ]]).

Theorem hasTableau_conjecture :
    hasTableau InnerSkolemization [  [[ Axiom0 ]];  [[ Axiom1 ]];  Neg [[ conjecture ]] ] subst.
Proof. tableaux proof. Qed.
