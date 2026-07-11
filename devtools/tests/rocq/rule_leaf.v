Set Warnings "-native-compiler".
From Tableaux Require Import All.

Definition Axiom0 : EForm :=
	EPred "a" [] 
.

Definition T : EForm :=
	EPred "a" [] 
.

Definition subst := translate_substitution [].


Definition T_Proof : ExtendedRuleTree.
Proof.
exact (mkClosure [[ EPred "a" [] ]] [[ ENeg (EPred "a" []) ]]).
Defined.

Theorem hasTableau_T_Proof :
	hasTableau OuterSkolemization [  [[ Axiom0 ]] ;  Neg (translate_EForm T) ] subst.
Proof.
tableaux T_Proof.
Qed.
