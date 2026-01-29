
Set Warnings "-native-compiler".
From Tableaux Require Import All.

Definition T : EForm :=
	EImp (EPred "a" []) (EPred "a" []) 
.

Definition subst := translate_substitution [].


Definition T_Proof : ExtendedRuleTree.
Proof.
apply (mkUnaryNode ( AlphaNegImp (Neg [[ EImp (EPred "a" []) (EPred "a" []) ]]) ) ).
exact Leaf.
Defined.

Theorem hasTableau_T_Proof :
	hasTableau InnerSkolemization [  Neg (translate_EForm T) ] subst.
Proof.
tableaux T_Proof.
Qed.

