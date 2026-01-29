
Set Warnings "-native-compiler".
From Tableaux Require Import All.

Definition T : EForm :=
	EAnd (ETop) (ETop) 
.

Definition subst := translate_substitution [].


Definition T_Proof : ExtendedRuleTree.
Proof.
apply (mkBinaryNode ( BetaNegAnd (Neg [[ EAnd (ETop) (ETop) ]]) ) ).
{
exact Leaf.
}
{
exact Leaf.
}
Defined.

Theorem hasTableau_T_Proof :
	hasTableau InnerSkolemization [  Neg (translate_EForm T) ] subst.
Proof.
tableaux T_Proof.
Qed.

