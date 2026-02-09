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
exact mkTrivialClosure.
}
{
exact mkTrivialClosure.
}
Defined.

Theorem hasTableau_T_Proof :
	hasTableau OuterSkolemization [  Neg (translate_EForm T) ] subst.
Proof.
tableaux T_Proof.
Qed.
