Set Warnings "-native-compiler".
From Tableaux Require Import All.

Definition T : EForm :=
	ENeg (EImp (ETop) (EBot)) 
.

Definition subst := translate_substitution [].


Definition T_Proof : ExtendedRuleTree.
Proof.
apply (mkUnaryNode ( AlphaNegNeg (Neg (Neg [[ EImp (ETop) (EBot) ]])) ) ).
apply (mkBinaryNode ( BetaImp [[ EImp (ETop) (EBot) ]] ) ).
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
