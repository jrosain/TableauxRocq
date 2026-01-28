
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
exact Leaf.
}
{
exact Leaf.
}
Defined.

Theorem hasTableau_T_proof :
	GuidedTableauSearch InnerSkolemization [  Neg [[ T ]] ]
subst T_Proof = ret true.
Proof.
now native_compute.
Qed.

