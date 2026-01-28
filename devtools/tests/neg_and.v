
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

Theorem hasTableau_T_proof :
	GuidedTableauSearch InnerSkolemization [  Neg [[ T ]] ]
subst T_Proof = ret true.
Proof.
now native_compute.
Qed.

