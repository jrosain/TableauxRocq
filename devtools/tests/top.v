
Set Warnings "-native-compiler".
From Tableaux Require Import All.

Definition T : EForm :=
	ETop 
.

Definition subst := translate_substitution [].


Definition T_Proof : ExtendedRuleTree.
Proof.
exact Leaf.
Defined.

Theorem hasTableau_T_proof :
	GuidedTableauSearch InnerSkolemization [  Neg [[ T ]] ]
subst T_Proof = ret true.
Proof.
now native_compute.
Qed.

