
Set Warnings "-native-compiler".
From Tableaux Require Import All.

Definition Axiom0 : EForm :=
	ENeg (EPred "a" []) 
.

Definition T : EForm :=
	ENeg (EPred "a" []) 
.

Definition subst := translate_substitution [].


Definition T_Proof : ExtendedRuleTree.
Proof.
apply (mkUnaryNode ( AlphaNegNeg (Neg (Neg [[ EPred "a" [] ]])) ) ).
exact Leaf.
Defined.

Theorem hasTableau_T_proof :
	GuidedTableauSearch InnerSkolemization [  [[ Axiom0 ]] ;  Neg [[ T ]] ]
subst T_Proof = ret true.
Proof.
now native_compute.
Qed.

