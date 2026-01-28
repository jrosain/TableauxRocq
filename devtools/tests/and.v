
Set Warnings "-native-compiler".
From Tableaux Require Import All.

Definition T : EForm :=
	ENeg (EAnd (EPred "a" []) (ENeg (EPred "a" []))) 
.

Definition subst := translate_substitution [].


Definition T_Proof : ExtendedRuleTree.
Proof.
apply (mkUnaryNode ( AlphaNegNeg (Neg (Neg [[ EAnd (EPred "a" []) (ENeg (EPred "a" [])) ]])) ) ).
apply (mkUnaryNode ( AlphaAnd [[ EAnd (EPred "a" []) (ENeg (EPred "a" [])) ]] ) ).
exact Leaf.
Defined.

Theorem hasTableau_T_proof :
	GuidedTableauSearch InnerSkolemization [  Neg [[ T ]] ]
subst T_Proof = ret true.
Proof.
now native_compute.
Qed.

