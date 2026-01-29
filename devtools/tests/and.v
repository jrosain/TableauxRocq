
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

Theorem hasTableau_T_Proof :
	hasTableau InnerSkolemization [  Neg (translate_EForm T) ] subst.
Proof.
tableaux T_Proof.
Qed.

