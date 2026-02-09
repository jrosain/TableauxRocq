Set Warnings "-native-compiler".
From Tableaux Require Import All.

Definition T : EForm :=
	ENeg (EBot) 
.

Definition subst := translate_substitution [].


Definition T_Proof : ExtendedRuleTree.
Proof.
apply (mkUnaryNode ( AlphaNegNeg (Neg (Neg [[ EBot ]])) ) ).
exact mkTrivialClosure.
Defined.

Theorem hasTableau_T_Proof :
	hasTableau OuterSkolemization [  Neg (translate_EForm T) ] subst.
Proof.
tableaux T_Proof.
Qed.
