Set Warnings "-native-compiler".
From Tableaux Require Import All.

Definition T : EForm :=
	ENeg (EAll "X3" (EAnd (EPred "p" [(EVar "X3")]) (ENeg (EPred "p" [(EVar "X3")])))) 
.

Definition subst := translate_substitution [].


Definition T_Proof : ExtendedRuleTree.
Proof.
apply (mkUnaryNode ( AlphaNegNeg (Neg (Neg [[ EAll "X3" (EAnd (EPred "p" [(EVar "X3")]) (ENeg (EPred "p" [(EVar "X3")]))) ]])) ) ).
apply (mkUnaryNode ( GammaAll [[ EAll "X3" (EAnd (EPred "p" [(EVar "X3")]) (ENeg (EPred "p" [(EVar "X3")]))) ]] "X3_5" ) ).
apply (mkUnaryNode ( AlphaAnd [[ EAnd (EPred "p" [(EVar "X3_5")]) (ENeg (EPred "p" [(EVar "X3_5")])) ]] ) ).
exact (mkClosure [[ EPred "p" [(EVar "X3_5")] ]] [[ ENeg (EPred "p" [(EVar "X3_5")]) ]]).
Defined.

Theorem hasTableau_T_Proof :
	hasTableau OuterSkolemization [  Neg (translate_EForm T) ] subst.
Proof.
tableaux T_Proof.
Qed.
