Set Warnings "-native-compiler".
From Tableaux Require Import All.

Definition T : EForm :=
	ENeg (EEx "X3" (EAnd (EPred "p" [(EVar "X3")]) (ENeg (EPred "p" [(EVar "X3")])))) 
.

Definition subst := translate_substitution [].


Definition T_Proof : ExtendedRuleTree.
Proof.
apply (mkUnaryNode ( AlphaNegNeg (Neg (Neg [[ EEx "X3" (EAnd (EPred "p" [(EVar "X3")]) (ENeg (EPred "p" [(EVar "X3")]))) ]])) ) ).
apply (mkUnaryNode ( DeltaEx [[ EEx "X3" (EAnd (EPred "p" [(EVar "X3")]) (ENeg (EPred "p" [(EVar "X3")]))) ]] [[ (EFun "skolem@X3@0" []) ]] ) ).
apply (mkUnaryNode ( AlphaAnd [[ EAnd (EPred "p" [(EFun "skolem@X3@0" [])]) (ENeg (EPred "p" [(EFun "skolem@X3@0" [])])) ]] ) ).
exact (mkClosure [[ EPred "p" [(EFun "skolem@X3@0" [])] ]] [[ ENeg (EPred "p" [(EFun "skolem@X3@0" [])]) ]]).
Defined.

Theorem hasTableau_T_Proof :
	hasTableau OuterSkolemization [  Neg (translate_EForm T) ] subst.
Proof.
tableaux T_Proof.
Qed.
