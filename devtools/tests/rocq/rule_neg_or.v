Set Warnings "-native-compiler".
From Tableaux Require Import All.

Definition T : EForm :=
	EOr (EImp (EPred "a" []) (EOr (EPred "a" []) (ENeg (EPred "a" [])))) (EOr (ENeg (EPred "a" [])) (EPred "a" [])) 
.

Definition subst := translate_substitution [].


Definition T_Proof : ExtendedRuleTree.
Proof.
apply (mkUnaryNode ( AlphaNegOr (Neg [[ EOr (EImp (EPred "a" []) (EOr (EPred "a" []) (ENeg (EPred "a" [])))) (EOr (ENeg (EPred "a" [])) (EPred "a" [])) ]]) ) ).
apply (mkUnaryNode ( AlphaNegImp (Neg [[ EImp (EPred "a" []) (EOr (EPred "a" []) (ENeg (EPred "a" []))) ]]) ) ).
apply (mkUnaryNode ( AlphaNegOr (Neg [[ EOr (ENeg (EPred "a" [])) (EPred "a" []) ]]) ) ).
exact (mkClosure [[ ENeg (EPred "a" []) ]] [[ EPred "a" [] ]]).
Defined.

Theorem hasTableau_T_Proof :
	hasTableau OuterSkolemization [  Neg (translate_EForm T) ] subst.
Proof.
tableaux T_Proof.
Qed.
