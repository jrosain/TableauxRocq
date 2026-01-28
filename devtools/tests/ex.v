
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
exact Leaf.
Defined.

Theorem hasTableau_T_proof :
	GuidedTableauSearch InnerSkolemization [  Neg [[ T ]] ]
subst T_Proof = ret true.
Proof.
now native_compute.
Qed.

