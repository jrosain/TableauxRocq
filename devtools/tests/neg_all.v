
Set Warnings "-native-compiler".
From Tableaux Require Import All.

Definition T : EForm :=
	EAll "X3" (EOr (EPred "p" [(EVar "X3")]) (ENeg (EPred "p" [(EVar "X3")]))) 
.

Definition subst := translate_substitution [].


Definition T_Proof : ExtendedRuleTree.
Proof.
apply (mkUnaryNode ( DeltaNegAll (Neg [[ EAll "X3" (EOr (EPred "p" [(EVar "X3")]) (ENeg (EPred "p" [(EVar "X3")]))) ]]) [[ (EFun "skolem@X3@0" []) ]] ) ).
apply (mkUnaryNode ( AlphaNegOr (Neg [[ EOr (EPred "p" [(EFun "skolem@X3@0" [])]) (ENeg (EPred "p" [(EFun "skolem@X3@0" [])])) ]]) ) ).
apply (mkUnaryNode ( AlphaNegNeg (Neg (Neg [[ EPred "p" [(EFun "skolem@X3@0" [])] ]])) ) ).
exact Leaf.
Defined.

Theorem hasTableau_T_proof :
	GuidedTableauSearch InnerSkolemization [  Neg [[ T ]] ]
subst T_Proof = ret true.
Proof.
now native_compute.
Qed.

