
Set Warnings "-native-compiler".
From Tableaux Require Import All.

Definition Axiom0 : EForm :=
	EPred "p" [(EFun "a" [])] 
.

Definition T : EForm :=
	EEx "X4" (EPred "p" [(EVar "X4")]) 
.

Definition subst := translate_substitution [("X4_6", (EFun "a" []))].


Definition T_Proof : ExtendedRuleTree.
Proof.
apply (mkUnaryNode ( GammaNegEx (Neg [[ EEx "X4" (EPred "p" [(EVar "X4")]) ]]) "X4_6" ) ).
exact Leaf.
Defined.

Theorem hasTableau_T_proof :
	GuidedTableauSearch InnerSkolemization [  [[ Axiom0 ]] ;  Neg [[ T ]] ]
subst T_Proof = ret true.
Proof.
now native_compute.
Qed.

