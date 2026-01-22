
From Tableaux Require Import All.

Import ATPCompat.

Definition T : EForm :=
	ENeg (EAnd (EPred "a" []) (ENeg (EPred "a" []))) 
.

Definition subst := translate_substitution [].


Theorem T_proof :
	hasTableau OuterSkolemization {{  translate_EForm (ENeg T) }} subst.
Proof.
exists \{\}, \{\}.
eapply hasTableauNegNeg with (i := 0).
1: reflexivity. 
eapply hasTableauAnd with (i := 0).
1: reflexivity. 
eapply hasTableauContr with (i := 1) (j := 0).
1: reflexivity. 
1: reflexivity. 
reflexivity.
Qed.

