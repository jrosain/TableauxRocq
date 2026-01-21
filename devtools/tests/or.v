
From Tableaux Require Import All.

Import ATPCompat.

Definition T : EForm :=
	EOr (EPred "a" []) (ENeg (EPred "a" [])) 
.

Definition subst := translate_substitution [].


Theorem T_proof :
	hasTableau OuterSkolemization {{  translate_EForm (ENeg T) }} subst.
Proof.
exists \{\}, \{\}.
eapply hasTableauNegOr with (i := 0).
1: reflexivity. 
eapply hasTableauNegNeg with (i := 0).
1: reflexivity. 
eapply hasTableauContr with (i := 0) (j := 2).
1: reflexivity. 
1: reflexivity. 
reflexivity.
Qed.

