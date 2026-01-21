
From Tableaux Require Import All.

Import ATPCompat.

Definition T : EForm :=
	EImp (EPred "a" []) (EPred "a" []) 
.

Definition subst := translate_substitution [].


Theorem T_proof :
	hasTableau OuterSkolemization {{  translate_EForm (ENeg T) }} subst.
Proof.
exists \{\}, \{\}.
eapply hasTableauNegImp with (i := 0).
1: reflexivity.
eapply hasTableauContr with (i := 0) (j := 1).
1: reflexivity. 
1: reflexivity. 
reflexivity.
Qed.

