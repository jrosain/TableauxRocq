
From Tableaux Require Import All.

Import ATPCompat.

Definition Axiom0 : EForm :=
	EPred "a" [] 
.

Definition T : EForm :=
	EPred "a" [] 
.

Definition subst := translate_substitution [].


Theorem T_proof :
	hasTableau OuterSkolemization {{ translate_EForm (Axiom0) ;;  translate_EForm (ENeg T) }} subst.
Proof.
exists \{\}, \{\}.
eapply hasTableauContr with (i := 1) (j := 0).
1: reflexivity. 
1: reflexivity. 
reflexivity.
Qed.

