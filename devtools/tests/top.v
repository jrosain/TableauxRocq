
From Tableaux Require Import All.

Import ATPCompat.

Definition T : EForm :=
	ETop 
.

Definition subst := translate_substitution [].


Theorem T_proof :
	hasTableau OuterSkolemization {{  translate_EForm (ENeg T) }} subst.
Proof.
exists \{\}, \{\}.
eapply hasTableauNegTop with (i := 0).
reflexivity.
Qed.

