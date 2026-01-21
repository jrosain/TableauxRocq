
From Tableaux Require Import All.

Import ATPCompat.

Definition T : EForm :=
	ENeg (EBot) 
.

Definition subst := translate_substitution [].


Theorem T_proof :
	hasTableau OuterSkolemization {{  translate_EForm (ENeg T) }} subst.
Proof.
exists \{\}, \{\}.
eapply hasTableauNegNeg with (i := 0).
1: reflexivity. 
eapply hasTableauBot with (i := 0).
reflexivity.
Qed.

