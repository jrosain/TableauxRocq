
From Tableaux Require Import All.

Import ATPCompat.

Definition T : EForm :=
	ENeg (EAll "X3" (EAnd (EPred "p" [(EVar "X3")]) (ENeg (EPred "p" [(EVar "X3")])))) 
.

Definition subst := translate_substitution [].


Theorem T_proof :
	hasTableau OuterSkolemization {{  translate_EForm (ENeg T) }} subst.
Proof.
exists \{ "X3_5" \}, \{\}.
eapply hasTableauNegNeg with (i := 0).
1: reflexivity. 
unshelve eapply hasTableauAll with (i := 0).
1-3: shelve.
1: exact "X3_5".
1: reflexivity.
1: now esimpl.
1: reflexivity.
1: now esimpl.
eapply hasTableauAnd with (i := 0).
1: reflexivity. 
eapply hasTableauContr with (i := 1) (j := 0).
1: reflexivity. 
1: reflexivity. 
reflexivity.
Qed.

