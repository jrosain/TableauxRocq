
From Tableaux Require Import All.

Import ATPCompat.

Definition T : EForm :=
	EAll "X3" (EOr (EPred "p" [(EVar "X3")]) (ENeg (EPred "p" [(EVar "X3")]))) 
.

Definition subst := translate_substitution [].


Theorem T_proof :
	hasTableau OuterSkolemization {{  translate_EForm (ENeg T) }} subst.
Proof.
exists \{\}, \{ "skolem@X3@0" \}.
unshelve eapply hasTableauNegAll with (sko := OuterSkolemization) (i := 0).
1-3: shelve.
1: exact ((EFun "skolem@X3@0" [])).
2, 3: reflexivity.
1: now esimpl.
1: now esimpl.
eapply hasTableauNegOr with (i := 0).
1: reflexivity. 
eapply hasTableauNegNeg with (i := 0).
1: reflexivity. 
eapply hasTableauContr with (i := 0) (j := 2).
1: reflexivity. 
1: reflexivity. 
reflexivity.
Qed.

