
From Tableaux Require Import All.

Import ATPCompat.

Definition T : EForm :=
	ENeg (EEx "X3" (EAnd (EPred "p" [(EVar "X3")]) (ENeg (EPred "p" [(EVar "X3")])))) 
.

Definition subst := translate_substitution [].


Theorem T_proof :
	hasTableau OuterSkolemization {{  translate_EForm (ENeg T) }} subst.
Proof.
exists \{\}, \{ "skolem@X3@0" \}.
eapply hasTableauNegNeg with (i := 0).
1: reflexivity. 
unshelve eapply hasTableauEx with (sko := OuterSkolemization) (i := 0).
1-3: shelve.
1: exact ((EFun "skolem@X3@0" [])).
2, 3: reflexivity.
1: now native_compute.
1: now native_compute.
1: now cbn.
eapply hasTableauAnd with (i := 0).
1: reflexivity. 
eapply hasTableauContr with (i := 1) (j := 0).
1: reflexivity. 
1: reflexivity. 
reflexivity.
Qed.

