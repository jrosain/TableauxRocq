
From Tableaux Require Import All.

Import ATPCompat.

Definition Axiom0 : EForm :=
	EPred "p" [(EFun "a" [])] 
.

Definition T : EForm :=
	EEx "X4" (EPred "p" [(EVar "X4")]) 
.

Definition subst := translate_substitution [("X4_8", (EFun "a" []))].


Theorem T_proof :
	hasTableau OuterSkolemization {{ translate_EForm (Axiom0) ;;  translate_EForm (ENeg T) }} subst.
Proof.
exists \{ "X4_8" \}, \{\}.
unshelve eapply hasTableauNegEx with (i := 0).
1-3: shelve.
1: exact "X4_8".
1: reflexivity.
1: now native_compute.
1: reflexivity.
1: now native_compute.
1: now native_compute.
eapply hasTableauContr with (i := 3) (j := 0).
1: reflexivity. 
1: reflexivity. 
reflexivity.
Qed.

