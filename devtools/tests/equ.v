
From Tableaux Require Import All.

Import ATPCompat.

Definition T : EForm :=
	ENeg (EEqu (ETop) (EBot)) 
.

Definition subst := translate_substitution [].


Theorem T_proof :
	hasTableau OuterSkolemization {{  translate_EForm (ENeg T) }} subst.
Proof.
exists \{\}, \{\}.
eapply hasTableauNegNeg with (i := 0).
1: reflexivity. 
eapply hasTableauEqu with (S1 := @empty_set string _) (S2 := @empty_set string _) (Sf1 := empty_record) (Sf2 := empty_record) (i := 0).
1: reflexivity.
3: now native_compute.
3: now native_compute.
3: now native_compute.
{
eapply hasTableauNegTop with (i := 1).
reflexivity.
}
{
eapply hasTableauBot with (i := 1).
reflexivity.
}
Qed.

