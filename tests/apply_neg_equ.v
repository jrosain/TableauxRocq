From Tableaux Require Import All.

Import ATPCompat.


Definition T : EForm :=
        EEqu (EPred "f" []) (EEqu (EPred "g" []) (EEqu (EPred "f" []) (EPred "g" []))) 
.

Definition subst := translate_substitution [].


Theorem T_proof :
        hasTableau OuterSkolemization {{  translate_EForm (ENeg T) }} subst.
Proof.
exists \{\}, \{\}.
eapply hasTableauNegEqu with (S1 := @empty_set string _) (S2 := @empty_set string _) (Sf1 := empty_record) (Sf2 := empty_record) (i := 0).
Abort.
