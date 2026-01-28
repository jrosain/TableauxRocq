From Tableaux Require Import All.

Import ATPCompat.

Definition Axiom0 : EForm :=
  EAll "X6" (EEx "Y4" (EPred "p" [(EVar "X6") ; (EVar "Y4")])).

Definition T : EForm :=
  EAll "X10" (EEx "Y8" (EPred "p" [(EVar "X10") ; (EVar "Y8")])).

Definition subst :=
  translate_substitution
    [("Y8_17", (EFun "skolem@Y4@1" [(EFun "skolem@X10@0" [])])); ("X6_13", (EFun "skolem@X10@0" []))].

Theorem T_proof :
  hasTableau OuterSkolemization {{ translate_EForm (Axiom0) ;; translate_EForm (ENeg T) }} subst.
Proof.
  exists \{ "X6_13" , "Y8_17" \}, \{ "skolem@X10@0", "skolem@Y4@1" \}.
  unshelve eapply hasTableauNegAll with (sko := OuterSkolemization) (i := 0).
  1-3: shelve.
  1: exact ((EFun "skolem@X10@0" [])).
  2, 3: reflexivity.
  1: { now native_compute. }
  1: { now native_compute. }
  1: now cbn.
  unshelve eapply hasTableauAll with (i := 2).
  1-3: shelve.
  1: exact "X6_13".
  1: { reflexivity. }
  1: { now native_compute. }
  1: { reflexivity. }
  1: { now native_compute. }
  1: { now native_compute. }
  unshelve eapply hasTableauEx with (sko := OuterSkolemization) (i := 0).
  1-3: shelve.
  1: exact ((EFun "skolem@Y4@1" [(EVar "X6_13")])).
  2, 3: reflexivity.
  1: { now native_compute. }
  1: { now native_compute. }
  1: now cbn.
  unshelve eapply hasTableauNegEx with (i := 3).
  1-3: shelve.
  1: exact "Y8_17".
  1: { reflexivity. }
  1: { now native_compute. }
  1: { reflexivity. }
  1: { now native_compute. }
  1: { now native_compute. }
  eapply hasTableauContr with (i := 2) (j := 0).
  1: { reflexivity. }
  1: { reflexivity. }
  reflexivity.
Qed.
