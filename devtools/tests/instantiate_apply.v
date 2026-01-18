From Tableaux Require Import All.
Import ATPCompat.
Definition T: EForm :=
  EAll "X7"
    (EImp
       (EPred "p"[(EVar "X7")])
       (EEx "Y5"(EOr (EPred "p"[(EVar "Y5")]) (EPred "q" [(EVar "Y5")])))).

Definition subst:= translate_substitution [("Y5_12", (EFun "skolem@X7@0"[]))].

Theorem T_proof:
  hasTableau OuterSkolemization {{ translate_EForm (ENeg T) }} subst.
Proof.
  exists\{ "Y5_12"\}, \{ "skolem@X7@0"\}.
  unshelve eapply hasTableauNegAll with (sko := OuterSkolemization) (i := 0).
  1, 2: shelve.
  1: exact((EFun "skolem@X7@0"[])).
  2, 3: reflexivity.
  1: { now esimpl. }
  eapply hasTableauNegImp with (i := 0).
  1: { reflexivity. }
  eapply hasTableauNegEx with(i := 1).
  1: { reflexivity. }
  1: { now esimpl. }
  eapply hasTableauNegOr with(i := 0).
  1: { reflexivity. }
  eapply hasTableauContr with(i := 4) (j := 1).
  1: { reflexivity. }
  1: { reflexivity. }
  reflexivity.
Qed.
