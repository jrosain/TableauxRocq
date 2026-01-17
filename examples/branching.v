From Tableaux Require Import All.

Import ATPCompat.

(** In this file, we give an example of a tableau proof of the following branching
    formula:
      [exists x, P x -> P a /\ P b],
    both in outer and inner Skolemization.

    We start by defining the drinker formula using the extended syntax: *)
Definition branching : EForm :=
  EEx "x" (EImp (EPred "P" [EVar "x"])
             (EAnd (EPred "P" [ EFun "a" [] ]) (EPred "P" [ EFun "b" [] ]))).

(** In the proofs (be it in outer or in inner), we create two metavariables by instantiating
    the formula twice, and replace one of them by [a] and the other one by [b].

    Here, we do not create any new skolem symbol. *)
Definition subst := translate_substitution [("X", EFun "a" []) ; ("X2", EFun "b" [])].

Theorem outer_branching_proof :
  hasTableau OuterSkolemization {{ translate_EForm (ENeg branching) }} subst.
Proof.
  (** As in the [drinker] formula, we need to give both (i) the set of free variables
      of the tableau, and (ii) the set of Skolem symbols, which will be empty here. *)
  exists \{ "X", "X2" \}, \{\}.

  (** We start by creating a new free variable *)
  eapply hasTableauNegEx with (i := 0).
  1: reflexivity.
  1: now esimpl.

  (** Then, the proof progresses as expected. *)
  eapply hasTableauNegImp with (i := 0).
  1: reflexivity.

  (** Now, we have a branching rule. Here, we have to specify more things than simply the
      index of the formula we want to use:

      - we have to give the set of metavariables of each branch.
        [S1] is the set of the left child, while [S2] is the set of the second child.
        Note that, if one of them is empty, you cannot use [\{\}] as the elaboration process
        does not understand that this is the notation for a set of strings. Instead, you should
        use [@empty_set string _].
      - we also have to give the set of skolem symbols of each branch. In outer skolemization,
        this is a set, so we could use the same [@empty_set string _], but in general, it might
        not be simply a set (e.g., in pre-inner Skolemization, where the formulas a symbol
        originate from is important). Instead, for empty set of skolemization symbols, we
        can use [empty_record]. *)
  eapply hasTableauNegAnd with (S1 := @empty_set string _) (S2 := \{ "X2" \})
                               (Sf1 := empty_record) (Sf2 := empty_record) (i := 1).
  (** The first goal is, as always, [reflexivity]. *)
  1: reflexivity.

  (** The last three goals should always be automatically solved by [now esimpl]. *)
  3: { now esimpl. }
  3: { now esimpl. }
  3: { now esimpl. }

  (** Then, we can go into the different branches. First, let's do the left one. *)
  { (** This is the branch where we have [Neg P a], hence we can directly conclude with the
        contradiction using [P x]. *)
    eapply hasTableauContr with (i := 2) (j := 0).
    1: reflexivity.
    1: reflexivity.
    reflexivity. }

  (** Next, let's do the right branch. *)
  { (** Here, we have to create another metavariable [X2] to conclude using [Neg P b].
        This is what we do with the first two rules. *)
    eapply hasTableauNegEx with (i := 7).
    1: reflexivity.
    1: now esimpl.

    eapply hasTableauNegImp with (i := 0).
    1: reflexivity.

    (** Then, we can indeed use the contradiction between [P X2] and [Neg P b]. *)
    eapply hasTableauContr with (i := 0) (j := 5).
    1: reflexivity.
    1: reflexivity.
    reflexivity. }
Qed.

(** The proof in inner Skolemization is the same, as we have no Skolem symbol here. *)
Theorem inner_branching_proof :
  hasTableau InnerSkolemization {{ translate_EForm (ENeg branching) }} subst.
Proof.
  exists \{ "X", "X2" \}, \{\}.
  eapply hasTableauNegEx with (i := 0).
  1: reflexivity.
  1: now esimpl.

  eapply hasTableauNegImp with (i := 0).
  1: reflexivity.

  eapply hasTableauNegAnd with (S1 := @empty_set string _) (S2 := \{ "X2" \})
                               (Sf1 := empty_record) (Sf2 := empty_record) (i := 1).
  1: reflexivity.
  3-5: now esimpl.
  { eapply hasTableauContr with (i := 2) (j := 0).
    1: reflexivity.
    1: reflexivity.
    reflexivity. }
  { eapply hasTableauNegEx with (i := 7).
    1: reflexivity.
    1: now esimpl.

    eapply hasTableauNegImp with (i := 0).
    1: reflexivity.

    eapply hasTableauContr with (i := 0) (j := 5).
    1: reflexivity.
    1: reflexivity.
    reflexivity. }
Qed.
