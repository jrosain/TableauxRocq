(** * Prelude.Init: set basic flags and Corelib/Stdlib exports *)

From Corelib Require Export ssr.ssreflect.

From Stdlib Require Export Strings.String.
From Stdlib Require Export Lists.List.

Export ListNotations.
Open Scope string_scope.

Notation "#| l |" := (List.length l).

Axiom prodext :
  forall {A : Type} {P Q : A -> Prop},
    (forall x : A, P x = Q x) ->
    (forall x : A, P x) = (forall x : A, Q x).
