(** * Prelude.Init: set basic flags and Corelib/Stdlib exports *)

From Corelib Require Export ssr.ssreflect.

From Stdlib Require Export Strings.String.
From Stdlib Require Export Lists.List.

Export ListNotations.

Notation "#| l |" := (List.length l).
Notation "l .( i )" := (List.nth_error l i).

(** We freely suppose functional and product extensionnality. *)
Axiom funext :
  forall {A : Type} {B : A -> Type} {f g : forall (x : A), B x},
    (forall (x : A), f x = g x) -> f = g.

Axiom prodext :
  forall {A : Type} {P Q : A -> Prop},
    (forall x : A, P x = Q x) ->
    (forall x : A, P x) = (forall x : A, Q x).

(** ** Rocq's default behaviour *)

(** Make the usage of bullets mandatory. *)
#[export] Set Default Goal Selector "!".

(** Remove indexes of constructor in pattern matches. *)
#[export] Set Asymmetric Patterns.

(** Simplify some proofs by avoiding [unfold]s using [Declare Equivalent Keys]. *)
#[export] Set Keyed Unification.

(** We always want our records to have primitive projections. *)
#[export] Set Primitive Projections.

(** Automatically declare the implicit arguments. *)
#[export] Set Strongly Strict Implicit.
#[export] Set Maximal Implicit Insertion.

(** Make contextual implicit arguments be implicit. *)
#[export] Set Contextual Implicit.

(** Makes typeclasses search fail instead of loop infinitely. *)
#[export] Set Typeclasses Depth 1000.
