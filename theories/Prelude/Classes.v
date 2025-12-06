(** * Prelude.Classes: definition of common typeclasses *)

From Tableaux Require Import Prelude.Init.

From Corelib Require Export Classes.RelationClasses.

(** ** Typeclasses definition *)

Class EqDec (A : Type) :=
  eqDec : forall x y : A, { x = y } + { x <> y }.
Notation "x == y" := (eqDec x y) (at level 40).

Lemma EqDec_UIP :
  forall {A : Type} `{EqDec A} {x y : A} (p q : x = y), p = q.
Proof.
  intros.
  set g := fun x y (p : x = y) => match eqDec x y with
    | left e => e
    | right n => False_ind (x = y) (n p)
    end.
  have H0 : forall (p : x = y), p = eq_trans (eq_sym (g x x eq_refl)) (g x y p).
  { clear; intros; destruct p. symmetry.
    apply eq_trans_sym_inv_l. }
  rewrite (H0 p) (H0 q).
  unfold g; now destruct (eqDec x y).
Qed.

Lemma EqDec_refl :
  forall {A : Type} `{EqDec A} (x : A), x == x = left eq_refl.
Proof.
  intros ???. destruct (eqDec x x).
  - f_equal. apply EqDec_UIP.
  - destruct n. reflexivity.
Qed.

Class EqBool (A : Type) :=
  { eqb : A -> A -> bool
  ; eqbIsEq : forall (x y : A), eqb x y = true <-> x = y }.

(** ** Generic instances *)

Section EqDecOtherInstances.
  Context {A : Type} `{EqDec A}.

  #[global] Instance eq_dec_list : EqDec (list A).
  Proof using H.
    intros xs; induction xs as [| x xs IHxs]; intro ys; destruct ys as [|y ys].
    2,3: right; intro e; inversion e.
    - now left.
    - destruct (x == y).
      2: right; intro e; injection e => e0 e1; now apply n.
      destruct (IHxs ys).
      + left; now rewrite e e0.
      + right; intro e'; injection e' => e0 e1; now apply n.
  Qed.
End EqDecOtherInstances.

Section EquivEqBoolEqDec.
  Context (A : Type).

  #[global] Instance eq_dec_from_eq_bool `{EqBool A} : EqDec A.
  Proof using Type.
    intros ??. destruct (eqb x y) eqn:e.
    + left. now apply eqbIsEq in e.
    + right. intro e'.
      have e0 : ~(eqb x y = true).
      { intro e0. rewrite e in e0. inversion e0. }
      rewrite eqbIsEq in e0. now apply e0.
  Qed.

  #[global] Instance eq_bool_from_eq_dec `{EqDec A} : EqBool A.
  Proof using Type.
    unshelve econstructor; intros x y.
    - exact (match x == y with
             | left _ => true
             | right _ => false
             end).
    - cbn; destruct (x == y); split; auto.
      intro contra; inversion contra.
  Qed.
End EquivEqBoolEqDec.

(** ** Common instances *)

#[global] Instance eq_dec_nat : EqDec nat.
Proof.
  intros x; induction x as [|n IHn]; destruct y as [|m].
  2,3: right; intro contra; inversion contra.
  - now left.
  - destruct (IHn m) as [e | ne].
    + left; now f_equal.
    + right; intro e. injection e => contra. now apply ne.
Qed.

#[global] Instance eq_dec_string : EqDec string.
Proof.
  apply eq_dec_from_eq_bool; unshelve econstructor.
  - exact String.eqb.
  - apply String.eqb_eq.
Qed.
