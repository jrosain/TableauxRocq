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
  set g := fun x y (p : x = y) => match x == y with
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

(** We set [eqb] [Opaque] for tatics used in proofs, i.e., [cbn], [simpl], etc.
    This is useful as it allows us to avoid using [change] to get [eqb], and then
    to simply rewrite with [match_eq_dec_eq_bool] to get a decidable equality and
    go on with the proof. Of course, an instance of [eqb] can still be locally set
    [Transparent] if it really needs to compute. *)
#[global] Opaque eqb.

Lemma EqBool_refl :
  forall {A : Type} `{EqBool A} (x : A), eqb x x = true.
Proof. intros. now rewrite eqbIsEq. Qed.

Lemma EqBool_neq :
  forall {A : Type} `{EqBool A} (x y : A),
    x <> y <-> eqb x y = false.
Proof.
  intros; have h0 := not_iff_compat (eqbIsEq x y).
  split; intro h.
  - rewrite -h0 in h. now apply Bool.not_true_is_false.
  - intros e; subst. rewrite EqBool_refl in h. inversion h.
Qed.

Lemma match_eq_dec_eq_bool :
  forall {A B : Type} {t u : B} `{EqDec A} `{EqBool A} {x y : A},
    match x == y with
    | left _ => t
    | right _ => u
    end = if (eqb x y) then t else u.
Proof.
  intros. destruct (eqDec x y).
  - rewrite e. now rewrite EqBool_refl.
  - rewrite EqBool_neq in n. now rewrite n.
Qed.

(** ** Equivalence *)
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

  Definition eqb_from_eqDec `{EqDec A} : A -> A -> bool :=
    (fun x y => match x == y with
             | left _ => true
             | right _ => false
             end).

  Lemma eqb_from_eqDec_is_eq `{EqDec A} (x y : A) :
    eqb_from_eqDec x y = true <-> x = y.
  Proof using Type.
    unfold eqb_from_eqDec; cbn; destruct (x == y); split; auto.
    intro contra; inversion contra.
  Qed.

  #[global] Instance eq_bool_from_eq_dec `{EqDec A} : EqBool A.
  Proof using Type.
    unshelve econstructor; intros x y.
    - exact (eqb_from_eqDec x y).
    - exact (eqb_from_eqDec_is_eq x y).
  Defined.
End EquivEqBoolEqDec.

(** ** Common instances *)

#[global] Instance eq_dec_bool : EqDec bool.
Proof using Type.
  red. intros [] []; auto.
  right; now intro.
Qed.

#[global] Instance eq_dec_nat : EqDec nat.
Proof.
  intros x; induction x as [|n IHn]; destruct y as [|m].
  2,3: right; intro contra; inversion contra.
  - now left.
  - destruct (IHn m) as [e | ne].
    + left; now f_equal.
    + right; intro e. injection e => contra. now apply ne.
Qed.

#[global] Instance eq_bool_nat : EqBool nat.
Proof.
  unshelve econstructor.
  - exact Nat.eqb.
  - apply PeanoNat.Nat.eqb_eq.
Defined.

#[global] Instance eq_bool_string : EqBool string.
Proof.
  unshelve econstructor.
  - exact String.eqb.
  - apply String.eqb_eq.
Defined.

#[global] Instance eq_dec_string : EqDec string.
Proof. apply eq_dec_from_eq_bool; exact eq_bool_string. Defined.

Fixpoint list_replace {A : Type} `{EqDec A} (l : list A) (x y : A) : list A :=
  match l with
  | [] => []
  | z :: zs =>
      (match z == x with
       | left _ => y
       | right _ => z
       end) :: list_replace zs x y
  end.

Lemma trivial_pred_is_eq_for_unit :
  forall x y : unit, (fun _ _ : unit => true) x y = true <-> x = y.
Proof. intros [] []. now split. Qed.

#[global] Instance eq_bool_unit : EqBool unit.
Proof.
  unshelve econstructor.
  - exact (fun _ _ => true).
  - apply trivial_pred_is_eq_for_unit.
Defined.

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

(** ** Monads *)

Class Monad (M : Type -> Type) :=
  { ret  : forall {A : Type}, A -> M A
  ; bind : forall {A B : Type}, M A -> (A -> M B) -> M B }.

Arguments bind {_ _ _ _}.

Notation "x >>= f" := (bind x f) (at level 20, right associativity).
