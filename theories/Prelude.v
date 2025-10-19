(** * Prelude: generic definitions and typeclasses *)

From Corelib Require Export ssr.ssreflect.

From Stdlib Require Export Strings.String.
From Stdlib Require Export Lists.List.

Export ListNotations.

(** ** Basic typeclasses *)

Class EqDec (A : Type) :=
  eqDec : forall x y : A, { x = y } + { x <> y }.
Notation "x == y" := (eqDec x y) (at level 40).

Class EqBool (A : Type) :=
  { eqb : A -> A -> bool
  ; eqbIsEq : forall (x y : A), eqb x y = true <-> x = y }.

(** *** Other instances of [EqDec] from [EqDec A] *)
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

(** *** Equivalence of [EqBool] with [EqDec]. *)
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

(** ** Basic inductives *)

Inductive Forall {A : Type} (P : A -> Type) : list A -> Type :=
| Forall_nil : Forall P []
| Forall_cons : forall (x : A) (l : list A), Forall P l -> P x -> Forall P (x :: l).

Fixpoint In {A : Type} (x : A) (l : list A) : Type :=
  match l with
  | [] => False
  | (cons y ys) => In x ys + { x = y }
  end.

(** *** Equivalence between [Forall] and [In]. *)
Section EquivForallIn.
  Context {A : Type} (P : A -> Type).

  Lemma Forall_In :
    forall (l : list A),
      Forall P l -> forall (x : A), In x l -> P x.
  Proof using Type.
    intros l H. induction H.
    - intros ? H; inversion H.
    - intros ? H'; destruct H'.
      + apply IHForall; auto.
      + now rewrite e.
  Qed.

  Lemma In_Forall :
    forall (l : list A),
      (forall (x : A), In x l -> P x) -> Forall P l.
  Proof using Type.
    intros l HIn. induction l as [|x xs IHxs].
    - apply Forall_nil.
    - apply Forall_cons.
      + apply IHxs; intros. apply HIn; auto. now left.
      + apply HIn. now right.
  Qed.
End EquivForallIn.

(** ** Axiomatized Sets *)
Class set (A : Type) :=
  { car :> Type
  ; empty_set : car
  ; mem : A -> car -> Prop
  ; add : A -> car -> car
  ; union : car -> car -> car }.
Arguments car {_ _}.
Arguments empty_set _ {_}.
Arguments mem {_ _} _ _.
Arguments add {_ _} _ _.
Arguments union {_ _} _ _.

Definition singleton {A : Type} `{set_A : set A} (x : A) : set_A :=
  add x (empty_set A).

(** ** Atoms: the class of bound/free variables *)

Class Atom :=
  { atom :> Type
  ; eq_dec_atom : EqDec atom }.

(** *** Instantiation with natural numbers. *)

#[global] Instance eq_dec_nat : EqDec nat.
Proof.
  intros x; induction x as [|n IHn]; destruct y as [|m].
  2,3: right; intro contra; inversion contra.
  - now left.
  - destruct (IHn m) as [e | ne].
    + left; now f_equal.
    + right; intro e. injection e => contra. now apply ne.
Qed.

Canonical Structure nat_atom :=
  {| atom := nat
  ;  eq_dec_atom := eq_dec_nat |}.

(** *** Instantiation with strings. *)

#[global] Instance eq_dec_string : EqDec string.
Proof.
  apply eq_dec_from_eq_bool; unshelve econstructor.
  - exact String.eqb.
  - apply eqb_eq.
Qed.

Canonical Structure string_atom :=
  {| atom := string
  ;  eq_dec_atom := eq_dec_string |}.

(** ** Classes for variables manipulation *)

(** *** Variable opening: replacing a bound variable with an atom *)
Class Opening {X : Atom} (A : Type) :=
  varOpening : nat -> X -> A -> A.
Arguments varOpening {_ _ _} _ _ _.
Notation "t { n \to x }" := (varOpening n x t) (at level 3).

(** *** Variable substitution: replacing a free variable with something *)
Section HasSetNat.
  Context `{set_nat : set nat}.

  Class BV (A : Type) :=
    bv : A -> set_nat.
  Arguments bv {_ _}.

  Class LocallyClosed {A : Type} `{BV A} (x : A) :=
    isLocallyClosed : bv x = empty_set nat.
  Arguments isLocallyClosed {_} _ _.

  Class Substitution (X : Atom) (A : Type) `{BV A} :=
    { subst :> X -> A
    ; isSubst : forall (x : X), LocallyClosed (subst x) }.

  Class Subst {X : Atom} (A B : Type) `{BV B} :=
    substitute : A -> Substitution X B -> A.
  Arguments substitute {_ _ _ _ _} _ _.
End HasSetNat.

Notation "x @[ sigma ]" := (substitute x sigma) (at level 3).

(** *** Free variables and closedness *)
Section FreeVariables.
  Context {var : Atom} `{set_var : set var}.

  Class FV (A : Type) :=
    fv : A -> set_var.

  Class Closed {A : Type} `{FV A} (x : A) :=
    isClosed : fv x = empty_set var.
End FreeVariables.
