(** * Prelude: generic definitions and typeclasses *)

From Corelib Require Export ssr.ssreflect.

From Stdlib Require Export Strings.String.
From Stdlib Require Export Lists.List.
From Stdlib Require Import MSets.MSetAVL.
From Stdlib Require Import Structures.Orders.

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

(** *** Usual instances *)

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
  - apply eqb_eq.
Qed.

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
  ; union : car -> car -> car
  ; inter : car -> car -> car
  ; is_empty : car -> Prop
  ; disjoint : car -> car -> Prop }.
Arguments car {_ _}.
Arguments empty_set _ {_}.
Arguments mem {_ _} _ _.
Arguments add {_ _} _ _.
Arguments union {_ _} _ _.
Arguments inter {_ _} _ _.
Arguments is_empty {_ _} _.
Arguments disjoint {_ _} _ _.

Definition singleton {A : Type} `{set_A : set A} (x : A) : set_A :=
  add x (empty_set A).

Notation "S1 \union S2" := (union S1 S2) (at level 30).
Notation "S1 \inter S2" := (inter S1 S2) (at level 25).

(** *** Usual instantiations with [MSets] *)

(** Generic instantiation of our [set] from an ordered type *)
Module SetFromOrdered (X : OrderedType).
  Module SetOfX_ := MSetAVL.Make X.

  #[global] Instance set_of_ordered : set X.t :=
  {| car := SetOfX_.t
  ;  empty_set := SetOfX_.empty
  ;  mem := SetOfX_.In
  ;  add := SetOfX_.add
  ;  union := SetOfX_.union
  ;  inter := SetOfX_.inter
  ;  is_empty := SetOfX_.Empty
  ;  disjoint := fun S S' => SetOfX_.Empty (SetOfX_.inter S S') |}.
End SetFromOrdered.

(** Set of natural numbers. *)
Module OrderedNat <: OrderedType.
  Definition t := nat.
  Definition eq := @eq nat.
  Definition eq_equiv := @eq_equivalence nat.
  Definition lt := lt.
  Definition lt_strorder := PeanoNat.Nat.lt_strorder.
  Definition lt_compat := PeanoNat.Nat.lt_compat.
  Definition compare := PeanoNat.Nat.compare.
  Definition compare_spec := PeanoNat.Nat.compare_spec.
  Definition eq_dec := @eqDec nat _.
End OrderedNat.

Module SetOfNat_ := SetFromOrdered OrderedNat.
Canonical Structure SetOfNat := SetOfNat_.set_of_ordered.

(** Set of strings. *)
Module OrderedString <: OrderedType.
  Definition t := string.
  Definition eq := @eq string.
  Definition eq_equiv := @eq_equivalence string.
  Definition lt := fun s1 s2 => compare s1 s2 = Lt.
  Definition lt_strorder : StrictOrder lt. Admitted.
  Definition lt_compat : Proper (eq ==> eq ==> iff) lt. Admitted.
  Definition compare := compare.
  Definition compare_spec : forall (x y : t), CompareSpec (eq x y) (lt x y) (lt y x) (compare x y). Admitted.
  Definition eq_dec := @eqDec string _.
End OrderedString.

Module SetOfString_ := SetFromOrdered OrderedString.
Canonical Structure SetOfString := SetOfString_.set_of_ordered.

(** ** Atoms: the class of bound/free variables *)

Class Atom :=
  { atom :> Type
  ; set_atom : set atom
  ; eq_dec_atom : EqDec atom
  ; isFresh : atom -> set_atom -> Prop }.
Arguments set_atom : clear implicits.

(** *** Usual instantiations. *)

Canonical Structure nat_atom :=
  {| atom := nat
  ;  set_atom := SetOfNat
  ;  eq_dec_atom := eq_dec_nat
  ;  isFresh := fun x S => ~(mem x S) |}.

Canonical Structure string_atom :=
  {| atom := string
  ;  set_atom := SetOfString
  ;  eq_dec_atom := eq_dec_string
  ;  isFresh := fun x S => ~(mem x S) |}.

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
    isLocallyClosed : is_empty (bv x).
  Arguments isLocallyClosed {_} _ _.

  Class Substitution (X : Atom) (A : Type) `{BV A} :=
    { subst :> X -> A
    ; isSubst : forall (x : X), LocallyClosed (subst x) }.

  Class Subst {X : Atom} (A B : Type) `{BV B} :=
    substitute : A -> Substitution X B -> A.
  Arguments substitute {_ _ _ _ _} _ _.

  (** *** Furhter instantiations of [Subst] based on previous ones *)
  #[global] Instance subst_list {X : Atom} {A B : Type} `{H : BV B} `{@Subst X A B H} :
    @Subst X (list A) B H :=
    fun xs sigma =>
      (fix F (xs : list A) : list A :=
         match xs with
         | [] => []
         | x :: xs => substitute x sigma :: F xs
         end) xs.
End HasSetNat.

Notation "x @[ sigma ]" := (substitute x sigma) (at level 3).

(** *** Free variables and closedness *)
Section FreeVariables.
  Context {var : Atom} `{set_var : set var}.

  Class FV (A : Type) :=
    fv : A -> set_var.

  Class Closed {A : Type} `{FV A} (x : A) :=
    isClosed : is_empty (fv x).

  (** *** Furhter instantiations of [FV] based on previous ones *)
  #[global] Instance fv_list {A : Type} `{FV A} : FV (list A) :=
    fix F (xs : list A) : set_var :=
      match xs with
      | [] => empty_set var
      | x :: xs => (fv x) \union (F xs)
      end.
End FreeVariables.
