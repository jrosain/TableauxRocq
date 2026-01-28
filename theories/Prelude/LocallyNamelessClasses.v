(** * Prelude.LocallyNamelessClasses: classes for locally nameless representation *)

From Tableaux Require Import Init.
From Tableaux Require Import Sets.
From Tableaux Require Import Atoms.

(** This file mainly defines the different classes (and also notations) for manipulating
    variables in a locally nameless representation. In particular, it defines a typeclass
    for:
    - variable opening (i.e., instantiating a variable by a term),
    - getting the bound variables of a term,
    - substitution in a locally nameless environment *)

(** ** Variable opening: replacing a bound variable with an atom *)
Class Opening (A B : Type) :=
  varOpening : nat -> A -> B -> B.
Arguments varOpening {_ _ _} _ _ _.
Notation "t { n \to x }" := (varOpening n x t) (at level 3).

(** ** Variable substitution: replacing a free variable with something *)
Section Substitution.
  Context `{set_nat : set nat}.

  Class BV (A : Type) :=
    bv : A -> set_nat.
  Arguments bv {_ _}.

  Definition isLocallyClosed {A : Type} `{BV A} (x : A) :=
    is_empty (bv x).

  Class Substitution (X : Atom) (A : Type) `{BV A} :=
    { subst :> X -> A
    ; isSubst : forall (x : X), isLocallyClosed (subst x) }.

  Class Subst {X : Atom} (A B : Type) `{BV B} :=
    substitute : A -> Substitution X B -> A.
  Arguments substitute {_ _ _ _ _} _ _.
End Substitution.

Notation "x @[ sigma ]" := (substitute x sigma) (at level 3).

(** ** Further free instances of [BV]. *)
Section BVInstances.
  Context `{set_nat : set nat}.

  #[global] Instance bv_list {A : Type} `{H : @BV set_nat A} : @BV set_nat (list A) :=
    fix F (l : list A) : set_nat :=
      match l with
      | [] => empty_set
      | h :: t => (bv h) \union F t
      end.
End BVInstances.

(** ** Further free instances of [Subst]. *)
Section SubstInstances.
  Context `{set_nat : set nat}.

  #[global] Instance subst_list {A B : Type} `{H : BV B} `{Subst A B} :
    Subst (list A) B :=
    fun xs sigma =>
      (fix F (xs : list A) : list A :=
         match xs with
         | [] => []
         | x :: xs => x@[sigma] :: F xs
         end) xs.
End SubstInstances.

(** ** Free variable and free-variable closedness *)
Section FreeVariables.
  Context {var : Atom}.

  Let set_var := set_atom var.

  Class FV (A : Type) :=
    fv : A -> set_var.

  Definition isClosed {A : Type} `{FV A} (x : A) :=
    is_empty (fv x).
End FreeVariables.

(** ** Further free instances of [FV]. *)
Section FVInstances.
  Context {var : Atom}.

  Let set_var := set_atom var.

  #[global] Instance fv_list {A : Type} `{@FV var A} : @FV var (list A) :=
    fix F (xs : list A) : set_var :=
      match xs with
      | [] => empty_set
      | x :: xs => (fv x) \union (F xs)
      end.

  Lemma fv_list_in :
    forall {A : Type} `{@FV var A} (x : A) (l : list A),
      List.In x l -> fv l = fv (x :: l).
  Proof using Type.
    intros ???? hin; induction l as [|y ys IHys]; inversion hin.
    - subst. cbn. rewrite -union_assoc union_idemp //.
    - cbn. rewrite -union_assoc.
      symmetry; etransitivity. { refine (f_equal (fun s => s \union fv ys) _). apply union_comm. }
      rewrite union_assoc. cbn in IHys. rewrite -IHys; auto.
  Qed.
End FVInstances.
