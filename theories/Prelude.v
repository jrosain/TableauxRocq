(** * Prelude: generic definitions and typeclasses *)

From Corelib Require Export ssr.ssreflect.

From Stdlib Require Export Strings.String.
From Stdlib Require Export Lists.List.
From Stdlib Require Import MSets.MSetAVL.
From Stdlib Require Import MSets.MSetProperties.
From Stdlib Require Import MSets.MSetFacts.
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
  - apply String.eqb_eq.
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
Class set {A : Type} :=
  { car :> Type
  ; empty_set : car
  ; mem : A -> car -> Prop
  ; add : A -> car -> car
  ; remove : A -> car -> car
  ; union : car -> car -> car
  ; inter : car -> car -> car
  ; is_empty : car -> Prop
  ; disjoint : car -> car -> Prop
  ; set_eq : car -> car -> Prop
  ; from_list : list A -> car

  ; Equivalence_eq : Equivalence set_eq
  ; is_empty_spec : forall (s : car), is_empty s <-> s = empty_set
  ; empty_unitl   : forall (s : car), (union empty_set s) = s
  ; empty_unitr   : forall (s : car), (union s empty_set) = s
  ; empty_disjointl : forall (s : car), disjoint empty_set s
  ; disjoint_sym  : forall (s1 s2 : car), disjoint s1 s2 <-> disjoint s2 s1 }.

Arguments set : clear implicits.
Arguments empty_set _ {_}.

Notation "S1 \union S2" := (union S1 S2) (at level 30).
Notation "S1 \inter S2" := (inter S1 S2) (at level 25).

Section SetProperties.
  Context {A : Type} `{set_A : set A}.

  Definition singleton (x : A) : set_A :=
    add x (empty_set A).

  Lemma empty_disjointr :
    forall (s : set_A), disjoint s (empty_set A).
  Proof using Type. intros. rewrite disjoint_sym. apply empty_disjointl. Qed.

  Lemma is_empty_spec' : is_empty (empty_set A).
  Proof using Type. rewrite is_empty_spec //. Qed.
End SetProperties.

(** *** Usual instantiations with [MSets] *)

(** Generic instantiation of our [set] from an ordered type *)
Module SetFromOrdered (X : OrderedType).
  Module SetOfX_ := MSetAVL.Make X.
  Module SetOfXProps := WPropertiesOn X SetOfX_.
  Module SetOfXOrdProps := MSetProperties.OrdProperties SetOfX_.
  Module SetOfXFacts := WFactsOn X SetOfX_.

  (** Here, we assume that the proofs of sets being sets are irrelevant. *)
  Axiom Ok_irrelevant : forall (s : SetOfX_.Raw.tree) (e1 e2 : SetOfX_.Raw.Ok s), e1 = e2.

  #[local] Lemma SetOfX__eq :
    forall (s1 s2 : SetOfX_.t),
      SetOfX_.this s1 = SetOfX_.this s2 ->
      s1 = s2.
  Proof.
    intros [] [] e. cbn in *. destruct e. f_equal.
    apply Ok_irrelevant.
  Qed.

  #[local] Lemma set_empty_unitl :
    forall (s : SetOfX_.t), SetOfX_.union SetOfX_.empty s = s.
  Proof. intros []. apply SetOfX__eq; now cbn. Qed.

  #[local] Lemma set_empty_unitr :
    forall (s : SetOfX_.t), SetOfX_.union s SetOfX_.empty = s.
  Proof.
    intros []. apply SetOfX__eq; cbn.
    destruct this; reflexivity.
  Qed.

  #[local] Definition set_disjoint (s1 s2 : SetOfX_.t) :=
    SetOfX_.Empty (SetOfX_.inter s1 s2).

  #[local] Lemma set_empty_disjointl :
    forall (s : SetOfX_.t), set_disjoint SetOfX_.empty s.
  Proof.
    intro; unfold set_disjoint.
    have H := @SetOfXProps.inter_subset_1 SetOfX_.empty s.
    apply SetOfXProps.empty_is_empty_2. split.
    + intro; now apply H.
    + apply SetOfXProps.subset_empty.
  Qed.

  #[local] Lemma set_disjoint_sym :
    forall (s1 s2 : SetOfX_.t), set_disjoint s1 s2 <-> set_disjoint s2 s1.
  Proof.
    intros ??; unfold set_disjoint; split.
    - intro. apply SetOfXOrdProps.P.empty_is_empty_1 in H.
      apply SetOfXOrdProps.P.empty_is_empty_2.
      rewrite SetOfXOrdProps.P.inter_sym //.
    - intro. apply SetOfXOrdProps.P.empty_is_empty_1 in H.
      apply SetOfXOrdProps.P.empty_is_empty_2.
      rewrite SetOfXOrdProps.P.inter_sym //.
  Qed.

  #[local] Lemma set_is_empty_spec :
    forall (s : SetOfX_.t), SetOfX_.Empty s <-> s = SetOfX_.empty.
  Proof.
    intros s; split.
    - unfold SetOfX_.Empty; intro. apply SetOfX__eq.
      destruct s; cbn. induction this.
      + reflexivity.
      + specialize (H t0). exfalso. apply H.
        now constructor.
    - intros ->. apply SetOfX_.empty_spec.
  Qed.

  #[global] Instance set_of_ordered : set X.t :=
  {| car := SetOfX_.t
  ;  empty_set := SetOfX_.empty
  ;  mem := SetOfX_.In
  ;  add := SetOfX_.add
  ;  remove := SetOfX_.remove
  ;  union := SetOfX_.union
  ;  inter := SetOfX_.inter
  ;  is_empty := SetOfX_.Empty
  ;  disjoint := set_disjoint
  ;  set_eq := SetOfX_.Equal
  ;  from_list := SetOfXProps.of_list

  ;  Equivalence_eq := SetOfX_.eq_equiv
  ;  is_empty_spec := set_is_empty_spec
  ;  empty_unitl := set_empty_unitl
  ;  empty_unitr := set_empty_unitr
  ;  empty_disjointl := set_empty_disjointl
  ;  disjoint_sym  := set_disjoint_sym |}.

  Definition proper_empty : Proper (set_eq ==> iff) is_empty := SetOfXOrdProps.P.FM.Empty_m.
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
  Definition lt :=
    fix rec (s1 s2 : string) : Prop :=
      match s1, s2 with
      | EmptyString, EmptyString => False
      | EmptyString, String _ _ => True
      | String _ _ , EmptyString => False
      | String c1 s1', String c2 s2' =>
          BinNat.N.lt (Ascii.N_of_ascii c1) (Ascii.N_of_ascii c2) \/ (c1 = c2 /\ rec s1' s2')
      end.
  Lemma lt_strorder : StrictOrder lt.
  Proof.
    split.
    - intros? H. induction x; red in H; auto.
      destruct H. apply BinNat.N.lt_strorder in H; auto.
      destruct H as (_ & H). apply IHx, H.
    - intros x; induction x; cbn; intros; destruct y, z; auto.
      + inversion H.
      + destruct H, H0.
        * left; etransitivity; eauto.
        * destruct H0 as (e & _); left. now rewrite -e.
        * destruct H as (e & _); left; now rewrite e.
        * right; destruct H, H0. split; try congruence.
          eapply IHx; eauto.
  Qed.
  Definition lt_compat : Proper (eq ==> eq ==> iff) lt.
  Proof. intros ?? e x' y' e'. rewrite e e'. reflexivity. Defined.
  Definition compare := compare.
  Lemma compare_spec : forall (x y : t), CompareSpec (eq x y) (lt x y) (lt y x) (compare x y).
  Proof.
    intros x y. destruct (compare x y) eqn:e; constructor.
    - now apply compare_eq_iff in e.
    - generalize dependent y. induction x; intros; destruct y; cbn in *;
        try (trivial || inversion e).
      destruct (Ascii.compare a a0) eqn:ea.
      + apply Ascii.compare_eq_iff in ea. right. split; auto.
      + left. rewrite /Ascii.compare BinNat.N.compare_lt_iff // in ea.
      + inversion e.
    - generalize dependent y. induction x; intros; destruct y; cbn in *;
        try (trivial || inversion e).
      destruct (Ascii.compare a a0) eqn:ea.
      + apply Ascii.compare_eq_iff in ea. right. split; auto.
      + inversion e.
      + left. rewrite /Ascii.compare BinNat.N.compare_gt_iff // in ea.
  Qed.
  Definition eq_dec := @eqDec string _.
End OrderedString.

Module SetOfString_ := SetFromOrdered OrderedString.
Canonical Structure SetOfString := SetOfString_.set_of_ordered.

(** ** Utility functions about defined types *)

Definition option_get {A : Type} (def : A) (x : option A) : A :=
  match x with
  | None => def
  | Some x => x
  end.

Definition bind {A B : Type} (x : option A) (f : A -> option B) : option B :=
  match x with
  | Some x => f x
  | None => None
  end.

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
  ;  isFresh := fun (x : nat) (S : SetOfNat) => ~(mem x S) |}.

Canonical Structure string_atom :=
  {| atom := string
  ;  set_atom := SetOfString
  ;  eq_dec_atom := eq_dec_string
  ;  isFresh := fun (x : string) (S : SetOfString) => ~(mem x S) |}.

(** ** Classes for variables manipulation *)

(** *** Variable opening: replacing a bound variable with an atom *)
Class Opening (A B : Type) :=
  varOpening : nat -> A -> B -> B.
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
  Context {var : Atom}.

  Let set_var := set_atom var.

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
