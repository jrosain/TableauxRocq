(** * Prelude.Sets: an effective axiomatization of sets and some instances *)

From Tableaux Require Import Prelude.Init.
From Tableaux Require Import Prelude.Classes.

From Stdlib Require Import MSets.MSetAVL.
From Stdlib Require Import MSets.MSetProperties.
From Stdlib Require Import MSets.MSetFacts.
From Stdlib Require Import MSets.MSetDecide.

(** ** Axiomatization of sets as a typeclass *)
Class set {A : Type} :=
  { car :> Type

  (** *** Basic set operations *)
  ; empty_set : car
  ; mem : A -> car -> Prop
  ; union : car -> car -> car
  ; inter : car -> car -> car
  ; singleton : A -> car

  (** *** Extensionality property of sets *)
  ; set_ext : forall (s1 s2 : car), s1 = s2 <-> (forall (x : A), mem x s1 <-> mem x s2)

  (** *** Properties of defined operations *)
  ; empty_spec : forall (x : A), mem x empty_set -> False
  ; singleton_spec : forall (x y : A), mem x (singleton y) <-> x = y
  ; union_spec : forall (x : A) (s1 s2 : car), mem x (union s1 s2) <-> mem x s1 \/ mem x s2
  ; inter_spec : forall (x : A) (s1 s2 : car), mem x (inter s1 s2) <-> mem x s1 /\ mem x s2 }.
Arguments set : clear implicits.

Notation "S1 \union S2" := (union S1 S2) (at level 30).
Notation "S1 \inter S2" := (inter S1 S2) (at level 25).

Section SetProperties.
  Context {A : Type} `{set_A : set A}.

  Definition add (x : A) (s : set_A) : set_A :=
    union (singleton x) s.

  Lemma add_spec1 :
    forall (x : A) (s : set_A),
      mem x (add x s).
  Proof using Type.
    intros x s; unfold add. rewrite union_spec. left. rewrite singleton_spec. reflexivity.
  Qed.

  Lemma add_spec2 :
    forall (x y : A) (s : set_A),
      mem x s -> mem x (add y s).
  Proof using Type.
    intros x y s hin; unfold add. rewrite union_spec. now right.
  Qed.

  Lemma add_inv :
    forall (x y : A) (s : set_A),
      mem x (add y s) -> x = y \/ mem x s.
  Proof using Type.
    intros ??? hin. rewrite /add union_spec in hin. destruct hin as [hin | hin].
    - rewrite singleton_spec in hin. now left.
    - now right.
  Qed.

  Lemma singleton_spec1 :
    forall (x : A), singleton x = add x empty_set.
  Proof using Type.
    intros x; apply set_ext; intro y; split; intro hin.
    - apply singleton_spec in hin. rewrite hin. apply add_spec1.
    - apply add_inv in hin. destruct hin.
      + rewrite H. now apply singleton_spec.
      + now apply empty_spec in H.
  Qed.

  Definition subset (s1 s2 : set_A) :=
    forall (x : A), mem x s1 -> mem x s2.

  #[global] Instance reflexive_subset : Reflexive subset.
  Proof using Type. intro. unfold subset. tauto. Qed.

  #[global] Instance transitive_subset : Transitive subset.
  Proof using Type. intros???. unfold subset. firstorder. Qed.

  #[global] Instance antisym_subset : Antisymmetric set_A eq subset.
  Proof using Type. intros ????. apply set_ext; intros; split; firstorder. Qed.

  Definition is_empty (s : set_A) := s = empty_set.

  Lemma is_empty_spec :
    forall (x : A) (s : set_A),
      is_empty s -> mem x s -> False.
  Proof using Type. intros ?? e. rewrite e. apply empty_spec. Qed.

  Lemma empty_is_empty :
    is_empty empty_set.
  Proof using Type. reflexivity. Qed.

  Lemma is_empty_spec' :
    forall (s : set_A),
      (forall (x : A), mem x s -> False) -> is_empty s.
  Proof using Type.
    intros. have e : s = empty_set.
    { apply set_ext; intro y; cbn. split.
      - intro h; apply H in h. inversion h.
      - intro h. apply empty_spec in h. inversion h. }
    rewrite e. apply empty_is_empty.
  Qed.

  Lemma is_empty_union1 :
    forall (s1 s2 : set_A), is_empty (s1 \union s2) -> is_empty s1.
  Proof using Type.
    intros. apply is_empty_spec'. intros x hin.
    apply is_empty_spec with (x := x) in H; auto.
    rewrite union_spec. now left.
  Qed.

  Lemma is_empty_union2 :
    forall (s1 s2 : set_A), is_empty (s1 \union s2) -> is_empty s2.
  Proof using Type.
    intros. apply is_empty_spec'. intros x hin.
    apply is_empty_spec with (x := x) in H; auto.
    rewrite union_spec. now right.
  Qed.

  Fixpoint from_list (l : list A) : set_A :=
    match l with
    | [] => empty_set
    | h :: t => add h (from_list t)
    end.

  Lemma mem_unionl :
    forall (x : A) (s1 s2 : set_A),
      mem x s1 -> mem x (union s1 s2).
  Proof using Type. intros. rewrite union_spec. now left. Qed.

  Lemma mem_unionr :
    forall (x : A) (s1 s2 : set_A),
      mem x s2 -> mem x (union s1 s2).
  Proof using Type. intros. rewrite union_spec. now right. Qed.

  Lemma empty_unitl :
    forall (s : set_A),
      union empty_set s = s.
  Proof using Type.
    intro s. apply set_ext; intro; split; intro hin.
    - rewrite union_spec in hin. destruct hin as [contra | hin]; auto.
      now apply empty_spec in contra.
    - now apply mem_unionr.
  Qed.

  Lemma empty_unitr :
    forall (s : set_A),
      union s empty_set = s.
  Proof using Type.
    intro s. apply set_ext; intro; split; intro hin.
    - rewrite union_spec in hin. destruct hin as [hin | contra]; auto.
      now apply empty_spec in contra.
    - now apply mem_unionl.
  Qed.

  Lemma union_idemp :
    forall (s : set_A),
      union s s = s.
  Proof using Type.
    intro s; apply set_ext; intro; split; intro hin.
    - rewrite union_spec in hin. now destruct hin.
    - rewrite union_spec. now left.
  Qed.

  Lemma union_sym :
    forall (s1 s2 : set_A),
      union s1 s2 = union s2 s1.
  Proof using Type.
    intros; apply set_ext; intro; split; intro hin; rewrite !union_spec in hin |- *; destruct hin;
      firstorder.
  Qed.

  Lemma union_assoc :
    forall (s1 s2 s3 : set_A),
      union (union s1 s2) s3 = union s1 (union s2 s3).
  Proof using Type.
    intros; apply set_ext; intro; split; intro hin; rewrite !union_spec in hin |- *;
      destruct hin as [hin | hin]; try destruct hin as [hin | hin]; firstorder.
  Qed.

  Lemma inter_sym :
    forall (s1 s2 : set_A), inter s1 s2 = inter s2 s1.
  Proof using Type.
    intros s1 s2; apply set_ext; intros; split; intro hin; rewrite !inter_spec in hin |- *;
      firstorder.
  Qed.

  Definition disjoint (s1 s2 : set_A) := inter s1 s2 = empty_set.

  Lemma empty_disjointl :
    forall (s : set_A),
      disjoint empty_set s.
  Proof using Type.
    intro s. apply set_ext; intro; split; intro hin.
    - now rewrite inter_spec in hin.
    - now apply empty_spec in hin.
  Qed.

  Lemma empty_disjointr :
    forall (s : set_A),
      disjoint s empty_set.
  Proof using Type. intro; unfold disjoint. rewrite inter_sym. apply empty_disjointl. Qed.

  Lemma disjoint_sym :
    forall (s1 s2 : set_A),
      disjoint s1 s2 <-> disjoint s2 s1.
  Proof using Type.
    intros s1 s2; unfold disjoint. split; intro e;
      now rewrite inter_sym.
  Qed.

  Lemma set_fold_left :
    forall {B : Type} (f : B -> set_A) (l : list B) (s : set_A),
      (fold_left (fun (s : set_A) (b : B) => union s (f b)) l s) =
        s \union (fold_left (fun (s : set_A) (b : B) => union s (f b)) l empty_set).
  Proof using Type.
    intros???; induction l as [|y ys IHys]; intros; cbn in *.
    - now rewrite empty_unitr.
    - rewrite empty_unitl. rewrite IHys; cbn.
      have e0 : fold_left (fun (s0 : set_A) (b : B) => s0 \union f b) ys (f y) =
                  (f y) \union fold_left (fun (s0 : set_A) (b : B) => s0 \union f b) ys empty_set.
      { apply IHys. }
      rewrite e0 union_assoc //.
  Qed.

  (* TODO: rewrite it with equalities. Maybe this is the thing above? *)
  Lemma mem_fold_left_cons_unionl :
    forall {B : Type} (f : B -> set_A) (b : B) (l : list B) (x : A) (s : set_A),
      mem x (fold_left (fun (s : set_A) (b : B) => union s (f b)) (b :: l) s) <->
        mem x (union ((fold_left (fun (s : set_A) (b : B) => union s (f b)) l s)) (f b)).
  Proof.
    Admitted.
End SetProperties.

(** We denote [\{ x, y, ..., z \}] for finite sets *)
Notation "\{ \}" := empty_set.
Notation "\{ x \}" := (add x \{\}).
Notation "\{ x , y , .. , z \}" := (add x (add y .. (add z \{\}) ..)).

(** ** Built-in instances *)

(** We hide built-in instances under modules so that the user chooses whether he wants to
    import them or not. For instance, [SetComputationalInstances] will be annoying inside
    proofs, but will compute well once extracted / have a nice [decide] tactic. *)
Module SetComputationalInstances.
  Module Type SimpleOrderedType.
    Parameter t : Type.

    Parameter lt : t -> t -> Prop.
    Parameter lt_strorder : StrictOrder lt.
    Parameter lt_compat : Proper (eq ==> eq ==> iff) lt.
    Parameter compare : t -> t -> comparison.
    Parameter compare_spec : forall (x y : t), CompareSpec (x = y) (lt x y) (lt y x) (compare x y).
    Parameter eq_dec : EqDec t.
  End SimpleOrderedType.

  (** Generic instantiation of our [set] from an ordered type *)
  Module SetFromOrdered (X : SimpleOrderedType).
    Module X_ <: OrderedType.
      Definition t := X.t.
      Definition eq (x y : t) := x = y.
      Lemma eq_equiv : Equivalence eq.
      Proof. apply eq_equivalence. Qed.
      Definition lt := X.lt.
      Definition lt_strorder := X.lt_strorder.
      Definition lt_compat := X.lt_compat.
      Definition compare := X.compare.
      Definition compare_spec := X.compare_spec.
      Definition eq_dec := X.eq_dec.
    End X_.

    Module SetOfX_ := MSetAVL.Make X_.
    Module SetOfXProps := WPropertiesOn X_ SetOfX_.
    Module SetOfXOrdProps := MSetProperties.OrdProperties SetOfX_.
    Module SetOfXFacts := WFactsOn X_ SetOfX_.
    Module SetOfXDecide := WDecideOn X_ SetOfX_.

    (** Here, we assume that [SetOfX_.Equal] is equality to get the [set_ext] property of [set]s.
        We do so for simplicity sake, as this is not the thing we focus on in this formalization.
        We could instead assume relation [set_eq] inside [set] and setup everything to make
        the [rewrite] tactic work properly, and we'll probably do it in a future version of
        the library. *)
    Axiom set_equal_eq : forall (s1 s2 : SetOfX_.t), SetOfX_.Equal s1 s2 -> s1 = s2.

    Lemma set_equal_is_eq :
      forall (s1 s2 : SetOfX_.t),
        SetOfX_.Equal s1 s2 <-> s1 = s2.
    Proof.
      intros ??; split.
      - apply set_equal_eq.
      - intros []. reflexivity.
    Qed.

    Lemma SetOfX_set_ext :
      forall (s1 s2 : SetOfX_.t),
        s1 = s2 <-> (forall (x : X.t), SetOfX_.In x s1 <-> SetOfX_.In x s2).
    Proof.
      intros; split.
      - intros []; firstorder.
      - intro H. rewrite -set_equal_is_eq. apply SetOfXProps.subset_antisym.
        + intros x h. now rewrite -H.
        + intros x h. now rewrite H.
    Qed.

    Lemma SetOfX_empty_spec :
      forall (x : X.t),
        SetOfX_.In x SetOfX_.empty -> False.
    Proof. intros ? hin. now rewrite SetOfXFacts.empty_iff in hin. Qed.

    Lemma SetOfX_Empty_eq_empty :
      forall (s : SetOfX_.t),
        SetOfX_.Empty s -> s = SetOfX_.empty.
    Proof.
      intros??. apply SetOfXOrdProps.P.empty_is_empty_1 in H.
      now rewrite set_equal_is_eq in H.
    Qed.

    Lemma SetOfX_singleton_spec :
      forall (x y : X.t),
        SetOfX_.In x (SetOfX_.singleton y) <-> x = y.
    Proof.
      intros; rewrite SetOfX_.singleton_spec. reflexivity.
    Qed.

    #[global] Instance set_of_ordered : set X.t :=
      {| car := SetOfX_.t

      ;  empty_set := SetOfX_.empty
      ;  mem := SetOfX_.In
      ;  union := SetOfX_.union
      ;  inter := SetOfX_.inter
      ;  singleton := SetOfX_.singleton

      ;  set_ext := SetOfX_set_ext

      ;  empty_spec := SetOfX_empty_spec
      ;  singleton_spec := SetOfX_singleton_spec
      ;  union_spec x s1 s2 := SetOfX_.union_spec s1 s2 x
      ;  inter_spec x s1 s2 := SetOfX_.inter_spec s1 s2 x |}.
  End SetFromOrdered.

  (** Set of natural numbers. *)
  Module OrderedNat <: SimpleOrderedType.
    Definition t := nat.
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
  Module OrderedString <: SimpleOrderedType.
    Definition t := string.
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
End SetComputationalInstances.
