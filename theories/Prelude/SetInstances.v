(** * Prelude.SetInstances: Instances of the set typeclasses for nat and strings *)

From Tableaux Require Import Prelude.Init.
From Tableaux Require Import Prelude.Classes.
From Tableaux Require Export Prelude.Sets.

From Stdlib Require Import MSets.MSetAVL.
From Stdlib Require Import MSets.MSetProperties.
From Stdlib Require Import MSets.MSetFacts.
From Stdlib Require Import MSets.MSetDecide.

Open Scope string_scope.

Module Type SimpleOrderedType.
  Parameter t : Type.

  Parameter lt : t -> t -> Prop.
  Parameter lt_strorder : StrictOrder lt.
  Parameter lt_compat : Proper (eq ==> eq ==> iff) lt.
  Parameter compare : t -> t -> comparison.
  Parameter compare_spec : forall (x y : t), CompareSpec (x = y) (lt x y) (lt y x) (compare x y).
  Parameter eq_bool : EqBool t.
End SimpleOrderedType.

Module MSetAVLCompat (X : SimpleOrderedType).
  Existing Instance X.eq_bool.

  Module XOrd <: OrderedType.
    Definition t := X.t.
    Definition eq (x y : t) := x = y.
    Lemma eq_equiv : Equivalence eq.
    Proof. apply eq_equivalence. Qed.
    Definition lt := X.lt.
    Definition lt_strorder := X.lt_strorder.
    Definition lt_compat := X.lt_compat.
    Definition compare := X.compare.
    Definition compare_spec := X.compare_spec.
    Definition eq_dec := eq_dec_from_eq_bool X.t.
  End XOrd.

  Module XSet := MSetAVL.Make XOrd.
  Module XProps := WPropertiesOn XOrd XSet.
  Module XOrdProps := MSetProperties.OrdProperties XSet.
  Module XFacts := WFactsOn XOrd XSet.
  Module XDec := WDecideOn XOrd XSet.

  Include XSet.

  (** Here, we assume that [XSet.Equal] is equality to get the [set_ext] property of [set]s.
        We do so for simplicity sake, as this is not the thing we focus on in this formalization.
        We could instead assume relation [set_eq] inside [set] and setup everything to make
        the [rewrite] tactic work properly, and we'll probably do it in a future version of
        the library. *)
  Axiom set_equal_eq : forall (s1 s2 : XSet.t), XSet.Equal s1 s2 -> s1 = s2.

  Lemma set_equal_is_eq :
    forall (s1 s2 : XSet.t),
      XSet.Equal s1 s2 <-> s1 = s2.
  Proof.
    intros ??; split.
    - apply set_equal_eq.
    - intros []. reflexivity.
  Qed.

  Lemma ext :
    forall (s1 s2 : XSet.t),
      s1 = s2 <-> (forall (x : X.t), XSet.In x s1 <-> XSet.In x s2).
  Proof.
    intros; split.
    - intros []; firstorder.
    - intro H. rewrite -set_equal_is_eq. apply XProps.subset_antisym.
      + intros x h. now rewrite -H.
      + intros x h. now rewrite H.
  Qed.

  Lemma empty_spec' :
    forall (x : X.t),
      XSet.In x XSet.empty -> False.
  Proof. intros ? hin. now rewrite XFacts.empty_iff in hin. Qed.

  Lemma Empty_eq_empty :
    forall (s : XSet.t),
      XSet.Empty s -> s = XSet.empty.
  Proof.
    intros??. apply XOrdProps.P.empty_is_empty_1 in H.
    now rewrite set_equal_is_eq in H.
  Qed.

  Lemma singleton_spec' :
    forall (x y : X.t),
      XSet.In x (XSet.singleton y) <-> x = y.
  Proof.
    intros; rewrite XSet.singleton_spec. reflexivity.
  Qed.

  Lemma diff_spec' :
    forall (x : X.t) (s1 s2 : XSet.t),
      XSet.In x (XSet.diff s1 s2) <-> XSet.In x s1 /\ ~ XSet.In x s2.
  Proof.
    intros; split; intro H.
    - split.
      + eapply XFacts.diff_1; eauto.
      + intro contra. now apply XFacts.diff_2 in H.
    - destruct H as (hin & hnin).
      apply XFacts.diff_3; auto.
  Qed.

  Lemma equal_eq :
    forall x y : XSet.t, XSet.equal x y = true <-> x = y.
  Proof.
    intros; split.
    - intro heq. apply XFacts.equal_2 in heq. now rewrite set_equal_is_eq in heq.
    - intros []. apply XFacts.equal_1. apply XProps.equal_refl.
  Qed.

  Instance eqb : EqBool XSet.t.
  Proof.
    unshelve econstructor.
    - exact XSet.equal.
    - exact equal_eq.
  Defined.

  Lemma in_dec :
    forall (x : X.t) (s : XSet.t),
      XSet.In x s \/ ~XSet.In x s.
  Proof. apply XProps.Dec.MSetDecideAuxiliary.dec_In. Qed.

  Lemma subsetb_spec :
    forall (s1 s2 : XSet.t),
      XSet.subset s1 s2 = true <-> (forall (x : X.t), XSet.In x s1 -> XSet.In x s2).
  Proof. intros ??; rewrite XSet.subset_spec; reflexivity. Qed.
End MSetAVLCompat.

(** Set of natural numbers. *)
Module NOrd <: SimpleOrderedType.
  Definition t := nat.
  Definition lt := lt.
  Definition lt_strorder := PeanoNat.Nat.lt_strorder.
  Definition lt_compat := PeanoNat.Nat.lt_compat.
  Definition compare := PeanoNat.Nat.compare.
  Definition compare_spec := PeanoNat.Nat.compare_spec.
  Definition eq_bool : EqBool nat := ltac:(typeclasses eauto).
End NOrd.

Module NSet := MSetAVLCompat NOrd.

#[global] Instance nat_set : set nat :=
  {| car := NSet.t

  ;  set_eqb := NSet.eqb
  ;  empty_set := NSet.empty
  ;  mem := NSet.mem
  ;  set_in := NSet.In
  ;  Sets.union := NSet.union
  ;  inter := NSet.inter
  ;  diff := NSet.diff
  ;  singleton := NSet.singleton
  ;  subsetb := NSet.subset

  ;  set_ext := NSet.ext

  ;  set_in_dec := NSet.in_dec
  ;  empty_spec := NSet.empty_spec'
  ;  singleton_spec := NSet.singleton_spec'
  ;  mem_spec x s := NSet.mem_spec s x
  ;  union_spec x s1 s2 := NSet.union_spec s1 s2 x
  ;  inter_spec x s1 s2 := NSet.inter_spec s1 s2 x
  ;  diff_spec := NSet.diff_spec'
  ;  subsetb_spec := NSet.subsetb_spec |}.

(** Set of strings. *)
Module SOrd <: SimpleOrderedType.
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
      destruct H.
      + apply BinNat.N.lt_strorder in H; auto.
      + destruct H as (_ & H). apply IHx, H.
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
  Definition eq_bool : EqBool string := ltac:(typeclasses eauto).
End SOrd.

Module SSet := MSetAVLCompat SOrd.

#[global] Instance string_set : set string :=
  {| car := SSet.t

  ;  set_eqb := SSet.eqb
  ;  empty_set := SSet.empty
  ;  mem := SSet.mem
  ;  set_in := SSet.In
  ;  Sets.union := SSet.union
  ;  inter := SSet.inter
  ;  diff := SSet.diff
  ;  singleton := SSet.singleton
  ;  subsetb := SSet.subset

  ;  set_ext := SSet.ext

  ;  set_in_dec := SSet.in_dec
  ;  empty_spec := SSet.empty_spec'
  ;  singleton_spec := SSet.singleton_spec'
  ;  mem_spec x s := SSet.mem_spec s x
  ;  union_spec x s1 s2 := SSet.union_spec s1 s2 x
  ;  inter_spec x s1 s2 := SSet.inter_spec s1 s2 x
  ;  diff_spec := SSet.diff_spec'
  ;  subsetb_spec := SSet.subsetb_spec |}.
