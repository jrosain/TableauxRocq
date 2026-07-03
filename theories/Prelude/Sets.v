(** * Prelude.Sets: an effective axiomatization of sets *)

From Tableaux Require Import Prelude.Init.
From Tableaux Require Import Prelude.Classes.

From Stdlib Require Import Bool.Bool.

Create HintDb set_db.

(** ** Axiomatization of sets as a typeclass *)
Class set {A : Type} :=
  { car :> Type

  ; set_eqb :: EqBool car

  (** *** Basic set operations *)
  ; empty_set : car
  ; mem : A -> car -> bool       (** Use [mem] in definitions to compute *)
  ; set_in : A -> car -> Prop    (** Use [mem_spec] to convert [mem] to [set_in] in proofs *)
  ; union : car -> car -> car
  ; inter : car -> car -> car
  ; diff  : car -> car -> car
  ; singleton : A -> car
  ; subsetb : car -> car -> bool

  (** *** Extensionality property of sets *)
  ; set_ext : forall (s1 s2 : car), s1 = s2 <-> (forall (x : A), set_in x s1 <-> set_in x s2)

  (** *** Properties of defined operations *)
  ; set_in_dec : forall (x : A) (s : car), set_in x s \/ ~set_in x s
  ; empty_spec : forall (x : A), set_in x empty_set -> False
  ; mem_spec : forall (x : A) (s : car), mem x s = true <-> set_in x s
  ; singleton_spec : forall (x y : A), set_in x (singleton y) <-> x = y
  ; union_spec : forall (x : A) (s1 s2 : car), set_in x (union s1 s2) <-> set_in x s1 \/ set_in x s2
  ; inter_spec : forall (x : A) (s1 s2 : car), set_in x (inter s1 s2) <-> set_in x s1 /\ set_in x s2
  ; diff_spec  : forall (x : A) (s1 s2 : car), set_in x (diff s1 s2) <-> set_in x s1 /\ ~ set_in x s2
  ; subsetb_spec  : forall (s1 s2 : car),
      subsetb s1 s2 = true <-> (forall (x : A), set_in x s1 -> set_in x s2)
  }.
Arguments set : clear implicits.

Notation "S1 \union S2" := (union S1 S2) (at level 30).
Notation "S1 \inter S2" := (inter S1 S2) (at level 25).

Section SetProperties.
  Context {A : Type} `{set_A : set A}.

  Lemma carrier_eq_dec :
    forall (x y : A), x = y \/ x <> y.
  Proof using set_A.
    intros. destruct (singleton x == singleton y) as [e | n].
    - rewrite set_ext in e. specialize (e x).
      destruct e as (h & _).
      have hin : set_in x (singleton x) by now rewrite singleton_spec.
      specialize (h hin). rewrite singleton_spec in h. now left.
    - rewrite set_ext in n. right. intro e.
      apply n. intro z. subst. tauto.
  Qed.

  Definition add (x : A) (s : set_A) : set_A :=
    union (singleton x) s.

  Lemma add_spec1 :
    forall (x : A) (s : set_A),
      set_in x (add x s).
  Proof using Type.
    intros x s; unfold add. rewrite union_spec. left. rewrite singleton_spec. reflexivity.
  Qed.

  Lemma add_spec2 :
    forall (x y : A) (s : set_A),
      set_in x s -> set_in x (add y s).
  Proof using Type.
    intros x y s hin; unfold add. rewrite union_spec. now right.
  Qed.

  Lemma add_inv :
    forall (x y : A) (s : set_A),
      set_in x (add y s) -> x = y \/ set_in x s.
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

  Definition rem (x : A) (s : set_A) : set_A :=
    diff s (singleton x).

  Lemma rem_spec1 :
    forall (x : A) (s : set_A),
      ~ set_in x (rem x s).
  Proof using Type.
    intros ?? hin; unfold rem in hin.
    rewrite diff_spec in hin. destruct hin as (_ & h). apply h.
    now apply singleton_spec.
  Qed.

  Lemma rem_spec2 :
    forall (x y : A) (s : set_A),
      set_in y (rem x s) -> set_in y s.
  Proof using Type.
    intros ??? h. unfold rem in h.
    rewrite diff_spec in h. now destruct h as [hin _].
  Qed.

  Lemma rem_spec3 :
    forall (x y : A) (s : set_A),
      x <> y -> set_in y s -> set_in y (rem x s).
  Proof using Type.
    intros ??? n e. unfold rem. rewrite diff_spec.
    split; auto. intro contra. apply n.
    now rewrite singleton_spec in contra.
  Qed.

  Lemma add_rem :
    forall (x : A) (s : set_A),
      set_in x s -> add x (rem x s) = s.
  Proof using Type.
    intros. apply set_ext; intro y; split; intro h.
    - apply add_inv in h. destruct h as [e | h]; subst; auto.
      eapply rem_spec2; eauto.
    - unfold add. rewrite union_spec.
      destruct (carrier_eq_dec x y) as [e | n].
      + left. rewrite e. now rewrite singleton_spec.
      + right. eapply rem_spec3; eauto.
  Qed.

  Definition subset (s1 s2 : set_A) :=
    forall (x : A), set_in x s1 -> set_in x s2.

  #[global] Instance reflexive_subset : Reflexive subset.
  Proof using Type. intro. unfold subset. tauto. Qed.

  #[global] Instance transitive_subset : Transitive subset.
  Proof using Type. intros???. unfold subset. firstorder. Qed.

  #[global] Instance antisym_subset : Antisymmetric set_A eq subset.
  Proof using Type. intros ????. apply set_ext; intros; split; firstorder. Qed.

  Definition is_empty (s : set_A) := s = empty_set.

  Lemma is_empty_spec :
    forall (x : A) (s : set_A),
      is_empty s -> set_in x s -> False.
  Proof using Type. intros ?? e. rewrite e. apply empty_spec. Qed.

  Lemma empty_is_empty :
    is_empty empty_set.
  Proof using Type. reflexivity. Qed.

  Lemma is_empty_spec' :
    forall (s : set_A),
      (forall (x : A), set_in x s -> False) -> is_empty s.
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

  Lemma is_empty_union :
    forall (s1 s2 : set_A), is_empty s1 /\ is_empty s2 -> is_empty (s1 \union s2).
  Proof using Type.
    intros ?? (empty1 & empty2). apply is_empty_spec'.
    intros x hin. rewrite union_spec in hin. destruct hin.
    - eapply is_empty_spec in empty1; eauto.
    - eapply is_empty_spec in empty2; eauto.
  Qed.

  Lemma union_congl :
    forall (s1 s2 s3 : set_A), s1 = s2 -> s3 \union s1 = s3 \union s2.
  Proof using Type. intros. now apply f_equal. Qed.

  Lemma union_congr :
    forall (s1 s2 s3 : set_A), s1 = s2 -> s1 \union s3 = s2 \union s3.
  Proof using Type. intros. now apply (f_equal (fun s => s \union s3)). Qed.

  Fixpoint from_list (l : list A) : set_A :=
    match l with
    | [] => empty_set
    | h :: t => add h (from_list t)
    end.

  Lemma mem_unionl :
    forall (x : A) (s1 s2 : set_A),
      set_in x s1 -> set_in x (union s1 s2).
  Proof using Type. intros. rewrite union_spec. now left. Qed.

  Lemma mem_unionr :
    forall (x : A) (s1 s2 : set_A),
      set_in x s2 -> set_in x (union s1 s2).
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
  Hint Rewrite empty_unitl empty_unitr union_idemp union_assoc : set_db.

  Lemma union_comm :
    forall (s1 s2 : set_A),
      union s1 s2 = union s2 s1.
  Proof using Type.
    intros; apply set_ext; intro; split; intro hin; rewrite !union_spec in hin |- *;
      destruct hin as [hin | hin]; auto.
  Qed.

  Lemma inter_sym :
    forall (s1 s2 : set_A), inter s1 s2 = inter s2 s1.
  Proof using Type.
    intros s1 s2; apply set_ext; intros; split; intro hin; rewrite !inter_spec in hin |- *;
      firstorder.
  Qed.

  Definition disjoint (s1 s2 : set_A) := Classes.eqb (s1 \inter s2) empty_set.
  Definition are_disjoint (s1 s2 : set_A) := s1 \inter s2 = empty_set.
  Hint Unfold are_disjoint : set_db.

  Lemma disjoint_are_disjoint :
    forall (s1 s2 : set_A),
      disjoint s1 s2 = true <-> are_disjoint s1 s2.
  Proof using Type.
    intros. transitivity (forall (x : A), set_in x (s1 \inter s2) <-> set_in x empty_set).
    - rewrite eqbIsEq. apply set_ext.
    - symmetry. apply set_ext.
  Qed.

  Lemma empty_disjointl :
    forall (s : set_A),
      are_disjoint empty_set s.
  Proof using Type.
    intro s. apply set_ext; intro; split; intro hin.
    - now rewrite inter_spec in hin.
    - now apply empty_spec in hin.
  Qed.

  Lemma empty_disjointr :
    forall (s : set_A),
      are_disjoint s empty_set.
  Proof using Type. intro; autounfold with set_db. rewrite inter_sym. apply empty_disjointl. Qed.

  Lemma disjoint_sym :
    forall (s1 s2 : set_A),
      are_disjoint s1 s2 <-> are_disjoint s2 s1.
  Proof using Type.
    intros s1 s2; autounfold with set_db. split; intro e;
      now rewrite inter_sym.
  Qed.

  Lemma set_fold_left :
    forall {B : Type} (f : B -> set_A) (l : list B) (s : set_A),
      (fold_left (fun (s : set_A) (b : B) => union s (f b)) l s) =
        s \union (fold_left (fun (s : set_A) (b : B) => union s (f b)) l empty_set).
  Proof using Type.
    intros???; induction l as [|y ys IHys]; intros; cbn in *; autorewrite with set_db.
    - reflexivity.
    - rewrite IHys; cbn.
      have e0 : fold_left (fun (s0 : set_A) (b : B) => s0 \union f b) ys (f y) =
                  (f y) \union fold_left (fun (s0 : set_A) (b : B) => s0 \union f b) ys empty_set.
      { apply IHys. }
      rewrite e0 union_assoc //.
  Qed.

  Lemma mem_spec' :
    forall (x : A) (s : set_A), mem x s = false <-> ~(set_in x s).
  Proof using Type.
    intros x s; split; intro h.
    - intro hin. rewrite -mem_spec in hin. rewrite hin in h. inversion h.
    - apply not_true_is_false. intro e. apply h. rewrite -mem_spec //.
  Qed.
End SetProperties.
Hint Rewrite @empty_unitl @empty_unitr @union_idemp @union_assoc : set_db.
Hint Unfold are_disjoint : set_db.

(** We denote [\{ x, y, ..., z \}] for finite sets *)
Notation "\{ \}" := empty_set.
Notation "\{ x \}" := (add x \{\}).
Notation "\{ x , y , .. , z \}" := (add x (add y .. (add z \{\}) ..)).
Notation "S1 \subseteq S2" := (subset S1 S2) (at level 40).

(** For builtin instances, see the file [SetInstances.v]. *)
