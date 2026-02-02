(** * Prelude.Utils: some utility functions / lemmas *)

From Tableaux Require Import Init.
From Tableaux Require Import Ind.
From Tableaux Require Import Classes.

From Stdlib Require Import FunInd.

From Stdlib Require Import Lia.
From Stdlib Require Import Numbers.DecimalString.
From Stdlib Require Import Numbers.DecimalNat.

Definition nat_to_string (n: nat) := NilZero.string_of_uint (Decimal.rev (Unsigned.to_lu n)).

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

Fixpoint forallb2 {A : Type} (P : A -> A -> bool) (l1 l2 : list A) : bool :=
  match l1, l2 with
  | [], [] => true
  | x :: xs, y :: ys => P x y && forallb2 P xs ys
  | _, _ => false
  end.

Lemma forallb2_eq :
  forall {A : Type} {P : A -> A -> bool} (l1 l2 : list A),
    (forall (x y : A), In x l1 -> P x y = true -> x = y) ->
    forallb2 P l1 l2 = true -> l1 = l2.
Proof.
  intros ???. induction l1 as [| x xs IHxs]; destruct l2 as [|y ys]; cbn in *.
  - reflexivity.
  - now intros.
  - now intros.
  - intros h (h0 & h1)%andb_prop. apply h in h0.
    2: auto. rewrite h0. apply f_equal, IHxs; auto.
Qed.

Lemma forallb2_refl :
  forall {A : Type} {P : A -> A -> bool} (l : list A),
    (forall (x : A), In x l -> P x x = true) ->
    forallb2 P l l = true.
Proof.
  intros. induction l; auto.
  cbn. rewrite Bool.andb_true_iff. split; auto.
  - apply H. now right.
  - apply IHl. intros. apply H. now left.
Qed.

Lemma eqb_list_is_eq :
  forall {A : Type} `{EqBool A} (l l' : list A),
    forallb2 eqb l l' = true <-> l = l'.
Proof.
  intros ???. induction l as [|x xs IHxs]; destruct l' as [|y ys]; cbn; try tauto.
  1,2: split; intros contra; inversion contra.
  split.
  - intros (e & IH)%andb_prop. rewrite eqbIsEq in e. rewrite e. apply f_equal.
    rewrite -IHxs //.
  - intros e. injection e => <- ->. apply andb_true_intro; split.
    + rewrite EqBool_refl //.
    + rewrite IHxs //.
Qed.

#[global] Instance eqb_list {A : Type} `{EqBool A} : EqBool (list A).
Proof.
  unshelve econstructor.
  - exact (forallb2 eqb).
  - apply eqb_list_is_eq.
Defined.

Lemma nth_error_Some' :
  forall {A : Type} (l : list A) (n : nat) (x : A),
    l.(n) = Some x -> n < #|l|.
Proof.
  intros ???? e. rewrite -nth_error_Some. intro. congruence.
Qed.

Fixpoint replace_in_list {A : Type} `{EqBool A} (x y : A) (l : list A) : list A :=
  match l with
  | [] => []
  | z :: zs =>
      (if eqb x z then y
       else z) :: replace_in_list x y zs
  end.

Fixpoint replace_nth {A : Type} (n : nat) (x : A) (l : list A) : list A :=
  match l with
  | [] => []
  | y :: ys =>
      match n with
      | 0 => x :: ys
      | S n => y :: replace_nth n x ys
      end
  end.
Functional Scheme replace_nth__ind := Induction for replace_nth Sort Prop.

Lemma get_replace_nth :
  forall {A : Type} (n : nat) (x0 x : A) (l : list A),
    l.(n) = Some x0 ->
    (replace_nth n x l).(n) = Some x.
Proof.
  intros ????? e; generalize dependent n; induction l as [|y ys IHys]; intros n e; cbn.
  - rewrite nth_error_nil in e; inversion e.
  - destruct n as [|n']; cbn in e |- *.
    + reflexivity.
    + now specialize (IHys n' e).
Qed.

Lemma In_replace_nth :
  forall {A : Type} (n : nat) (x0 x : A) (l : list A),
    l.(n) = Some x0 ->
    List.In x (replace_nth n x l).
Proof. intros; eapply nth_error_In. eapply get_replace_nth; eauto. Qed.

Lemma In_replace_nth' :
  forall {A : Type} (n m : nat) (x0 x1 : A) (l : list A),
    l.(n) = Some x0 -> n <> m ->
    List.In x0 (replace_nth m x1 l).
Proof.
  intros ?????? e ne. generalize dependent n.
  functional induction (replace_nth m x1 l) using replace_nth__ind; intros i ei ne.
  - rewrite nth_error_nil in ei; inversion ei.
  - destruct i.
    + exfalso; now apply ne.
    + cbn in ei. apply nth_error_In in ei.
      now right.
  - destruct i.
    + left; cbn in ei; injection ei => -> //.
    + cbn in ei. have ne' : i <> n0.
      { intro. apply ne. now subst. }
      specialize (IHl0 i ei ne').
      now right.
Qed.
