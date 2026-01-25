(** * Prelude.Utils: some utility functions / lemmas *)

From Tableaux Require Import Init.
From Tableaux Require Import Classes.

From Corelib Require Import Program.Wf.

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
