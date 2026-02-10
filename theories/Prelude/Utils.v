(** * Prelude.Utils: some utility functions / lemmas *)

From Tableaux Require Import Init.
From Tableaux Require Import Ind.
From Tableaux Require Import Classes.

From Stdlib Require Import FunInd.

From Stdlib Require Import Lia.
From Stdlib Require Import Numbers.DecimalString.
From Stdlib Require Import Numbers.DecimalNat.

Definition nat_to_string (n: nat) := NilZero.string_of_uint (Decimal.rev (Unsigned.to_lu n)).

#[global] Instance option_Monad : Monad option :=
  {| ret := fun A x => Some x
  ;  bind := fun A B x f => match x with
                         | Some x => f x
                         | None => None
                         end |}.

Definition option_get {A : Type} (def : A) (x : option A) : A :=
  match x with
  | None => def
  | Some x => x
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

(** Comparison of lists. *)
Fixpoint lt_list {A : Type} (lt_A : A -> A -> Prop) (l l' : list A) : Prop :=
  match l, l' with
  | [], [] => False
  | [], _ :: _ => True
  | _ :: _, [] => False
  | x :: xs, y :: ys => lt_A x y \/ (x = y /\ lt_list lt_A xs ys)
  end.

Fixpoint ltb_list {A : Type} `{EqBool A} (ltb_A : A -> A -> bool) (l l' : list A) : bool :=
  match l, l' with
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | x :: xs, y :: ys => ltb_A x y || (eqb x y && ltb_list ltb_A xs ys)
  end.

Lemma ltb_list_lt_list :
  forall {A : Type} `{EqBool A} (ltb_A : A -> A -> bool) (lt_A : A -> A -> Prop) (l l' : list A),
    (forall (x : A), In x l -> forall (y : A), ltb_A x y = true <-> lt_A x y) ->
    ltb_list ltb_A l l' = true <-> lt_list lt_A l l'.
Proof.
  intros ?????? equ; split; intro h.
  - generalize dependent l'; induction l as [| x xs IHxs]; intros l' h;
      destruct l' as [|y ys]; try easy.
    have equ' := (equ x ltac:(now right) y); cbn in equ' |- *.
    cbn in h. apply Bool.orb_prop in h; destruct h as [hltb | hlt].
    + left; rewrite -equ' //.
    + apply andb_prop in hlt; destruct hlt.
      right; split.
      * rewrite -eqbIsEq //.
      * apply IHxs; auto.
        intros. apply equ; now left.
  - generalize dependent l'; induction l as [| x xs IHxs]; intros l' h;
      destruct l' as [|y ys]; try easy.
    cbn in *; destruct h as [ e | [e h] ].
    + apply Bool.orb_true_intro. left.
      rewrite equ; auto; now left.
    + apply Bool.orb_true_intro. right.
      apply andb_true_intro; split.
      * now rewrite eqbIsEq.
      * apply IHxs; auto.
Qed.

Lemma ltb_list_false :
  forall {A : Type} `{EqBool A} (ltb_A : A -> A -> bool) (l l' : list A),
    (forall (x : A), In x l -> forall (y : A), ltb_A x y = false -> x <> y -> ltb_A y x = true) ->
    ltb_list ltb_A l l' = false -> l <> l' -> ltb_list ltb_A l' l = true.
Proof.
  intros ????? hltA hnltb ne.
  generalize dependent l. induction l' as [|z zs IHzs]; intros l hltA hnltb ne;
    destruct l as [|z' zs']; try easy.
  cbn in *. apply Bool.orb_false_elim in hnltb; destruct hnltb as [ltbz h].
  apply Bool.andb_false_elim in h. destruct h as [ne' | nlt]; apply Bool.orb_true_intro.
  - left. apply hltA; try easy.
    + now right.
    + now rewrite -EqBool_neq in ne'.
  - have h : z' <> z \/ (z' = z /\ zs' <> zs).
    { destruct (z' == z); auto.
      right; split; auto. intro; apply ne; now subst. }
    destruct h as [ ne' | [e ne'] ].
    + left. apply hltA; try easy. now right.
    + right. apply andb_true_intro; split.
      * rewrite eqbIsEq //.
      * apply IHzs; auto.
Qed.

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

Lemma get_replace_nth' :
  forall {A : Type} (n m : nat) (x y : A) (l : list A),
    l.(n) = Some x -> n <> m ->
    (replace_nth m y l).(n) = Some x.
Proof.
  intros ?????? en ne. generalize dependent n.
  functional induction (replace_nth m y l) using replace_nth__ind; auto; intros n en ne.
  - destruct n; auto.
    exfalso. now apply ne.
  - destruct n; cbn in *; auto.
Qed.

Lemma get_replace_nth_inv'  :
  forall {A : Type} (n m : nat) (x y : A) (l : list A),
    (replace_nth m y l).(n) = Some x -> n <> m ->
    l.(n) = Some x.
Proof.
  intros ?????? e ne. generalize dependent n. revert m. induction l as [|z zs IHzs];
    intro m; destruct m; intros n e ne; cbn in *.
  - rewrite nth_error_nil in e; inversion e.
  - rewrite nth_error_nil in e; inversion e.
  - destruct n; try congruence. now cbn in *.
  - destruct n; cbn in *; auto.
    eapply IHzs; eauto.
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

Lemma replace_nth_Some :
  forall {A : Type} (n m : nat) (x y : A) (l : list A),
    l.(n) = Some x ->
    exists z, (replace_nth m y l).(n) = Some z.
Proof.
  intros ?????? en. generalize dependent n.
  functional induction (replace_nth m y l) using replace_nth__ind; intros k ek.
  - now rewrite nth_error_nil in ek.
  - destruct k.
    + now exists x0.
    + exists x; cbn in ek |- *; auto.
  - destruct k; cbn.
    + exists y; auto.
    + cbn in ek. now specialize (IHl0 k ek).
Qed.

Lemma replace_nth_replace_nth :
  forall {A : Type} (n m : nat) (x y : A) (l : list A),
    n <> m ->
    replace_nth n x (replace_nth m y l) =
      replace_nth m y (replace_nth n x l).
Proof.
  intros ?????? e. generalize dependent m. revert n. induction l as [|z zs IHzs]; cbn;
    intros n m e.
  - destruct n, m; now cbn.
  - destruct n, m; cbn.
    + exfalso; now apply e.
    + reflexivity.
    + reflexivity.
    + rewrite IHzs; auto.
Qed.

Lemma In_In_replace_nth :
  forall {A : Type} (n : nat) (x y : A) (l : list A),
    x <> y -> List.In x (replace_nth n y l) ->
    List.In x l.
Proof.
  intros ????? e hinr. generalize dependent n; induction l as [|z zs IHzs];
    intros n hinr.
  - destruct n; cbn in *; auto.
  - destruct n.
    + cbn in hinr |- *. destruct hinr; subst; auto.
      exfalso; now apply e.
    + cbn in hinr |- *. destruct hinr; auto.
      right; eapply IHzs; eauto.
Qed.

Lemma hd_error_hd :
  forall {A : Type} (x y : A) (l : list A),
    hd_error l = Some x -> hd y l = x.
Proof.
  intros ???? hin; destruct l.
  - inversion hin.
  - cbn in hin |- *. now injection hin.
Qed.
