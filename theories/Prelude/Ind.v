(** * Prelude.Ind: useful inductives not defined in Corelib/Stdlib *)

From Tableaux Require Import Prelude.Init.

(** ** Inductives *)

Inductive Forall {A : Type} (P : A -> Type) : list A -> Type :=
| Forall_nil : Forall P []
| Forall_cons : forall (x : A) (l : list A), Forall P l -> P x -> Forall P (x :: l).

Fixpoint In {A : Type} (x : A) (l : list A) : Type :=
  match l with
  | [] => False
  | (cons y ys) => In x ys + { x = y }
  end.

(** ** Equivalence between [Forall] and [In]. *)
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

(** ** Some properties of [Forall] *)

Lemma Forall_tail :
  forall {A : Type} {x : A} {xs : list A} (P : A -> Type),
    Forall P (x :: xs) -> Forall P xs.
Proof. intros ???? H. now inversion H. Qed.
