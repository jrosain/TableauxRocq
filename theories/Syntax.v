(** * Syntax: definition of a locally-nameless first-order logic syntax. *)

From Tableaux Require Export Prelude.

From Stdlib Require Import Structures.Orders.

Import ListNotations.

(** ** First-order logic terms *)

Inductive Term_ {func var : Atom} : Type :=
| Bound : nat -> Term_
| Free  : var -> Term_
| Fun   : func -> list Term_ -> Term_.

Arguments Term_ : clear implicits.
Definition Term := Term_ string string.

(** *** Better induction principles for terms *)
Section TermInd.
  Context {func var : Atom}.

  Definition term_rect (P : Term_ func var -> Type) (Pb : forall (n : nat), P (Bound n))
    (Pa : forall (a : var), P (Free a))
    (Pl : forall (f : func) (l : list (Term_ func var)), Forall P l -> P (Fun f l)) :
    forall (t : Term_ func var), P t :=
    fix F (t : Term_ func var) : P t :=
      let fix F_list (l : list (Term_ func var)) : Forall P l :=
        match l with
        | [] => Forall_nil P
        | x :: xs => Forall_cons P x xs (F_list xs) (F x)
        end in
      match t with
      | Bound n => Pb n
      | Free  a => Pa a
      | Fun f l => Pl f l (F_list l)
      end.

  Definition term_ind (P : Term_ func var -> Prop) (Pb : forall (n : nat), P (Bound n))
    (Pa : forall (a : var), P (Free a))
    (Pl : forall (f : func) (l : list (Term_ func var)), Forall P l -> P (Fun f l)) :
    forall (t : Term_ func var), P t :=
    term_rect P Pb Pa Pl.

  Definition term_rect' (P : Term_ func var -> Type) (Pb : forall (n : nat), P (Bound n))
    (Pa : forall (a : var), P (Free a))
    (Pl : forall (f : func) (l : list (Term_ func var)),
        (forall (t : Term_ func var), In t l -> P t) -> P (Fun f l)) :
    forall (t : Term_ func var), P t.
  Proof.
    apply term_rect; auto.
    intros ?? H. apply Pl; intros. eapply Forall_In in H; eauto.
  Defined.

  Definition term_ind' (P : Term_ func var -> Prop) (Pb : forall (n : nat), P (Bound n))
    (Pa : forall (a : var), P (Free a))
    (Pl : forall (f : func) (l : list (Term_ func var)),
        (forall (t : Term_ func var), In t l -> P t) -> P (Fun f l)) :
    forall (t : Term_ func var), P t :=
    term_rect' P Pb Pa Pl.
End TermInd.

(** *** Decidable equality for terms *)
Section DecEqTerms.
  Context {func var : Atom}.
  Existing Instance eq_dec_atom.

  #[global] Instance eqDec_Term : EqDec (Term_ func var).
  Proof using Type.
    intros t; induction t as [n | x | f xs IHxs] using term_rect';
      intro u; destruct u as [m | y | g ys].
    all: try (right; intro contra; inversion contra; fail).
    - destruct (n == m).
      + left; now f_equal.
      + right; intro e. injection e => e'. now apply n0.
    - destruct (x == y).
      + left; now f_equal.
      + right; intro e. injection e => e'. now apply n.
    - destruct (f == g).
      2: right; intro e; injection e => e0 e1; now apply n.
      generalize dependent xs. induction ys as [|y ys IHys]; destruct xs as [|x xs].
      2,3: right; intro e0; injection e0 => e0' e1; inversion e0'.
      + left; now rewrite e.
      + intros IHxs. specialize (IHys xs).
        have H : (forall t : Term_ func var, In t xs -> forall y : Term_ func var, {t = y} + {t <> y}).
        { intros t Hin z. apply IHxs. now left. }
        specialize (IHxs x (inright eq_refl)).
        destruct (IHxs y).
        2: right; intro e0; injection e0 => e1 e2 e3; now apply n.
        specialize (IHys H). destruct IHys as [e1 | ne1].
        * left. rewrite e0. injection e1 => e1' e1''. now rewrite e1' e1''.
        * right; intro e1. injection e1 => e2 e3 e4. apply ne1.
          rewrite e e2 //.
  Qed.
End DecEqTerms.

(** Set of [Term]s. *)
Module OrderedTerm <: OrderedType.
  Definition t := Term.
  Definition eq := @eq Term.
  Definition eq_equiv := @eq_equivalence Term.

  Inductive lt_list {A : Type} {lt : A -> A -> Prop} : list A -> list A -> Prop :=
  | lt_head : forall (t u : A) (l l' : list A), lt t u -> lt_list (t :: l) (u :: l')
  | lt_cons : forall (t : A) (l l' : list A), lt_list l l' -> lt_list (t :: l) (t :: l').
  Arguments lt_list {_} _ _ _.

  Lemma lt_list_irrefl :
    forall {A : Type} {lt : A -> A -> Prop} (l : list A),
      (forall t, In t l -> lt t t -> False) -> lt_list lt l l -> False.
  Proof.
    intros A lt l hirrefl hlt.
    have H0 : exists l', lt_list lt l l' /\ l = l' by exists l.
    destruct H0 as (l' & H' & e); induction H'.
    + injection e => e0 e1; subst. unshelve eapply hirrefl.
      * exact u.
      * now right.
      * assumption.
    + injection e => e0; subst. apply IHH'; auto.
      intros; eapply hirrefl; eauto. now left.
  Qed.

  Fixpoint compare_list {A : Type} (cmp : A -> A -> comparison) (l l' : list A) : comparison :=
    match l, l' with
    | [], [] => Eq
    | [], _  => Lt
    | _ , [] => Gt
    | x :: xs, y :: ys =>
        match cmp x y with
        | Eq => compare_list cmp xs ys
        | _ as v => v
        end
    end.

  Inductive lt_ : Term -> Term -> Prop :=
  | termLtBoundBound : forall (n m : nat), n < m -> lt_ (Bound n) (Bound m)
  | termLtBoundFree  : forall (n : nat) (x : string), lt_ (Bound n) (Free x)
  | termLtBoundFun   : forall (n : nat) (f : string) (l : list Term), lt_ (Bound n) (Fun f l)
  | termLtFreeFree   : forall (x y : string), OrderedString.lt x y -> lt_ (Free x) (Free y)
  | termLtFreeFun    : forall (x : string) (f : string) (l : list Term), lt_ (Free x) (Fun f l)
  | termLtFunFun1    : forall (f f' : string) (l l' : list Term),
      OrderedString.lt f f' -> lt_ (Fun f l) (Fun f' l')
  | termLtFunFun2    : forall (f : string) (l l' : list Term),
      lt_list lt_ l l' -> lt_ (Fun f l) (Fun f l').

  (* Definition lt_ind' (P : Term -> Term -> Prop) (f : forall n m : nat, n < m -> P (Bound n) (Bound m)) *)
  (*   (f0 : forall (n : nat) (x : string), P (Bound n) (Free x)) *)
  (*   (f1 : forall (n : nat) (f1 : string) (l : list Term), P (Bound n) (Fun f1 l)) *)
  (*   (f2 : forall x y : string, OrderedString.lt x y -> P (Free x) (Free y)) *)
  (*   (f3 : forall (x f3 : string) (l : list Term), P (Free x) (Fun f3 l)) *)
  (*   (f4 : forall (f4 f' : string) (l l' : list Term), OrderedString.lt f4 f' -> P (Fun f4 l) (Fun f' l')) *)
  (*   (f5 : forall (f5 : string) (l l' : list Term), *)
  (*       (forall i t u, nth_error l i = Some t -> nth_error l' i = Some u -> lt t u -> P t u) -> *)
  (*       lt_list lt l l' -> P (Fun f5 l) (Fun f5 l')) *)
  (*    : forall (t t0 : Term), lt t t0 -> P t t0. *)
  (* Proof. *)
  (*   refine (fix F (t t0 : Term) (h : lt t t0) : P t t0 := *)
  (*             let fix F_list (l l' : list Term) (h0 : lt_list lt l l') : *)
  (*               (forall i t u, nth_error l i = Some t -> nth_error l' i = Some u -> lt t u -> P t u) := _ *)
  (*             in *)
  (*             match h in (lt t1 t2) return (P t1 t2) with *)
  (*             | termLtBoundBound n m x => f n m x *)
  (*             | termLtBoundFree n x => f0 n x *)
  (*             | termLtBoundFun n f6 l0 => f1 n f6 l0 *)
  (*             | termLtFreeFree x y x0 => f2 x y x0 *)
  (*             | termLtFreeFun x f6 l0 => f3 x f6 l0 *)
  (*             | termLtFunFun1 f6 f' l0 l' x => f4 f6 f' l0 l' x *)
  (*             | termLtFunFun2 f6 l0 l' x => f5 f6 l0 l' (F_list l0 l' x) x *)
  (*             end). *)
  (*   intros. destruct h0. *)
  (*   - now apply F. *)
  (*   - destruct i; cbn in *. *)
  (*     + now apply F. *)
  (*     + eapply F_list; eauto. *)
  (* Defined. *)

  Definition lt := lt_.

  Lemma lt_strorder : StrictOrder lt.
  Proof. Admitted.
    (* split. *)
    (* - intros t H. *)
    (*   have H0 : exists u, lt t u /\ t = u by exists t. *)
    (*   destruct H0 as (u & H' & e); induction H'; *)
    (*     try (inversion e; fail). *)
    (*   + injection e => e'. rewrite e' in H0. *)
    (*     now apply StrictOrder_Irreflexive in H0. *)
    (*   + injection e => e'. rewrite e' in H0. *)
    (*     now apply StrictOrder_Irreflexive in H0. *)
    (*   + injection e => _ e'. rewrite e' in H0. *)
    (*     now apply StrictOrder_Irreflexive in H0. *)
    (*   + injection e => e'; subst. eapply lt_list_irrefl. *)
    (*     2: exact H0. *)
        
        
    (*     intros. *)
    (*   apply H. intros l hlt. *)
    (*   have H0 : exists l', lt_list l l' /\ l = l' by exists l. *)
    (*   destruct H0 as (l' & H' & e); induction H'. *)
    (*   + injection e => e0 e1; subst. *)
    (*     have contra : (lt u u -> False). *)
    (*     { apply H. intro. intro. *)
    (*     injection e' => _ e0. subst. apply IHH'; auto. *)
    (* - intros t u v htu huv. *)
    (*   have H0 : exists u', lt u' v /\ u = u' by exists u. *)
    (*   destruct H0 as (u' & H' & e). clear huv. induction htu; destruct H'. *)
    (*   (** trivial cases *) *)
    (*   all: try now constructor. *)
    (*   (** inconsistency in the equality *) *)
    (*   all: try (inversion e; fail). *)
    (*   + constructor. eapply StrictOrder_Transitive; eauto. *)
    (*     injection e => e'; now subst. *)
    (*   + constructor. eapply StrictOrder_Transitive; eauto. *)
    (*     injection e => e'; now subst. *)
    (*   + injection e => e' e''; subst. constructor. *)
    (*     eapply StrictOrder_Transitive; eauto. *)
    (*   + injection e => e' e''; subst; now constructor. *)
    (*   + injection e => e' e''; subst; now constructor. *)
    (*   + injection e => e' e''. rewrite e''. *)
    (*     have H : lt t0 u0. *)
    (*     {  *)
    (*     eapply termLtFunFun2. *)

  Lemma lt_compat : Proper (Logic.eq ==> Logic.eq ==> iff) lt.
  Proof.
    intros t u e t' u' e'. split.
    + intros; now subst.
    + intros; now subst.
  Qed.

  Fixpoint compare (t u : Term) : comparison :=
    match t, u with
    | Bound n, Bound m => OrderedNat.compare n m
    | Bound _, Free  _ => Lt
    | Bound _, Fun _ _ => Lt
    | Free _ , Bound _ => Gt
    | Free x , Free y  => OrderedString.compare x y
    | Free _ , Fun _ _ => Lt
    | Fun _ _, Bound _ => Gt
    | Fun _ _, Free _ => Gt
    | Fun x xs, Fun y ys =>
        match OrderedString.compare x y with
        | Eq => compare_list compare xs ys
        | _ as v => v
        end
    end.

  Lemma compare_spec :
    forall t u : Term, CompareSpec (t = u) (lt t u) (lt u t) (compare t u).
  Proof.
    intros t u; destruct t, u; cbn.
    - destruct (OrderedNat.compare n n0) eqn:e.
      + constructor.
        apply PeanoNat.Nat.compare_eq in e; now subst.
      + constructor.
        apply PeanoNat.Nat.compare_lt_iff in e. now constructor.
      + constructor.
        apply PeanoNat.Nat.compare_gt_iff in e. now constructor.
    - do 2 constructor.
    - do 2 constructor.
    - do 2 constructor.
    - have H := (OrderedString.compare_spec a a0); destruct H.
      + constructor. now rewrite H.
      + now do 2 constructor.
      + now do 2 constructor.
    - do 2 constructor.
    - do 2 constructor.
    - do 2 constructor.
    - have H := (OrderedString.compare_spec a a0); destruct H.
      + generalize dependent l0. induction l; destruct l0.
        * constructor. now rewrite H.
        * constructor. admit.
        * constructor. admit.
        * admit.
      + now do 2 constructor.
      + now do 2 constructor.
  Admitted.

  Definition eq_dec := @eqDec Term _.
End OrderedTerm.

Module SetOfTerm_ := SetFromOrdered OrderedTerm.
Canonical Structure SetOfTerm := SetOfTerm_.set_of_ordered.

(** *** Opening and substitution for terms *)
Section OpeningSubstTerms.
  Context {func var : Atom} `{set_nat : set nat}.
  Existing Instance eq_dec_atom.

  #[global] Instance opening_term : Opening (Term_ func var) (Term_ func var) :=
    fun n u =>
      fix F (t : Term_ func var) : Term_ func var :=
      match t with
      | Bound m => match n == m with
                  | left _ => u
                  | right _ => t
                  end
      | Free  _ => t
      | Fun f l => Fun f (map F l)
      end.

  #[global] Instance bv_term : BV (Term_ func var) :=
    fix F (t : Term_ func var) : set_nat :=
      match t with
      | Bound m => singleton m
      | Free  _ => empty_set nat
      | Fun _ l => fold_left (fun s t => s \union (F t)) l (empty_set nat)
      end.

  #[global] Instance subst_term : Subst (Term_ func var) (Term_ func var) :=
    fun t sigma =>
      (fix F (t : Term_ func var) : Term_ func var :=
         match t with
         | Bound _ => t
         | Free  x => sigma x
         | Fun f l => Fun f (map F l)
         end) t.
End OpeningSubstTerms.

(** *** Free variables of terms *)
Section FVTerms.
  Context {func var : Atom}.

  Let set_var := set_atom var.

  #[global] Instance fv_term : FV (Term_ func var) :=
    fix F (t : Term_ func var) : set_var :=
      match t with
      | Bound _ => empty_set var
      | Free  x => singleton x
      | Fun f l => fold_left (fun s t => s \union (F t)) l (empty_set var)
      end.
End FVTerms.

(** ** Minimal first-order logic formulas *)
Inductive Form_ {pred func var : Atom} : Type :=
| Bot  : Form_
| Pred : pred -> list (Term_ func var) -> Form_
| Neg  : Form_ -> Form_
| Or   : Form_ -> Form_ -> Form_
| All  : Form_ -> Form_.

Arguments Form_ : clear implicits.
Definition Form := Form_ string string string.

(** *** Decidable equality for formulas *)
Section DecEqForms.
  Context {pred func var : Atom}.
  Existing Instance eq_dec_atom.
  Existing Instance eq_dec_list.

  #[global] Instance eq_dec_form : EqDec (Form_ pred func var).
  Proof using Type.
    intros F; induction F as [|p l | F' IHF' | F1 IHF1 F2 IHF2 | F' IHF'];
      intros G; destruct G as [|p' l' | G' | G1 G2 | G'].
    all: try (right; intro contra; inversion contra; fail).
    - now left.
    - destruct (p == p').
      2: right; intro e; injection e => e0 e1; now apply n.
      destruct (l == l').
      2: right; intro e'; injection e' => e0 e1; now apply n.
      left; now rewrite e e0.
    - destruct (IHF' G').
      2: right; intro e; injection e => e0; now apply n.
      left; now rewrite e.
    - destruct (IHF1 G1).
      2: right; intro e; injection e => e0 e1; now apply n.
      destruct (IHF2 G2).
      2: right; intro e'; injection e' => e0' e1'; now apply n.
      left; now rewrite e e0.
    - destruct (IHF' G').
      2: right; intro e; injection e => e0; now apply n.
      left; now rewrite e.
  Qed.
End DecEqForms.

(** *** Opening and substitution for formulas *)
Section OpeningSubstForms.
  Context {pred func var : Atom} `{set_nat : set nat}.
  Existing Instance bv_term.

  #[global] Instance opening_form : Opening (Term_ func var) (Form_ pred func var) :=
    fun n u =>
      (fix rec (n : nat) (F : Form_ pred func var) : Form_ pred func var :=
         match F with
         | Bot      => Bot
         | Pred p l => Pred p (map (fun t => t{n \to u}) l)
         | Neg  F'  => Neg (rec n F')
         | Or F1 F2 => Or (rec n F1) (rec n F2)
         | All  F'  => All (rec (n+1) F')
         end) n.

  #[global] Instance subst_form : Subst (Form_ pred func var) (Term_ func var) :=
    fun F sigma =>
      (fix rec (F : Form_ pred func var) : Form_ pred func var :=
         match F with
         | Bot      => Bot
         | Pred p l => Pred p (map (fun t => t@[sigma]) l)
         | Neg F'   => Neg (rec F')
         | Or F1 F2 => Or (rec F1) (rec F2)
         | All F'   => All (rec F')
         end) F.
End OpeningSubstForms.

(** *** Free variables of forms *)
Section FVForms.
  Context {pred func var : Atom}.

  Let set_var := set_atom var.

  #[global] Instance fv_form : FV (Form_ pred func var) :=
    fix rec (F : Form_ pred func var) : set_var :=
      match F with
      | Bot      => empty_set var
      | Pred f l => fold_left (fun s t => s \union (fv t)) l (empty_set var)
      | Neg F'   => rec F'
      | Or F1 F2 => (rec F1) \union (rec F2)
      | All F'   => rec F'
      end.
End FVForms.

(** ** Contexts *)
Class Con_ {pred func var : Atom} :=
  { car :> Type
  ; empty_con : car
  ; extend : car -> Form_ pred func var -> car
  ; in_ctx : Form_ pred func var -> car -> Type
  ; con_nth : car -> nat -> option (Form_ pred func var) }.
Arguments empty_con {_ _ _ _}.
Arguments extend {_ _ _ _} _ _.
Arguments in_ctx {_ _ _ _} _ _.
Arguments con_nth {_ _ _ _} _ _.
Arguments Con_ : clear implicits.

Notation "Gamma ,, A" := (extend Gamma A) (at level 20).
Notation "A \in Gamma" := (in_ctx A Gamma) (at level 30).

Canonical Structure Con :=
  {| car := list Form
  ;  empty_con := []
  ;  extend := fun Gamma A => A :: Gamma
  ;  in_ctx := In
  ;  con_nth := @nth_error Form |}.
Arguments Con : clear implicits.

Notation "{{ F }}" := (empty_con ,, F).

(** ** Utils functions *)

Fixpoint get_symbol {func var : Atom} (t : Term_ func var) : option func :=
  match t with
  | Bound _ | Free _ => None
  | Fun f _ => Some f
  end.
