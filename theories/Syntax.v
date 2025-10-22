(** * Syntax: definition of a locally-nameless first-order logic syntax. *)

From Tableaux Require Export Prelude.
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
  Context {func var : Atom} `{set_var : set var}.

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
  Context {pred func var : Atom} `{set_var : set var}.

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
  ; extend : car -> Form_ pred func var -> car
  ; in_ctx : Form_ pred func var -> car -> Type }.
Arguments extend {_ _ _ _} _ _.
Arguments in_ctx {_ _ _ _} _ _.
Arguments Con_ : clear implicits.
Definition Con := Con_ string string string.

Notation "Gamma ,, A" := (extend Gamma A) (at level 20).
Notation "A \in Gamma" := (in_ctx A Gamma) (at level 30).

Canonical Structure con_list_forms {pred func var : Atom} :=
  {| car := list (Form_ pred func var)
  ;  extend := fun Gamma A => A :: Gamma
  ;  in_ctx := In |}.
Arguments con_list_forms : clear implicits.

(** ** Utils functions *)

Fixpoint get_symbol {func var : Atom} (t : Term_ func var) : option func :=
  match t with
  | Bound _ | Free _ => None
  | Fun f _ => Some f
  end.
