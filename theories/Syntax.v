(** * Syntax: definition of a locally-nameless first-order logic syntax. *)

From Tableaux Require Export Prelude.All.

From Stdlib Require Import Lia.
From Stdlib Require Import Structures.Orders.

(** ** First-order logic terms *)

Inductive Term {func var : Atom} : Type :=
| Bound : nat -> Term
| Free  : var -> Term
| Fun   : func -> list Term -> Term.

Arguments Term : clear implicits.

(** *** Better induction principles for terms *)
Section TermInd.
  Context {func var : Atom}.

  Definition term_rect (P : Term func var -> Type) (Pb : forall (n : nat), P (Bound n))
    (Pa : forall (a : var), P (Free a))
    (Pl : forall (f : func) (l : list (Term func var)), Forall P l -> P (Fun f l)) :
    forall (t : Term func var), P t :=
    fix F (t : Term func var) : P t :=
      let fix F_list (l : list (Term func var)) : Forall P l :=
        match l with
        | [] => Forall_nil P
        | x :: xs => Forall_cons P x xs (F_list xs) (F x)
        end in
      match t with
      | Bound n => Pb n
      | Free  a => Pa a
      | Fun f l => Pl f l (F_list l)
      end.

  Definition term_ind (P : Term func var -> Prop) (Pb : forall (n : nat), P (Bound n))
    (Pa : forall (a : var), P (Free a))
    (Pl : forall (f : func) (l : list (Term func var)), Forall P l -> P (Fun f l)) :
    forall (t : Term func var), P t :=
    term_rect P Pb Pa Pl.

  Definition term_rect' (P : Term func var -> Type) (Pb : forall (n : nat), P (Bound n))
    (Pa : forall (a : var), P (Free a))
    (Pl : forall (f : func) (l : list (Term func var)),
        (forall (t : Term func var), In t l -> P t) -> P (Fun f l)) :
    forall (t : Term func var), P t.
  Proof.
    apply term_rect; auto.
    intros ?? H. apply Pl; intros. eapply Forall_In in H; eauto.
  Defined.

  Definition term_ind' (P : Term func var -> Prop) (Pb : forall (n : nat), P (Bound n))
    (Pa : forall (a : var), P (Free a))
    (Pl : forall (f : func) (l : list (Term func var)),
        (forall (t : Term func var), In t l -> P t) -> P (Fun f l)) :
    forall (t : Term func var), P t :=
    term_rect' P Pb Pa Pl.
End TermInd.

(** *** Decidable equality for terms *)
Section DecEqTerms.
  Context {func var : Atom}.

  Fixpoint eqb_term (t u : Term func var) : bool :=
    match t, u with
    | Bound n, Bound m | Free n, Free m => eqb n m
    | Fun f l, Fun g l' =>
        eqb f g && forallb2 eqb_term l l'
    | _, _ => false
    end.

  Lemma eqb_term_eq :
    forall t u : Term func var, eqb_term t u = true <-> t = u.
  Proof using Type.
    intros t; induction t as [n | x | f xs IHxs] using term_rect';
      intro u; destruct u as [m | y | g ys]; split; cbn.
    all: try (now intro).
    - intro heqb. rewrite eqbIsEq in heqb. rewrite heqb //.
    - intro e. injection e => ->. rewrite eqbIsEq //.
    - rewrite eqbIsEq. now intros ->.
    - intros e; injection e => ->. rewrite eqbIsEq //.
    - intros (e & e')%andb_prop. rewrite eqbIsEq in e. rewrite e.
      apply f_equal. eapply forallb2_eq; eauto.
      intros. rewrite -IHxs; auto.
    - intros e; injection e => -> ->.
      rewrite Bool.andb_true_iff. split.
      + apply EqBool_refl.
      + apply forallb2_refl. intros. rewrite IHxs; auto.
        now injection e => -> _.
  Qed.

  #[global] Instance EqBool_term : EqBool (Term func var).
  Proof.
    unshelve econstructor.
    - exact eqb_term.
    - exact eqb_term_eq.
  Defined.

  #[global] Instance eqDec_Term : EqDec (Term func var).
  Proof using Type. typeclasses eauto. Defined.
End DecEqTerms.

(** *** Opening and substitution for terms *)
Section OpeningSubstTerms.
  Context {func var : Atom} `{set_nat : set nat}.

  #[global] Instance opening_term : Opening (Term func var) (Term func var) :=
    fun n u =>
      fix F (t : Term func var) : Term func var :=
      match t with
      | Bound m => if eqb n m then u else t
      | Free  _ => t
      | Fun f l => Fun f (map F l)
      end.

  #[global] Instance bv_term : BV (Term func var) :=
    fix F (t : Term func var) : set_nat :=
      match t with
      | Bound m => singleton m
      | Free  _ => empty_set
      | Fun _ l => @bv_list set_nat _ F l
      end.

  #[global] Instance subst_term : Subst (Term func var) (Term func var) :=
    fun t sigma =>
      (fix F (t : Term func var) : Term func var :=
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

  #[global] Instance fv_term : FV (Term func var) :=
    fix F (t : Term func var) : set_var :=
      match t with
      | Bound _ => empty_set
      | Free  x => singleton x
      | Fun f l => fold_left (fun s t => s \union (F t)) l empty_set
      end.
End FVTerms.

(** ** Subterms *)
Fixpoint is_subterm {func var : Atom} (t u : Term func var) : Prop :=
  let fix f_ls (l : list (Term func var)) : Prop :=
    match l with
    | [] => False
    | x :: xs => is_subterm t x \/ f_ls xs
    end in
  t = u \/
    match u with
    | Free _ | Bound _ => False
    | Fun f l => f_ls l
    end.

Lemma is_subterm_trans :
  forall {func var : Atom} (t0 t1 t2 : Term func var),
    is_subterm t0 t1 -> is_subterm t1 t2 -> is_subterm t0 t2.
Proof.
  intros ?????. induction t2 using term_ind; cbn in *.
  1-2: intros hsub [ e | contra ]; auto; left; rewrite e in hsub; cbn in hsub;
    now destruct hsub.
  intros hsub [ e | rec ].
  - rewrite e in hsub; now cbn in hsub.
  - right. induction l as [| u us IHus]; cbn in *; auto.
    destruct rec.
    + left. apply Forall_inv in X; now apply X.
    + right; apply IHus; auto.
      now apply Forall_tail in X.
Qed.

Lemma subterm_not_subterm_not_subterm :
  forall {func var : Atom} (t0 t1 t2 : Term func var),
    is_subterm t0 t2 -> ~is_subterm t1 t2 -> ~is_subterm t1 t0.
Proof.
  intros ????? hsub hnsub hsub'.
  have htrans := is_subterm_trans _ _ _ hsub' hsub.
  now apply hnsub.
Qed.
#[global] Opaque is_subterm.

(** ** Minimal first-order logic formulas *)
Inductive Form {pred func var : Atom} : Type :=
| Bot  : Form
| Pred : pred -> list (Term func var) -> Form
| Neg  : Form -> Form
| Or   : Form -> Form -> Form
| All  : Form -> Form.

Arguments Form : clear implicits.

Definition is_positive_litteral {pred func var : Atom}
  (F : Form pred func var) : bool :=
  match F with
  | Pred _ _ => true
  | _ => false
  end.

Definition is_negative_litteral {pred func var : Atom}
  (F : Form pred func var) : bool :=
  match F with
  | Neg F => is_positive_litteral F
  | _ => false
  end.

Definition is_litteral  {pred func var : Atom}
  (F : Form pred func var) : bool :=
  is_positive_litteral F || is_negative_litteral F.

(** *** Decidable equality for formulas *)
Section DecEqForms.
  Context {pred func var : Atom}.
  Existing Instance eq_dec_list.

  Fixpoint eqb_form (F G : Form pred func var) : bool :=
    match F, G with
    | Bot, Bot => true
    | Pred p l, Pred p' l' => eqb p p' && eqb l l'
    | Neg F, Neg G => eqb_form F G
    | Or F1 F2, Or G1 G2 => eqb_form F1 G1 && eqb_form F2 G2
    | All F, All G => eqb_form F G
    | _, _ => false
    end.

  Lemma eqb_form_eq :
    forall F G : Form pred func var, eqb_form F G = true <-> F = G.
  Proof using Type.
    intros F; induction F; intros G; destruct G; split; cbn.
    all: try now intro.
    - intros (e & e')%andb_prop. rewrite !eqbIsEq in e, e'. rewrite e e' //.
    - intros e; injection e => -> ->. apply andb_true_intro; split; apply EqBool_refl.
    - intro. apply f_equal. rewrite -IHF //.
    - intro. injection H => <-. rewrite IHF //.
    - intros (e & e')%andb_prop. rewrite IHF1 IHF2 in e, e'. now subst.
    - intros e; injection e => <- <-. apply andb_true_intro; split.
      + rewrite IHF1 //.
      + rewrite IHF2 //.
    - intros e; apply f_equal. rewrite -IHF //.
    - intros e; injection e => <-. rewrite IHF //.
  Qed.

  #[global] Instance eqbool_form : EqBool (Form pred func var).
  Proof.
    unshelve econstructor.
    - exact eqb_form.
    - exact eqb_form_eq.
  Defined.
End DecEqForms.

(** *** Opening and substitution for formulas *)
Section OpeningSubstForms.
  Context {pred func var : Atom} `{set_nat : set nat}.
  Existing Instance bv_term.

  Fixpoint opening_form_ (n : nat) (u : Term func var) (F : Form pred func var) :=
    match F with
    | Bot => Bot
    | Pred p l => Pred p (map (fun t => t{n \to u}) l)
    | Neg  F'  => Neg (opening_form_ n u F')
    | Or F1 F2 => Or (opening_form_ n u F1) (opening_form_ n u F2)
    | All  F'  => All (opening_form_ (n+1) u F')
    end.

  #[global] Instance opening_form : Opening (Term func var) (Form pred func var) :=
    opening_form_.

  #[global] Instance subst_form : Subst (Form pred func var) (Term func var) :=
    fun F sigma =>
      (fix rec (F : Form pred func var) : Form pred func var :=
         match F with
         | Bot      => Bot
         | Pred p l => Pred p (map (fun t => t@[sigma]) l)
         | Neg F'   => Neg (rec F')
         | Or F1 F2 => Or (rec F1) (rec F2)
         | All F'   => All (rec F')
         end) F.
End OpeningSubstForms.

Section SubstOpeningLemmas.
  Context {pred func var : Atom} `{set_nat : set nat}.

  Let Term := Term func var.
  Let Form := Form pred func var.

  Lemma isLocallyClosed_Fun_isLocallyClosed_list :
    forall (f : func) (l : list Term),
      isLocallyClosed (Fun f l) ->
      Forall isLocallyClosed l.
  Proof using Type.
    intros; apply In_Forall; intros t hin.
    red in H; cbn in H. red. apply is_empty_spec'.
    intros n hin'. apply (is_empty_spec n) in H; auto.
    induction l; inversion hin; auto; cbn; rewrite union_spec.
    - right. apply IHl; auto. cbn in H.
      now apply is_empty_union2 in H.
    - subst. now left.
  Qed.

  Lemma isLocallyClosed_Fun_isLocallyClosed_list' :
    forall (f : func) (l : list Term),
      isLocallyClosed (Fun f l) ->
      isLocallyClosed l.
  Proof using Type.
    intros ?? hclosed; apply isLocallyClosed_Fun_isLocallyClosed_list in hclosed;
      induction l as [|t ts IHts]; unfold isLocallyClosed in *; cbn.
    - reflexivity.
    - apply is_empty_union; split.
      + now apply Forall_inv in hclosed.
      + apply IHts; now apply Forall_tail in hclosed.
  Qed.

  Lemma term_locally_closed_inst :
    forall (t u : Term) (x : nat),
      isLocallyClosed t ->
      t { x \to u } = t.
  Proof using Type.
    intros t; induction t using term_ind; intros; cbn; auto.
    - red in H; cbn in H. apply (is_empty_spec n) in H.
      + inversion H.
      + now rewrite singleton_spec.
    - have hmap : map (varOpening x u) l = l.
      { apply isLocallyClosed_Fun_isLocallyClosed_list in H.
        induction l as [|t ts IHts]; auto.
        cbn. rewrite IHts; auto.
        - now apply Forall_tail in X.
        - now apply Forall_tail in H.
        - apply Forall_inv in X. rewrite X; auto.
          now apply Forall_inv in H. }
      rewrite hmap //.
  Qed.

  Lemma isLocallyClosed_isLocallyClosed_subst :
    forall (t : Term) (sigma : Substitution var Term),
      isLocallyClosed t ->
      isLocallyClosed t@[sigma].
  Proof using Type.
    intros ???. induction t using term_ind; auto; cbn.
    - apply sigma.
    - have hclosed : @isLocallyClosed set_nat _ _ (map (fun t => subst_term t sigma) l).
      { apply isLocallyClosed_Fun_isLocallyClosed_list in H.
        induction l as [|t ts IHts]; cbn.
        - red. now cbn.
        - red. cbn. apply is_empty_spec'.
          + intros x; rewrite union_spec; intros [].
            * apply Forall_inv in X, H.
              apply X in H. red in H.
              apply is_empty_spec with (x := x) in H; auto.
            * apply Forall_tail in X, H. specialize (IHts H X).
              red in IHts. apply is_empty_spec with (x := x) in IHts; auto. }
      red; now cbn.
  Qed.

  Lemma term_subst_opening :
    forall (t u : Term) (x : nat) (sigma : Substitution var Term),
      (t { x \to u })@[sigma] = t@[sigma] { x \to u@[sigma] }.
  Proof using Type.
    intros t; induction t using term_ind; intros; cbn.
    - rewrite -!match_eq_dec_eq_bool.
      destruct (x == n); cbn; auto.
    - destruct sigma as [sigma Hsigma]; cbn.
      rewrite term_locally_closed_inst; auto.
    - rewrite !map_map; cbn.
      have hmap : map (fun t => (t { x \to u })@[sigma]) l =
                    map (fun t => (t@[sigma] { x \to u@[sigma] })) l.
      { induction l as [|t ts IHts]; auto.
        cbn; rewrite IHts.
        - now apply Forall_tail in X.
        - apply Forall_inv in X. now rewrite X. }
      now rewrite hmap.
  Qed.

  Lemma form_subst_opening :
    forall (F : Form) (u : Term) (x : nat) (sigma : Substitution var Term),
      (F { x \to u })@[sigma] = F@[sigma] { x \to u@[sigma] }.
  Proof using Type.
    intros ??; induction F; intros; auto; cbn.
    - have hmap : map (fun t => (t { x \to u })@[sigma]) l =
                         map (fun t => (t@[sigma] { x \to u@[sigma] })) l.
      { induction l as [|t ts IHts]; auto.
        cbn; rewrite term_subst_opening IHts //. }
      rewrite !map_map hmap //.
    - now rewrite -IHF.
    - now rewrite -IHF1 -IHF2.
    - rewrite -IHF //.
  Qed.
End SubstOpeningLemmas.

(** *** Free variables of forms *)
Section FVForms.
  Context {pred func var : Atom}.

  Let set_var := set_atom var.

  #[global] Instance fv_form : FV (Form pred func var) :=
    fix rec (F : Form pred func var) : set_var :=
      match F with
      | Bot      => empty_set
      | Pred f l => fold_left (fun s t => s \union (fv t)) l empty_set
      | Neg F'   => rec F'
      | Or F1 F2 => (rec F1) \union (rec F2)
      | All F'   => rec F'
      end.
End FVForms.

(** *** Subformulas *)

Class HasSubformulas (pred func var : Atom) (A : Type) :=
  is_subformula : Form pred func var -> A -> Prop.

#[global] Instance HasSubformulas_list {pred func var : Atom} {A : Type}
  `{@HasSubformulas pred func var A} : HasSubformulas pred func var (list A) :=
  fix rec (F : Form pred func var) (l : list A) : Prop :=
    match l with
    | [] => False
    | G :: Gs => is_subformula F G \/ rec F Gs
    end.

#[global] Instance HasSubformulas_Form {pred func var : Atom} :
  HasSubformulas pred func var (Form pred func var) :=
  fun F G =>
    let fix rec (F G : Form pred func var) : Prop :=
      match G with
      | Neg G | All G => rec F G
      | Or G1 G2 => rec F G1 \/ rec F G2
      | _ => False
      end in
    F = G \/ rec F G.

Fixpoint ls_to_form {pred func var : Atom} (Gamma : list (Form pred func var))
  : Form pred func var :=
  match Gamma with
  | [] => Neg Bot
  | F :: Fs => Neg (Or (Neg F) (Neg (ls_to_form Fs)))
  end.

(** *** Closedness *)
Section isClosedLemmas.
  Context {pred func var : Atom} `{set_nat : set nat}.

  Let Term := Term func var.
  Let Form := Form pred func var.

  Lemma isClosedList_elem :
    forall (l : list Form) (F : Form),
      List.In F l -> isClosed l -> isClosed F.
  Proof using Type.
    intros ?? hin hclosed. induction l as [|G Gs IHGs]; inversion hin.
    - unfold isClosed in hclosed |- *; cbn in hclosed |- *.
      subst. now apply is_empty_union1 in hclosed.
    - apply IHGs; auto. now apply is_empty_union2 in hclosed.
  Qed.

  Lemma isClosedList_isClosedFormisClosed :
    forall (l : list Form) (F : Form),
      isClosed F -> isClosed l -> isClosed (F :: l).
  Proof using Type.
    intros ?? hclosedF hclosedl. unfold isClosed in hclosedF, hclosedl |- *.
    cbn in *. apply is_empty_spec'. intros.
    rewrite union_spec in H. destruct H.
    - now apply (is_empty_spec x) in hclosedF.
    - now apply (is_empty_spec x) in hclosedl.
  Qed.

  Lemma isClosedList_isClosedFormList :
    forall (l : list Form),
      isClosed (ls_to_form l) <-> isClosed l.
  Proof using Type.
    intros; induction l as [|F Fs IHFs]; unfold isClosed; cbn.
    - reflexivity.
    - split; intro h; unfold isClosed in IHFs; cbn in *.
      + apply is_empty_union; split.
        * now apply is_empty_union1 in h.
        * apply is_empty_union2 in h. rewrite -IHFs //.
      + apply is_empty_union; split.
        * now apply is_empty_union1 in h.
        * apply is_empty_union2 in h. rewrite IHFs //.
  Qed.

  Lemma isClosed_subst_term :
    forall (t : Term) (sigma : Substitution var Term),
      isClosed t -> t@[sigma] = t.
  Proof using Type.
    intros t sigma hclosed; induction t using term_ind; try reflexivity.
    - unfold isClosed in hclosed. apply (is_empty_spec a) in hclosed.
      + destruct hclosed.
      + cbn. rewrite singleton_spec //.
    - cbn. apply f_equal. induction l as [|u us IHus]; auto.
      cbn. rewrite IHus.
      + unfold isClosed in hclosed |- *; cbn in *.
        rewrite set_fold_left in hclosed.
        rewrite empty_unitl in hclosed. now apply is_empty_union2 in hclosed.
      + now apply Forall_tail in X.
      + apply Forall_inv in X. change (u@[sigma] :: us = u :: us).
        rewrite X; auto. unfold isClosed in hclosed |- *; cbn in *.
        rewrite set_fold_left in hclosed.
        rewrite empty_unitl in hclosed. now apply is_empty_union1 in hclosed.
  Qed.

  Lemma isClosed_subst_form :
    forall (F : Form) (sigma : Substitution var Term),
      isClosed F -> F@[sigma] = F.
  Proof using Type.
    intros. induction F; auto.
    - cbn. apply f_equal. induction l as [|t ts IHts]; auto.
      cbn. rewrite IHts.
      + unfold isClosed in H |- *; cbn in *.
        rewrite set_fold_left in H.
        rewrite empty_unitl in H. now apply is_empty_union2 in H.
      + rewrite isClosed_subst_term //.
        unfold isClosed in H |- *; cbn in *.
        rewrite set_fold_left in H.
        rewrite empty_unitl in H. now apply is_empty_union1 in H.
    - change (Neg (F@[sigma]) = Neg F). rewrite IHF //.
    - change (Or F1@[sigma] F2@[sigma] = Or F1 F2). rewrite IHF1.
      + unfold isClosed in H |- *; cbn in *.
        now apply is_empty_union1 in H.
      + rewrite IHF2 //.
        unfold isClosed in H |- *; cbn in *.
        now apply is_empty_union2 in H.
    - change (All F@[sigma] = All F). rewrite IHF //.
  Qed.
End isClosedLemmas.

(** ** Utils functions *)
Definition get_symbol {func var : Atom} (t : Term func var) : option func :=
  match t with
  | Bound _ | Free _ => None
  | Fun f _ => Some f
  end.

Definition is_free {func var : Atom} (t : Term func var) : bool :=
  match t with
  | Bound _ | Fun _ _ => false
  | Free _ => true
  end.

Lemma is_free_sound :
  forall {func var : Atom} (t : Term func var),
    is_free t = true -> exists (x : var), t = Free x.
Proof.
  intros ??? e; destruct t; try inversion e.
  now exists a.
Qed.

(** ** Function symbols *)
Section FunctionSymbols.
  Context {pred func var : Atom}.

  Let Term := Term func var.
  Let Form := Form pred func var.

  Class GetFunctSymbols (A : Type) :=
    function_symbols: A -> set_atom func.

  #[global] Instance GetFunctSymbols_term : GetFunctSymbols Term :=
    fix F (t : Term) : set_atom func :=
      match t with
      | Bound _ | Free _ => \{ \}
      | Fun f l => fold_left (fun s t => s \union (F t)) l (singleton f)
      end.

  #[global] Instance GetFunctSymbols_list {A : Type} `{GetFunctSymbols A} :
    GetFunctSymbols (list A) :=
    fun l => fold_left (fun s t => s \union (function_symbols t)) l \{\}.

  #[global] Instance GetFunctSymbols_form : GetFunctSymbols Form :=
    fix rec (F : Form) : set_atom func :=
      match F with
      | Bot => \{ \}
      | Pred _ l => function_symbols l
      | Neg F | All F => rec F
      | Or F1 F2 => rec F1 \union rec F2
      end.
End FunctionSymbols.

(** ** Concrete instances *)
Module ConcreteSyntaxInstances.
  Export AtomComputationalInstances.

  Definition Term := Term string string.
  Definition Form := Form string string string.

  (** *** Sets of formulas *)

  (** We instantiate [MSetsAVL] with formulas to get sets of formulas. *)

  (** First, we add a propositional & boolean function to compare terms. *)
  Fixpoint lt_term (t u : Term) : Prop :=
    match t, u with
    | Bound n, Bound m => n < m
    | Bound _, _ => True
    | Free x, Free y => OrderedString.lt x y
    | Free _, Bound _ => False
    | Free _, _ => True
    | Fun f lf, Fun g lg =>
        OrderedString.lt f g \/
          (f = g /\ lt_list lt_term lf lg)
    | Fun _ _, _ => False
    end.

  Fixpoint ltb_term (t u : Term) : bool :=
    match t, u with
    | Bound n, Bound m =>
        match PeanoNat.Nat.compare n m with
        | Lt => true
        | _ => false
        end
    | Bound _, _ => true
    | Free x, Free y =>
        match OrderedString.compare x y with
        | Lt => true
        | _ => false
        end
    | Free _, Bound _ => false
    | Free _, _ => true
    | Fun f lf, Fun g lg =>
        match OrderedString.compare f g with
        | Lt => true
        | Eq => ltb_list ltb_term lf lg
        | Gt => false
        end
    | Fun _ _, _ => false
    end.

  (** We have a reflection property on these two functions. *)
  Lemma ltb_term_lt_term :
    forall (t u : Term),
      ltb_term t u = true <-> lt_term t u.
  Proof.
    intro t; induction t using term_ind; destruct u; try easy; cbn.
    - destruct (PeanoNat.Nat.compare n n0) eqn:hcomp.
      + apply PeanoNat.Nat.compare_eq in hcomp; subst.
        split; intro contra.
        * inversion contra.
        * exfalso. now apply PeanoNat.Nat.lt_irrefl in contra.
      + split; auto; intros _. now apply Compare_dec.nat_compare_Lt_lt.
      + split; intro contra.
        * inversion contra.
        * exfalso. apply Compare_dec.nat_compare_Gt_gt in hcomp; lia.
    - have hspec := OrderedString.compare_spec a a0.
      destruct (OrderedString.compare a a0) eqn:hcomp.
      + inversion hspec; subst; cbn in *.
        split; intro contra.
        * inversion contra.
        * exfalso. now apply OrderedString.lt_strorder in contra.
      + inversion hspec; split; auto.
      + inversion hspec; split; intro contra.
        * inversion contra.
        * exfalso. have hcontr : OrderedString.lt a0 a0.
          { etransitivity; eauto. }
          now apply OrderedString.lt_strorder in hcontr.
    - have hspec := OrderedString.compare_spec f a.
      destruct (OrderedString.compare f a) eqn:hcomp.
      + inversion hspec; subst. split; intro h.
        * right; split; auto.
          erewrite <-ltb_list_lt_list; eauto.
          intros. eapply Ind.Forall_In in X; eauto.
        * destruct h.
          -- apply OrderedString.lt_strorder in H; auto.
          -- destruct H as [_ hlt].
             erewrite ltb_list_lt_list; eauto.
             intros; eapply Ind.Forall_In in X; eauto.
      + inversion hspec; split; auto.
      + inversion hspec; split.
        * intro contra; inversion contra.
        * intros [ hlt | [e hlt] ].
          -- have hlt' : OrderedString.lt a a by etransitivity; eauto.
             now apply OrderedString.lt_strorder in hlt'.
          -- subst. rewrite SetOfString_.SetOfXOrdProps.ME.compare_refl in hcomp; inversion hcomp.
  Qed.

  Lemma ltb_term_false :
    forall (t u : Term),
      ltb_term t u = false -> t <> u -> ltb_term u t = true.
  Proof.
    intro t; induction t using term_ind; intros ? hnlt ne; destruct u; cbn in *; try easy.
    - have hspec := OrderedNat.compare_spec n n0.
      destruct (PeanoNat.Nat.compare n n0); inversion hspec; try easy;
        destruct (PeanoNat.Nat.compare n0 n) eqn:hcomp; try easy.
      + exfalso; apply ne; now subst.
      + apply Compare_dec.nat_compare_Gt_gt in hcomp; lia.
      + apply PeanoNat.Nat.compare_eq in hcomp; lia.
      + apply Compare_dec.nat_compare_Gt_gt in hcomp; lia.
    - have hspec := OrderedString.compare_spec a a0.
      destruct (OrderedString.compare a a0); inversion hspec; try easy;
        destruct (OrderedString.compare a0 a) eqn:hcomp; try easy.
      + exfalso; apply ne; now subst.
      + rewrite SetOfString_.SetOfX_.Raw.MX.compare_gt_iff in hcomp; subst.
        now apply OrderedString.lt_strorder in hcomp.
      + apply SetOfString_.SetOfX_.Raw.MX.compare_eq in hcomp; subst.
        exfalso; now apply ne.
      + rewrite SetOfString_.SetOfX_.Raw.MX.compare_gt_iff in hcomp.
        have contra : OrderedString.lt a0 a0 by etransitivity; eauto.
        now apply OrderedString.lt_strorder in contra.
    - have hspec := OrderedString.compare_spec f a.
      destruct (OrderedString.compare f a); inversion hspec; try easy;
        destruct (OrderedString.compare a f) eqn:hcomp; try easy.
      + subst. have ne' : l <> l0.
        { intro; apply ne; now subst. }
        apply ltb_list_false; auto.
        intros; eapply Forall_In in X; eauto.
      + subst. rewrite SetOfString_.SetOfX_.Raw.MX.compare_refl in hcomp. inversion hcomp.
      + apply SetOfString_.SetOfX_.Raw.MX.compare_eq in hcomp; subst.
        now apply OrderedString.lt_strorder in H.
      + rewrite SetOfString_.SetOfX_.Raw.MX.compare_gt_iff in hcomp.
        have contra : OrderedString.lt a a by etransitivity; eauto.
        now apply OrderedString.lt_strorder in contra.
  Qed.

  (** We do the same for formulas. *)
  Fixpoint lt_form (F G : Form) : Prop :=
    match F, G with
    | Bot, Bot => False
    | Bot, _ => True
    | _, Bot => False

    | Pred p l, Pred p' l' =>
        OrderedString.lt p p' \/
          (p = p' /\ lt_list lt_term l l')
    | Pred _ _, _ => True

    | Neg F, Neg G => lt_form F G
    | Neg _, Pred _ _ => False
    | Neg _, _ => True

    | Or F1 F2, Or G1 G2 =>
        lt_form F1 G1 \/ (F1 = G1 /\ lt_form F2 G2)
    | Or _ _, All _ => True
    | Or _ _, _ => False

    | All F, All G => lt_form F G
    | All _, _ => False
    end.

  Fixpoint ltb_form (F G : Form) : bool :=
    match F, G with
    | Bot, Bot => false
    | Bot, _ => true
    | _, Bot => false

    | Pred p l, Pred p' l' =>
        match OrderedString.compare p p' with
        | Lt => true
        | Eq => ltb_list ltb_term l l'
        | Gt => false
        end
    | Pred _ _, _ => true

    | Neg F, Neg G => ltb_form F G
    | Neg _, Pred _ _ => false
    | Neg _, _ => true

    | Or F1 F2, Or G1 G2 =>
        ltb_form F1 G1 || (eqb F1 G1 && ltb_form F2 G2)
    | Or _ _, All _ => true
    | Or _ _, _ => false

    | All F, All G => ltb_form F G
    | All _, _ => false
    end.

  Lemma ltb_form_lt_form :
    forall (F G : Form),
      ltb_form F G = true <-> lt_form F G.
  Proof.
    intro F; induction F; intro G; destruct G; try easy; cbn.
    - have hspec := OrderedString.compare_spec a a0.
      destruct (OrderedString.compare a a0); inversion hspec.
      + subst; split.
        * intro hltb. right; split; auto.
          rewrite -ltb_list_lt_list; eauto.
          intros; apply ltb_term_lt_term.
        * intros [ contra | [ _ hlt ] ].
          -- now apply OrderedString.lt_strorder in contra.
          -- rewrite ltb_list_lt_list; eauto.
             intros; apply ltb_term_lt_term.
      + split; auto.
      + split.
        * intro contra; inversion contra.
        * intros [ hlt | [ e _ ] ].
          -- have hlt' : OrderedString.lt a0 a0 by etransitivity; eauto.
             now apply OrderedString.lt_strorder in hlt'.
          -- subst; now apply OrderedString.lt_strorder in H.
    - apply IHF.
    - split.
      + intros [hlt | [ e hlt ]%andb_prop ]%Bool.orb_prop.
        * left. rewrite -IHF1 //.
        * right; split.
          -- now rewrite -eqbIsEq.
          -- rewrite -IHF2 //.
      + intros [ hlt | [ e hlt ] ]; apply Bool.orb_true_intro.
        * left. now rewrite IHF1.
        * right; apply andb_true_intro; split.
          -- rewrite eqbIsEq //.
          -- rewrite IHF2 //.
    - apply IHF.
  Qed.

  Lemma ltb_form_false :
    forall (F G : Form),
      ltb_form F G = false -> F <> G -> ltb_form G F = true.
  Proof.
    intro F; induction F; intros ? hnlt ne; destruct G; cbn in *; try easy.
    - have hspec := OrderedString.compare_spec a a0.
      destruct (OrderedString.compare a a0); inversion hspec; cbn in *.
      + destruct (OrderedString.compare a0 a) eqn:hcomp; try easy.
        * apply ltb_list_false; auto.
          -- intros. apply ltb_term_false; auto.
          -- intro; subst; now apply ne.
        * subst. now rewrite SetOfString_.SetOfXOrdProps.ME.compare_refl in hcomp.
      + destruct (OrderedString.compare a0 a) eqn:hcomp; try easy.
      + destruct (OrderedString.compare a0 a) eqn:hcomp; try easy.
        * apply SetOfString_.SetOfX_.Raw.MX.compare_eq in hcomp; subst.
          inversion hspec. now apply OrderedString.lt_strorder in H0.
        * rewrite SetOfString_.SetOfX_.Raw.MX.compare_gt_iff in hcomp.
          have contra : OrderedString.lt a0 a0 by etransitivity; eauto.
          now apply OrderedString.lt_strorder in contra.
    - apply IHF; auto. congruence.
    - apply Bool.orb_false_elim in hnlt; destruct hnlt as [ne0 h].
      rewrite Bool.andb_false_iff in h; destruct h as [ne1 | ne1];
        apply Bool.orb_true_intro.
      + left. apply IHF1; auto. rewrite EqBool_neq //.
      + have [hF1 | [ e1 hF2 ] ] : F1 <> G1 \/ (F1 = G1 /\ F2 <> G2).
        { destruct (F1 == G1); auto.
          right. split; auto. intro. apply ne; now subst. }
        * left. apply IHF1; auto.
        * right. apply andb_true_intro; split.
          -- rewrite eqbIsEq //.
          -- apply IHF2; auto.
    - apply IHF; auto. congruence.
  Qed.

  (** Of course, [lt_term] and [lt_form] are both strict orders. *)
  #[global] Instance lt_term_strorder : StrictOrder lt_term.
  Proof.
    constructor.
    - intros t; induction t using term_ind; unfold complement; cbn; auto.
      + apply PeanoNat.Nat.lt_irrefl.
      + apply OrderedString.lt_strorder.
      + intros [ contra | [_ contra ] ].
        * now apply OrderedString.lt_strorder in contra.
        * induction l as [|t l' IHl']; auto.
          cbn in contra. destruct contra as [ contra | [ _ contra ] ].
          -- now apply Ind.Forall_inv in X.
          -- apply IHl'; auto. now apply Ind.Forall_tail in X.
    - intros t0 t1 t2 hlt0 hlt1. generalize dependent t2; generalize dependent t0.
      induction t1 using term_ind; intros t0 hlt0 t2 hlt1.
      + destruct t0, t2; auto.
        * cbn in *. etransitivity; eauto.
        * cbn in *. inversion hlt0.
        * cbn in *. inversion hlt0.
      + destruct t0, t2; auto.
        * cbn in *. inversion hlt1.
        * cbn in *. etransitivity; eauto.
        * cbn in *. inversion hlt0.
      + destruct t0, t2; auto.
        * cbn in *. inversion hlt1.
        * cbn in *. inversion hlt1.
        * cbn in *. destruct hlt0 as [ hlt0 | [ e0 hltlist0 ] ],
              hlt1 as [ hlt1 | [ e1 hltlist1 ] ].
          -- left; etransitivity; eauto.
          -- rewrite e1 in hlt0. now left.
          -- rewrite -e0 in hlt1. now left.
          -- right; split.
             ++ etransitivity; eauto.
             ++ clear e0 e1 a a0. generalize dependent l; generalize dependent l1;
                  induction l0 as [|t ts IHts];
                  intros l1 l IHl hltlist hltlist1.
                ** destruct l1.
                   --- destruct l; easy.
                   --- now cbn.
                ** destruct l1.
                   --- destruct l; easy.
                   --- destruct l; try easy.
                       cbn in *. destruct hltlist as [ hlt1 | [ e1 hlt ] ],
                           hltlist1 as [ hlt0 | [ e0 hltl1 ] ].
                       +++ apply Ind.Forall_inv in IHl; left; auto.
                       +++ left. now rewrite -e0.
                       +++ left. now rewrite e1.
                       +++ right; split.
                           *** etransitivity; eauto.
                           *** apply IHts with (l := l).
                               ---- now apply Ind.Forall_tail in IHl.
                               ---- auto.
                               ---- auto.
  Qed.

  #[global] Instance lt_strorder : StrictOrder lt_form.
  Proof.
    constructor.
    - intros F; induction F; unfold complement; cbn; auto.
      + intros [ contra | [_ contra] ].
        * now apply OrderedString.lt_strorder in contra.
        * induction l as [|t l' IHl'].
          -- now cbn in contra.
          -- cbn in contra; destruct contra.
             ++ now apply lt_term_strorder in H.
             ++ destruct H; auto.
      + intros [contra | [ _ contra ] ]; auto.
    - intros F G H hlt0 hlt1. generalize dependent H; generalize dependent F.
      induction G; intros F hlt0 H hlt1.
      + destruct F; easy.
      + destruct F, H; try easy.
        cbn in *. destruct hlt0 as [ hlt0 | [ e0 hltl0 ] ],
            hlt1 as [ hlt1 | [ e1 hltl1 ] ].
        * left; etransitivity; eauto.
        * left. now rewrite -e1.
        * left. now rewrite e0.
        * right; split.
          -- etransitivity; eauto.
          -- clear e0 e1 a a0 a1. generalize dependent l; generalize dependent l1;
               induction l0 as [|t ts IHts];
               intros l1 l hltlist hltlist1.
             ++ destruct l1, l; easy.
             ++ destruct l1, l; try easy.
                cbn in *. destruct hltlist as [ hlt1 | [ e1 hltl ] ],
                    hltlist1 as [ hlt0 | [ e0 hltl1 ] ].
                ** left; etransitivity; eauto.
                ** left; now rewrite -e0.
                ** left; now rewrite e1.
                ** right; split.
                   --- etransitivity; eauto.
                   --- eapply IHts; eauto.
      + destruct F, H; try easy.
        cbn in *; eapply IHG; eauto.
      + destruct F, H; try easy.
        cbn in *. destruct hlt0 as [ hlt1' | [ e1 hlt2 ] ],
            hlt1 as [ hlt | [ e hlt0 ] ].
        * left; eapply IHG1; eauto.
        * left; now rewrite -e.
        * left; now rewrite e1.
        * right; split.
          -- etransitivity; eauto.
          -- eapply IHG2; eauto.
      + destruct F, H; try easy.
        cbn in *; eapply IHG; eauto.
  Qed.

  (** We can now give an [OrderedType] structure for formulas. *)
  Module OrderedForm <: OrderedType.
    Definition t := Form.

    Definition eq : t -> t -> Prop := eq.

    Lemma eq_equiv : Equivalence eq.
    Proof. typeclasses eauto. Qed.

    Definition lt := lt_form.

    Lemma lt_strorder : StrictOrder lt.
    Proof. ltac:(typeclasses eauto). Qed.

    #[global] Instance lt_compat : Proper (eq ==> eq ==> iff) lt.
    Proof. intros F G ->; cbn. intros F H ->; cbn. reflexivity. Qed.

    Definition compare (F G : Form) : comparison :=
      if eqb F G then Eq
      else if ltb_form F G then Lt
           else Gt.

    Lemma compare_spec :
      forall (F G : Form), CompareSpec (F = G) (lt F G) (lt G F) (compare F G).
    Proof.
      intros ??. destruct (F == G).
      - subst. unfold compare. rewrite EqBool_refl. now constructor.
      - unfold compare. rewrite EqBool_neq in n; rewrite n.
        destruct (ltb_form F G) eqn:hlt.
        + constructor. unfold lt; rewrite -ltb_form_lt_form //.
        + constructor. unfold lt.
          rewrite -ltb_form_lt_form.
          apply ltb_form_false; auto.
          rewrite EqBool_neq //.
    Qed.

    Definition eq_dec (F G : Form) : { F = G } + { F <> G }.
    Proof. apply eq_dec_from_eq_bool; typeclasses eauto. Qed.
  End OrderedForm.

  (** Which means that we can give computational sets of formulas. *)
  Module FormSet := MSetAVL.Make OrderedForm.
End ConcreteSyntaxInstances.
