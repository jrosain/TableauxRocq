(** * Syntax: definition of a locally-nameless first-order logic syntax. *)

From Tableaux Require Export Prelude.All.

From Stdlib Require Import Structures.Orders.

(** ** First-order logic terms *)

Inductive Term_ {func var : Atom} : Type :=
| Bound : nat -> Term_
| Free  : var -> Term_
| Fun   : func -> list Term_ -> Term_.

Arguments Term_ : clear implicits.

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

  Fixpoint eqb_term (t u : Term_ func var) : bool :=
    match t, u with
    | Bound n, Bound m | Free n, Free m => eqb n m
    | Fun f l, Fun g l' =>
        eqb f g && forallb2 eqb_term l l'
    | _, _ => false
    end.

  Lemma eqb_term_eq :
    forall t u : Term_ func var, eqb_term t u = true <-> t = u.
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

  #[global] Instance EqBool_term : EqBool (Term_ func var).
  Proof.
    unshelve econstructor.
    - exact eqb_term.
    - exact eqb_term_eq.
  Defined.

  #[global] Instance eqDec_Term : EqDec (Term_ func var).
  Proof using Type. typeclasses eauto. Defined.
End DecEqTerms.

(** *** Opening and substitution for terms *)
Section OpeningSubstTerms.
  Context {func var : Atom} `{set_nat : set nat}.

  #[global] Instance opening_term : Opening (Term_ func var) (Term_ func var) :=
    fun n u =>
      fix F (t : Term_ func var) : Term_ func var :=
      match t with
      | Bound m => if eqb n m then u else t
      | Free  _ => t
      | Fun f l => Fun f (map F l)
      end.

  #[global] Instance bv_term : BV (Term_ func var) :=
    fix F (t : Term_ func var) : set_nat :=
      match t with
      | Bound m => singleton m
      | Free  _ => empty_set
      | Fun _ l => @bv_list set_nat _ F l
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
      | Bound _ => empty_set
      | Free  x => singleton x
      | Fun f l => fold_left (fun s t => s \union (F t)) l empty_set
      end.
End FVTerms.

(** ** Subterms *)
Fixpoint is_subterm {func var : Atom} (t u : Term_ func var) : Prop :=
  let fix f_ls (l : list (Term_ func var)) : Prop :=
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
  forall {func var : Atom} (t0 t1 t2 : Term_ func var),
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
  forall {func var : Atom} (t0 t1 t2 : Term_ func var),
    is_subterm t0 t2 -> ~is_subterm t1 t2 -> ~is_subterm t1 t0.
Proof.
  intros ????? hsub hnsub hsub'.
  have htrans := is_subterm_trans _ _ _ hsub' hsub.
  now apply hnsub.
Qed.
#[global] Opaque is_subterm.

(** ** Minimal first-order logic formulas *)
Inductive Form_ {pred func var : Atom} : Type :=
| Bot  : Form_
| Pred : pred -> list (Term_ func var) -> Form_
| Neg  : Form_ -> Form_
| Or   : Form_ -> Form_ -> Form_
| All  : Form_ -> Form_.

Arguments Form_ : clear implicits.

Definition is_positive_litteral {pred func var : Atom}
  (F : Form_ pred func var) : bool :=
  match F with
  | Pred _ _ => true
  | _ => false
  end.

Definition is_negative_litteral {pred func var : Atom}
  (F : Form_ pred func var) : bool :=
  match F with
  | Neg F => is_positive_litteral F
  | _ => false
  end.

Definition is_litteral  {pred func var : Atom}
  (F : Form_ pred func var) : bool :=
  is_positive_litteral F || is_negative_litteral F.

(** *** Decidable equality for formulas *)
Section DecEqForms.
  Context {pred func var : Atom}.
  Existing Instance eq_dec_list.

  Fixpoint eqb_form (F G : Form_ pred func var) : bool :=
    match F, G with
    | Bot, Bot => true
    | Pred p l, Pred p' l' => eqb p p' && eqb l l'
    | Neg F, Neg G => eqb_form F G
    | Or F1 F2, Or G1 G2 => eqb_form F1 G1 && eqb_form F2 G2
    | All F, All G => eqb_form F G
    | _, _ => false
    end.

  Lemma eqb_form_eq :
    forall F G : Form_ pred func var, eqb_form F G = true <-> F = G.
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

  #[global] Instance eqbool_form : EqBool (Form_ pred func var).
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

  Fixpoint opening_form_ (n : nat) (u : Term_ func var) (F : Form_ pred func var) :=
    match F with
    | Bot => Bot
    | Pred p l => Pred p (map (fun t => t{n \to u}) l)
    | Neg  F'  => Neg (opening_form_ n u F')
    | Or F1 F2 => Or (opening_form_ n u F1) (opening_form_ n u F2)
    | All  F'  => All (opening_form_ (n+1) u F')
    end.

  #[global] Instance opening_form : Opening (Term_ func var) (Form_ pred func var) :=
    opening_form_.

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

Section SubstOpeningLemmas.
  Context {pred func var : Atom} `{set_nat : set nat}.

  Let Term := Term_ func var.
  Let Form := Form_ pred func var.

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

  #[global] Instance fv_form : FV (Form_ pred func var) :=
    fix rec (F : Form_ pred func var) : set_var :=
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
  is_subformula : Form_ pred func var -> A -> Prop.

#[global] Instance HasSubformulas_list {pred func var : Atom} {A : Type}
  `{@HasSubformulas pred func var A} : HasSubformulas pred func var (list A) :=
  fix rec (F : Form_ pred func var) (l : list A) : Prop :=
    match l with
    | [] => False
    | G :: Gs => is_subformula F G \/ rec F Gs
    end.

#[global] Instance HasSubformulas_Form {pred func var : Atom} :
  HasSubformulas pred func var (Form_ pred func var) :=
  fun F G =>
    let fix rec (F G : Form_ pred func var) : Prop :=
      match G with
      | Neg G | All G => rec F G
      | Or G1 G2 => rec F G1 \/ rec F G2
      | _ => False
      end in
    F = G \/ rec F G.

Fixpoint ls_to_form {pred func var : Atom} (Gamma : list (Form_ pred func var))
  : Form_ pred func var :=
  match Gamma with
  | [] => Neg Bot
  | F :: Fs => Neg (Or (Neg F) (Neg (ls_to_form Fs)))
  end.

(** *** Closedness *)
Section isClosedLemmas.
  Context {pred func var : Atom} `{set_nat : set nat}.

  Let Term := Term_ func var.
  Let Form := Form_ pred func var.

  Lemma isClosedList_elem :
    forall (l : list Form) (F : Form),
      List.In F l -> isClosed l -> isClosed F.
  Proof using Type.
    intros ?? hin hclosed. induction l as [|G Gs IHGs]; inversion hin.
    - unfold isClosed in hclosed |- *; cbn in hclosed |- *.
      subst. now apply is_empty_union1 in hclosed.
    - apply IHGs; auto. now apply is_empty_union2 in hclosed.
  Qed.

  Lemma isClosedList_isClosedForm_isClosed :
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
Definition get_symbol {func var : Atom} (t : Term_ func var) : option func :=
  match t with
  | Bound _ | Free _ => None
  | Fun f _ => Some f
  end.

Definition is_free {func var : Atom} (t : Term_ func var) : bool :=
  match t with
  | Bound _ | Fun _ _ => false
  | Free _ => true
  end.

Lemma is_free_sound :
  forall {func var : Atom} (t : Term_ func var),
    is_free t = true -> exists (x : var), t = Free x.
Proof.
  intros ??? e; destruct t; try inversion e.
  now exists a.
Qed.

(** ** Function symbols *)
Section FunctionSymbols.
  Context {pred func var : Atom}.

  Let Term := Term_ func var.
  Let Form := Form_ pred func var.

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

  Definition Term := Term_ string string.
  Definition Form := Form_ string string string.
End ConcreteSyntaxInstances.
