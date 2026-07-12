(** * Syntax: definition of a locally-nameless first-order logic syntax. *)

From Tableaux Require Export Prelude.Core.

(** ** First-order logic terms *)

Inductive Term {func var : Type} `{isAtom func} `{isAtom var} : Type :=
| Bound : nat -> Term
| Free  : var -> Term
| Fun   : func -> list Term -> Term.

Arguments Term _ _ {_ _}.

(** *** Better induction principles for terms *)
Section TermInd.
  Context {func var : Type} `{isAtom func} `{isAtom var}.

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
    intros ?? hall. apply Pl; intros. eapply Forall_In in hall; eauto.
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
  Context {func var : Type} `{isAtom func} `{isAtom var}.

  Let Term := Term func var.

  Fixpoint eqb_term (t u : Term) : bool :=
    match t, u with
    | Bound n, Bound m | Free n, Free m => eqb n m
    | Fun f l, Fun g l' =>
        eqb f g && forallb2 eqb_term l l'
    | _, _ => false
    end.

  Lemma eqb_term_eq :
    forall t u : Term, eqb_term t u = true <-> t = u.
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

  #[global] Instance EqBool_term : EqBool Term.
  Proof.
    unshelve econstructor.
    - exact eqb_term.
    - exact eqb_term_eq.
  Defined.

  #[global] Instance eqDec_Term : EqDec Term.
  Proof using Type. tca. Defined.
End DecEqTerms.

(** *** Opening and substitution for terms *)
Section OpeningSubstTerms.
  Context {func var : Type} `{isAtom func} `{isAtom var} `{set_nat : set nat}.

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
  Context {func var : Type}  `{isAtom func} `{isAtom var}.

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
Fixpoint is_subterm {func var : Type} `{isAtom func} `{isAtom var} (t u : Term func var) : Prop :=
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
  forall {func var : Type} `{isAtom func} `{isAtom var} (t0 t1 t2 : Term func var),
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
  forall {func var : Type} `{isAtom func} `{isAtom var} (t0 t1 t2 : Term func var),
    is_subterm t0 t2 -> ~is_subterm t1 t2 -> ~is_subterm t1 t0.
Proof.
  intros ??????? hsub hnsub hsub'.
  have htrans := is_subterm_trans _ _ _ hsub' hsub.
  now apply hnsub.
Qed.
#[global] Opaque is_subterm.

(** ** Minimal first-order logic formulas *)
Inductive Form {pred func var : Type} `{isAtom pred} `{isAtom func} `{isAtom var} : Type :=
| Bot  : Form
| Pred : pred -> list (Term func var) -> Form
| Neg  : Form -> Form
| Or   : Form -> Form -> Form
| All  : Form -> Form.

Arguments Form _ _ _ {_ _ _}.

Definition is_positive_litteral {pred func var : Type} `{isAtom pred} `{isAtom func} `{isAtom var}
  (F : Form pred func var) : bool :=
  match F with
  | Pred _ _ => true
  | _ => false
  end.

Definition is_negative_litteral {pred func var : Type} `{isAtom pred} `{isAtom func} `{isAtom var}
  (F : Form pred func var) : bool :=
  match F with
  | Neg F => is_positive_litteral F
  | _ => false
  end.

Definition is_litteral  {pred func var : Type} `{isAtom pred} `{isAtom func} `{isAtom var}
  (F : Form pred func var) : bool :=
  is_positive_litteral F || is_negative_litteral F.

(** *** Decidable equality for formulas *)
Section DecEqForms.
  Context {pred func var : Type} `{isAtom pred} `{isAtom func} `{isAtom var}.
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
    - intro e. injection e => <-. rewrite IHF //.
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
  Context {pred func var : Type} `{isAtom pred} `{isAtom func} `{isAtom var} `{set_nat : set nat}.
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
  Context {pred func var : Type} `{isAtom pred} `{isAtom func} `{isAtom var} `{set_nat : set nat}.

  Let Term := Term func var.
  Let Form := Form pred func var.

  Lemma isLocallyClosed_Fun_isLocallyClosed_list :
    forall (f : func) (l : list Term),
      isLocallyClosed (Fun f l) ->
      Forall isLocallyClosed l.
  Proof using Type.
    intros ?? hclosed; apply In_Forall; intros t hin.
    red in hclosed; cbn in hclosed. red. apply is_empty_spec'.
    intros n hin'. apply (is_empty_spec n) in hclosed; auto.
    induction l; inversion hin; auto; cbn; rewrite union_spec.
    - right. apply IHl; auto. cbn in hclosed.
      now apply is_empty_union2 in hclosed.
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
    intros t; induction t using term_ind; intros ?? hclosed; cbn; auto.
    - red in hclosed; cbn in hclosed. apply (is_empty_spec n) in hclosed.
      + inversion hclosed.
      + now rewrite singleton_spec.
    - have hmap : map (varOpening x u) l = l.
      { apply isLocallyClosed_Fun_isLocallyClosed_list in hclosed.
        induction l as [|t ts IHts]; auto.
        cbn. rewrite IHts; auto.
        - now apply Forall_tail in X.
        - now apply Forall_tail in hclosed.
        - apply Forall_inv in X. rewrite X; auto.
          now apply Forall_inv in hclosed. }
      rewrite hmap //.
  Qed.

  Lemma isLocallyClosed_isLocallyClosed_subst :
    forall (t : Term) (sigma : Substitution var Term),
      isLocallyClosed t ->
      isLocallyClosed t@[sigma].
  Proof using Type.
    intros ?? hclosed. induction t using term_ind; auto; cbn.
    - apply sigma.
    - have hclosed1 : @isLocallyClosed set_nat _ _ (map (fun t => subst_term t sigma) l).
      { apply isLocallyClosed_Fun_isLocallyClosed_list in hclosed.
        induction l as [|t ts IHts]; cbn.
        - red. now cbn.
        - red. cbn. apply is_empty_spec'.
          + intros x; rewrite union_spec; intros [].
            * apply Forall_inv in X, hclosed.
              apply X in hclosed. red in hclosed.
              apply is_empty_spec with (x := x) in hclosed; auto.
            * apply Forall_tail in X, hclosed. specialize (IHts hclosed X).
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
  Context {pred func var : Type} `{isAtom pred} `{isAtom func} `{isAtom var}.

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

Class HasSubformulas
  (pred func var : Type) `{isAtom pred} `{isAtom func} `{isAtom var} (A : Type) :=
  is_subformula : Form pred func var -> A -> Prop.

#[global] Instance HasSubformulas_list {pred func var : Type} `{isAtom pred} `{isAtom func}
  `{isAtom var} {A : Type} `{!HasSubformulas pred func var A} :
  HasSubformulas pred func var (list A) :=
  fix rec (F : Form pred func var) (l : list A) : Prop :=
    match l with
    | [] => False
    | G :: Gs => is_subformula F G \/ rec F Gs
    end.

#[global] Instance HasSubformulas_Form {pred func var : Type} `{isAtom pred} `{isAtom func}
  `{isAtom var} : HasSubformulas pred func var (Form pred func var) :=
  fun F G =>
    let fix rec (F G : Form pred func var) : Prop :=
      match G with
      | Neg G | All G => rec F G
      | Or G1 G2 => rec F G1 \/ rec F G2
      | _ => False
      end in
    F = G \/ rec F G.

Fixpoint ls_to_form {pred func var : Type} `{isAtom pred} `{isAtom func} `{isAtom var}
  (Gamma : list (Form pred func var)) : Form pred func var :=
  match Gamma with
  | [] => Neg Bot
  | F :: Fs => Neg (Or (Neg F) (Neg (ls_to_form Fs)))
  end.

(** *** Closedness *)
Section isClosedLemmas.
  Context {pred func var : Type} `{isAtom pred} `{isAtom func} `{isAtom var} `{set_nat : set nat}.

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
    cbn in *. apply is_empty_spec'. intros ? hin.
    rewrite union_spec in hin. destruct hin.
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
    intros ?? hclosed. induction F; auto.
    - cbn. apply f_equal. induction l as [|t ts IHts]; auto.
      cbn. rewrite IHts.
      + unfold isClosed in hclosed |- *; cbn in *.
        rewrite set_fold_left in hclosed.
        rewrite empty_unitl in hclosed. now apply is_empty_union2 in hclosed.
      + rewrite isClosed_subst_term //.
        unfold isClosed in hclosed |- *; cbn in *.
        rewrite set_fold_left in hclosed.
        rewrite empty_unitl in hclosed. now apply is_empty_union1 in hclosed.
    - change (Neg (F@[sigma]) = Neg F). rewrite IHF //.
    - change (Or F1@[sigma] F2@[sigma] = Or F1 F2). rewrite IHF1.
      + unfold isClosed in hclosed |- *; cbn in *.
        now apply is_empty_union1 in hclosed.
      + rewrite IHF2 //.
        unfold isClosed in hclosed |- *; cbn in *.
        now apply is_empty_union2 in hclosed.
    - change (All F@[sigma] = All F). rewrite IHF //.
  Qed.
End isClosedLemmas.

(** ** Utils functions *)
Definition get_symbol {func var : Type} `{isAtom func} `{isAtom var} (t : Term func var) :
  option func :=
  match t with
  | Bound _ | Free _ => None
  | Fun f _ => Some f
  end.

Definition is_free {func var : Type} `{isAtom func} `{isAtom var} (t : Term func var) : bool :=
  match t with
  | Bound _ | Fun _ _ => false
  | Free _ => true
  end.

Lemma is_free_sound :
  forall {func var : Type} `{isAtom func} `{isAtom var} (t : Term func var),
    is_free t = true -> exists (x : var), t = Free x.
Proof.
  intros ????? e; destruct t; try inversion e.
  now exists v.
Qed.

(** ** Function symbols *)
Section FunctionSymbols.
  Context {pred func var : Type} `{!isAtom pred} `{!isAtom func} `{!isAtom var}.

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

  #[global] Instance GetFunctSymbols_opt {A : Type} `{GetFunctSymbols A} :
    GetFunctSymbols (option A) :=
    fun o => match o with
          | None => \{\}
          | Some x => function_symbols x
          end.

  Lemma GetFunctSymbols_in :
    forall {A : Type} `{GetFunctSymbols A} (x : A) (l : list A) (f : func),
      List.In x l -> set_in f (function_symbols x) ->
      set_in f (function_symbols l).
  Proof using Type.
    intros ????? hin1 hin2; induction l as [|y ys IHys]; inversion hin1.
    - subst; cbn. rewrite set_fold_left union_spec; left; rewrite union_spec; now right.
    - cbn. rewrite set_fold_left union_spec; right; now apply IHys.
  Qed.

  #[global] Instance GetFunctSymbols_form : GetFunctSymbols Form :=
    fix rec (F : Form) : set_atom func :=
      match F with
      | Bot => \{ \}
      | Pred _ l => function_symbols l
      | Neg F | All F => rec F
      | Or F1 F2 => rec F1 \union rec F2
      end.

  Lemma function_symbols_opening_terms :
    forall (t u : Term) (n : nat),
      function_symbols (u{n \to t}) \subseteq
        function_symbols u \union function_symbols t.
  Proof using Type.
    intros t u; induction u using term_ind; intros m.
    - cbn; rewrite -match_eq_dec_eq_bool; destruct (m == n).
      + rewrite empty_unitl //.
      + now intros f contra%empty_spec.
    - now intros f contra%empty_spec.
    - intros g hin; cbn in hin |- *.
      rewrite set_fold_left union_spec in hin; destruct hin as [e | hin].
      + apply singleton_spec in e; rewrite e.
        rewrite set_fold_left !union_spec; repeat left.
        now rewrite singleton_spec.
      + rewrite set_fold_left union_assoc !union_spec.
        right. rewrite -union_spec. induction l as [|w ws IHws]; auto.
        * cbn in hin |- *. now apply empty_spec in hin.
        * cbn in hin |- *; rewrite set_fold_left empty_unitl in hin.
          rewrite union_spec in hin; destruct hin as [hw | hws].
          -- apply Forall_inv in X; apply X in hw; rewrite union_spec in hw;
               destruct hw as [hw | ht].
             ++ rewrite set_fold_left empty_unitl !union_spec.
                now repeat left.
             ++ rewrite set_fold_left empty_unitl !union_spec.
                now right.
          -- apply Forall_tail in X. specialize (IHws X hws).
             rewrite set_fold_left empty_unitl !union_spec.
             rewrite union_spec in IHws; destruct IHws as [hws' | ht].
             ++ now left; right.
             ++ now right.
  Qed.

  Lemma function_symbols_opening :
    forall (F : Form) (t : Term) (n : nat),
      function_symbols (F{n \to t}) \subseteq
        function_symbols F \union function_symbols t.
  Proof using Type.
    intros F; induction F; intros t n.
    - now intros f contra%empty_spec.
    - cbn; intros f hin. induction l as [|u us IHus].
      + now apply empty_spec in hin.
      + cbn in hin; rewrite set_fold_left empty_unitl !union_spec in hin.
        destruct hin as [hu | hus].
        * cbn; rewrite set_fold_left empty_unitl !union_spec.
          apply function_symbols_opening_terms in hu; rewrite union_spec in hu;
            destruct hu as [hu | ht].
          -- now repeat left.
          -- now right.
        * cbn; rewrite set_fold_left empty_unitl !union_spec.
          specialize (IHus hus). rewrite union_spec in IHus; destruct IHus as [hus' | ht].
          -- now left; right.
          -- now right.
    - intros; now apply IHF.
    - intros f hin; cbn in hin |- *; rewrite !union_spec in hin |- *.
      destruct hin as [hF1 | hF2].
      + apply IHF1 in hF1; rewrite union_spec in hF1; destruct hF1 as [hF1 | ht].
        * cbn in hF1; now repeat left.
        * now right.
      + apply IHF2 in hF2; rewrite union_spec in hF2; destruct hF2 as [hF2 | ht].
        * cbn in hF2; now left; right.
        * now right.
    - now apply IHF.
  Qed.

  Lemma function_symbols_opening_terms' :
    forall (t u : Term) (n : nat),
      function_symbols u \subseteq function_symbols (u{n \to t}).
  Proof using Type.
    intros t u; induction u using term_ind; intros m.
    - now intros f contra%empty_spec.
    - now intros f contra%empty_spec.
    - intros g hin; cbn in hin |- *. rewrite set_fold_left union_spec in hin.
      rewrite set_fold_left union_spec. destruct hin as [hf | hus].
      + now left.
      + right. induction l as [|u us IHus]; auto.
        cbn in hus |- *. rewrite set_fold_left union_spec empty_unitl in hus.
        rewrite set_fold_left union_spec empty_unitl. destruct hus as [hu | hus].
        * left. apply Forall_inv in X; now apply X.
        * right; apply IHus; auto. now apply Forall_tail in X.
  Qed.

  Lemma function_symbols_opening_form' :
    forall (F : Form) (t : Term) (n : nat),
      function_symbols F \subseteq
        function_symbols (F{n \to t}).
  Proof using Type.
    intros F; induction F; intros t n.
    - now intros f contra%empty_spec.
    - cbn; intros f hin. induction l as [|u us IHus].
      + now apply empty_spec in hin.
      + cbn in hin; rewrite set_fold_left empty_unitl !union_spec in hin.
        destruct hin as [hu | hus].
        * cbn; rewrite set_fold_left empty_unitl !union_spec.
          eapply function_symbols_opening_terms' in hu; left; eassumption.
        * cbn; rewrite set_fold_left empty_unitl !union_spec. right.
          now apply IHus.
    - intros; now apply IHF.
    - intros f hin; cbn in hin |- *; rewrite !union_spec in hin |- *.
      destruct hin as [hF1 | hF2].
      + eapply IHF1 in hF1; left; eassumption.
      + eapply IHF2 in hF2; right; eassumption.
    - now apply IHF.
  Qed.

  Lemma function_symbols_opening_all_free :
    forall (F : Form) (n : nat) (x : var),
      function_symbols (F{n \to Free x}) = function_symbols (All F).
  Proof using Type.
    intros ???. apply set_ext; intros f; split; intros hin.
    - cbn. rewrite <-empty_unitr.
      change \{\} with (function_symbols (Free x)).
      eapply function_symbols_opening; eauto.
    - now apply function_symbols_opening_form'.
  Qed.
End FunctionSymbols.

(** A concrete instance of the syntax using string atoms can be found in SyntaxInstance.v *)
