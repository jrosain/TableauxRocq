(** * ATPCompat: helper functions and lemmas for easy ATP output *)

From Corelib Require Import Classes.RelationClasses.

From Tableaux Require Import Syntax.
From Tableaux Require Import Semantics.
From Tableaux Require Import Proofs.
From Tableaux Require Import Skolemization.

(** In this file, we define:
      1. a syntax using [string]s for bound variable, in order to make it easy to
         output formulas from ATPs,
      2. semantics for this syntax,
      3. a translation function from this syntax to the internal one,
      4. a proof that the two syntaxes are semantically equivalent,
      5. helper functions for transforming finite substitutions into internal substitutions,
      6. helper lemmas to build a tableau more easily *)

Section ESyntax.
  Inductive ETerm :=
  | EVar : string -> ETerm
  | EFun : string -> list ETerm -> ETerm.

  Inductive EForm :=
  | ETop  : EForm
  | EBot  : EForm
  | EPred : string -> list ETerm -> EForm
  | ENeg  : EForm -> EForm
  | EOr   : EForm -> EForm -> EForm
  | EAnd  : EForm -> EForm -> EForm
  | EImp  : EForm -> EForm -> EForm
  | EEqu  : EForm -> EForm -> EForm
  | EEx   : string -> EForm -> EForm
  | EAll  : string -> EForm -> EForm.
End ESyntax.

Section ETermInd.
  Definition eterm_rect (P : ETerm -> Type) (Pb : forall (x : string), P (EVar x))
    (Pl : forall (f : string) (l : list ETerm), Forall P l -> P (EFun f l)) :
    forall (t : ETerm), P t :=
    fix F (t : ETerm) : P t :=
      let fix F_list (l : list ETerm) : Forall P l :=
        match l with
        | [] => Forall_nil P
        | x :: xs => Forall_cons P x xs (F_list xs) (F x)
        end in
      match t with
      | EVar x => Pb x
      | EFun f l => Pl f l (F_list l)
      end.

  Definition eterm_ind (P : ETerm -> Prop) (Pb : forall (x : string), P (EVar x))
    (Pl : forall (f : string) (l : list ETerm), Forall P l -> P (EFun f l)) :
    forall (t : ETerm), P t :=
    eterm_rect P Pb Pl.

  Definition eterm_rect' (P : ETerm -> Type) (Pb : forall (x : string), P (EVar x))
    (Pl : forall (f : string) (l : list ETerm),
        (forall (t : ETerm), In t l -> P t) -> P (EFun f l)) :
    forall (t : ETerm), P t.
  Proof.
    apply eterm_rect; auto.
    intros ?? H. apply Pl; intros. eapply Forall_In in H; eauto.
  Defined.

  Definition eterm_ind' (P : ETerm -> Prop) (Pb : forall (x : string), P (EVar x))
    (Pl : forall (f : string) (l : list ETerm),
        (forall (t : ETerm), In t l -> P t) -> P (EFun f l)) :
    forall (t : ETerm), P t :=
    eterm_rect' P Pb Pl.
End ETermInd.

Section ESemantics.
  Definition interpret_eterm {M : Model string string} : env M string -> ETerm -> M :=
    fun rho =>
      fix F (t : ETerm) : M :=
        match t with
        | EVar x   => option_get non_empty (rho x)
        | EFun f l => interp_func f (map F l)
        end.

  Definition interpret_eform (M : Model string string) : env M string -> EForm -> Prop :=
    fix rec (rho : env M string) (F : EForm) : Prop :=
      match F with
      | ETop      => True
      | EBot      => False
      | EPred p l => interp_pred p (map (interpret_eterm rho) l)
      | ENeg F    => ~ (rec rho F)
      | EOr F G   => rec rho F \/ rec rho G
      | EAnd F G  => rec rho F \/ rec rho G
      | EImp F G  => ~(rec rho F) \/ rec rho G
      | EEqu F G  => rec rho F <-> rec rho G
      | EEx x F   => exists (v : M), rec (fun y => match eqDec x y with
                                          | left _ => Some v
                                          | right _ => rho y
                                          end) F
      | EAll x F   => forall (v : M), rec (fun y => match eqDec x y with
                                           | left _ => Some v
                                           | right _ => rho y
                                           end) F
      end.
End ESemantics.

Section ESyntaxTranslation.
  Fixpoint fv_eterm (t : ETerm) : SetOfString :=
    match t with
    | EVar x   => singleton x
    | EFun f l => fold_left (fun s t => s \union (fv_eterm t)) l (empty_set string)
    end.

  Fixpoint fv_eform (F : EForm) : SetOfString :=
    match F with
    | EBot | ETop => empty_set string
    | EPred p l => fold_left (fun s t => s \union (fv_eterm t)) l (empty_set string)
    | ENeg F => fv_eform F
    | EOr F G | EAnd F G | EImp F G | EEqu F G => (fv_eform F) \union (fv_eform G)
    | EEx x F | EAll x F => remove x (fv_eform F)
    end.

  Definition WellScoped (F : EForm) := is_empty (fv_eform F).

  Fixpoint index_of {A : Type} `{EqDec A} (x : A) (l : list A) : option nat :=
    match l with
    | [] => None
    | y :: ys => match eqDec x y with
               | left _ => Some 0
               | right _ => bind (index_of x ys) (fun n => Some (S n))
               end
    end.

  Fixpoint translate_ETerm (m : list string) (t : ETerm) : Term :=
    match t with
    | EVar x   =>
        match index_of x m with
        | None => Free x
        | Some n => Bound n
        end
    | EFun f l => Fun f (map (translate_ETerm m) l)
    end.

  Definition translate_EForm : EForm -> Form :=
    let fix rec (m : list string) (F : EForm) : Form :=
      match F with
      | EBot => Bot
      | ETop => Neg Bot
      | EPred f l => Pred f (map (translate_ETerm m) l)
      | ENeg F => Neg (rec m F)
      | EOr F G => Or (rec m F) (rec m G)
      | EAnd F G => Neg (Or (Neg (rec m F)) (Neg (rec m G)))
      | EImp F G => Or (Neg (rec m F)) (rec m G)
      | EEqu F G => Neg (Or (Neg (Or (Neg (rec m F)) (rec m G))) (Neg (Or (Neg (rec m G)) (rec m F))))
      | EEx x F  => Neg (All (Neg (rec (x :: m) F)))
      | EAll x F => All (rec (x :: m) F)
      end in
    rec [].

  Lemma WellScoped_no_fv_eterm :
    forall (t : ETerm), is_empty (fv_eterm t) -> is_empty (@fv string _ _ (translate_ETerm [] t)).
  Proof.
    intros t hscope; induction t using eterm_rect'; cbn in *.
    - assumption.
    - induction l.
      + now cbn in *.
      + cbn in *. Admitted.

  Lemma WellScoped_no_fv :
    forall (F : EForm), WellScoped F -> is_empty (@fv string _ _ (translate_EForm F)).
  Proof.
    intros F hscope; induction F.
    - cbn; apply is_empty_spec.
    - cbn; apply is_empty_spec.
    - cbn in *. admit.
    - cbn in *. now apply IHF.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
  Admitted.
End ESyntaxTranslation.

Coercion translate_EForm : EForm >-> Form.
Notation "[[ F ]]" := (translate_EForm F).

(* TODO: syntax corresponds *)

(** Helpers for [hasTableau] with the full first-order free-variable tableau calculus. *)
Section HasTableauLemmas.
  Context (sko : Skolemization).

  Lemma con_nth_in :
    forall (Gamma : Con) (i : nat) (F : Form),
      con_nth Gamma i = Some F -> F \in Gamma.
  Proof using Type.
    intros ??? e. generalize dependent i. induction Gamma as [|x xs IHxs]; cbn in *;
      intros i e.
    - rewrite nth_error_nil in e; inversion e.
    - destruct i.
      + rewrite nth_error_cons_0 in e.
        injection e => e'. now right.
      + left. apply IHxs with (i := i).
        now rewrite nth_error_cons_succ in e.
  Qed.

  Lemma hasTableauBot :
    forall (Gamma : Con) (sigma : Substitution string Term) (S Sf : SetOfString) (i : nat),
      con_nth Gamma i = Some [[ EBot ]] -> hasTableau_ sko Gamma S Sf sigma.
  Proof using Type.
    intros ????? e. apply hasTableauBot.
    eapply con_nth_in; eauto.
  Qed.

  Lemma hasTableauNegTop :
    forall (Gamma : Con) (sigma : Substitution string Term) (S Sf : SetOfString) (i : nat),
      con_nth Gamma i = Some [[ ENeg ETop ]] -> hasTableau_ sko Gamma S Sf sigma.
  Proof using Type.
    intros ????? e. eapply hasTableauNegNeg.
    - cbn in e. eapply con_nth_in; eauto.
    - unshelve eapply hasTableauBot; cbn. exact 0. now cbn.
  Qed.

  Lemma hasTableauContr :
    forall (Gamma : Con) (sigma : Substitution string Term) (S Sf : SetOfString) (i j : nat) (F G : EForm),
      con_nth Gamma i = Some [[ F ]] -> con_nth Gamma j = Some [[ G ]] -> [[ ENeg F ]]@[sigma] = [[ G ]]@[sigma] ->
      hasTableau_ sko Gamma S Sf sigma.
  Proof using Type.
    intros ????????? e0 e1.
    eapply hasTableauContr; cbn in *.
    - eapply con_nth_in. exact H.
    - eapply con_nth_in. exact e0.
    - assumption.
  Qed.

  Lemma hasTableauNegNeg :
    forall (Gamma : Con) (sigma : Substitution string Term) (S Sf : SetOfString) (i : nat) (F : EForm),
      con_nth Gamma i = Some [[ ENeg (ENeg F) ]] ->
      hasTableau_ sko (Gamma ,, [[ F ]]) S Sf sigma ->
      hasTableau_ sko Gamma S Sf sigma.
  Proof using Type.
    intros ?????? e htab. eapply hasTableauNegNeg; eauto.
    cbn in e; eapply con_nth_in; eauto.
  Qed.

  Lemma hasTableauAnd :
    forall (Gamma : Con) (sigma : Substitution string Term) (S Sf : SetOfString) (i : nat) (F G : EForm),
      con_nth Gamma i = Some [[ EAnd F G ]] ->
      hasTableau_ sko (Gamma ,, Neg (Neg [[ F ]]) ,, Neg (Neg [[ G ]]) ,, [[ F ]] ,, [[ G ]]) S Sf sigma ->
      hasTableau_ sko Gamma S Sf sigma.
  Proof using Type.
    intros ??????? e htab. eapply hasTableauNegOr.
    - cbn in e. eapply con_nth_in; eauto.
    - unshelve eapply hasTableauNegNeg.
      + exact 1.
      + exact F.
      + now cbn.
      + unshelve eapply hasTableauNegNeg.
        * exact 1.
        * exact G.
        * reflexivity.
        * assumption.
  Qed.

  Lemma hasTableauNegOr :
    forall (Gamma : Con) (sigma : Substitution string Term) (S Sf : SetOfString) (i : nat) (F G : EForm),
      con_nth Gamma i = Some [[ ENeg (EOr F G) ]] ->
      hasTableau_ sko (Gamma ,, Neg [[ F ]] ,, Neg [[ G ]]) S Sf sigma ->
      hasTableau_ sko Gamma S Sf sigma.
  Proof using Type.
    intros ??????? e htab. eapply hasTableauNegOr.
    - cbn in e; eapply con_nth_in; eauto.
    - assumption.
  Qed.

  Lemma hasTableauNegImp :
    forall (Gamma : Con) (sigma : Substitution string Term) (S Sf : SetOfString) (i : nat) (F G : EForm),
      con_nth Gamma i = Some [[ ENeg (EImp F G) ]] ->
      hasTableau_ sko (Gamma ,, Neg (Neg [[ F ]]) ,, Neg [[ G ]] ,, [[ F ]]) S Sf sigma ->
      hasTableau_ sko Gamma S Sf sigma.
  Proof using Type.
    intros ??????? e htab. eapply hasTableauNegOr.
    - cbn in *; change (Neg [[ F ]]) with ([[ ENeg F ]]) in e; eauto.
    - unshelve eapply hasTableauNegNeg.
      + exact 1.
      + exact F.
      + now cbn.
      + assumption.
  Qed.

  Lemma hasTableauOr :
    forall (Gamma : Con) (sigma : Substitution string Term) (S1 S2 Sf1 Sf2 : SetOfString) (i : nat) (F G : EForm),
      con_nth Gamma i = Some [[ EOr F G ]] ->
      hasTableau_ sko (Gamma ,, [[ F ]]) S1 Sf1 sigma ->
      hasTableau_ sko (Gamma ,, [[ G ]]) S2 Sf2 sigma -> disjoint S1 S2 -> disjoint Sf1 Sf2 ->
      hasTableau_ sko Gamma (S1 \union S2) (Sf1 \union Sf2) sigma.
  Proof using Type.
    intros ????????? e htab1 htab2. eapply hasTableauOr.
    1: cbn in *; eapply con_nth_in; eauto.
    all: assumption.
  Qed.

  Lemma hasTableauImp :
    forall (Gamma : Con) (sigma : Substitution string Term) (S1 S2 Sf1 Sf2 : SetOfString) (i : nat) (F G : EForm),
      con_nth Gamma i = Some [[ EImp F G ]] ->
      hasTableau_ sko (Gamma ,, [[ ENeg F ]]) S1 Sf1 sigma ->
      hasTableau_ sko (Gamma ,, [[ G ]]) S2 Sf2 sigma -> disjoint S1 S2 -> disjoint Sf1 Sf2 ->
      hasTableau_ sko Gamma (S1 \union S2) (Sf1 \union Sf2) sigma.
  Proof using Type.
    intros ????????? e htab1 htab2. eapply hasTableauOr.
    1: cbn in *; change (Neg [[ F ]]) with ([[ ENeg F ]]) in e; eassumption.
    all: assumption.
  Qed.

  Lemma hasTableauNegAnd :
    forall (Gamma : Con) (sigma : Substitution string Term) (S1 S2 Sf1 Sf2 : SetOfString) (i : nat) (F G : EForm),
      con_nth Gamma i = Some [[ ENeg (EAnd F G) ]] ->
      hasTableau_ sko (Gamma ,, (Or [[ ENeg F ]] [[ ENeg G ]]) ,, [[ ENeg F ]]) S1 Sf1 sigma ->
      hasTableau_ sko (Gamma ,, (Or [[ ENeg F ]] [[ ENeg G ]]) ,, [[ ENeg G ]]) S2 Sf2 sigma ->
      disjoint S1 S2 -> disjoint Sf1 Sf2 ->
      hasTableau_ sko Gamma (S1 \union S2) (Sf1 \union Sf2) sigma.
  Proof using Type.
    intros ????????? e htab1 htab2 hdisjoint1 hdisjoint2. eapply hasTableauNegNeg.
    - cbn in *. change (Or (Neg [[ F ]]) (Neg [[ G ]])) with ([[ EOr (ENeg F) (ENeg G) ]]) in e.
      eassumption.
    - unshelve eapply hasTableauOr.
      1: exact 0.
      3: reflexivity.
      all: assumption.
  Qed.

  (* TODO: equ, neg equ, ex, neg ex, all, neg all *)

  (* TODO: replace before translation *)
  Lemma hasTableauAll :
    forall (Gamma : Con) (sigma : Substitution string Term) (S Sf : SetOfString) (i : nat) (F : EForm)
      (x : string) (y : string),
      con_nth Gamma i = Some [[ EAll x F ]] -> isFresh y S ->
      hasTableau_ sko (Gamma ,, [[ F ]]{0 \to Free y}) S Sf sigma ->
      hasTableau_ sko Gamma (add y S) Sf sigma.
  Proof.
    intros ???????? e hfresh htab. eapply hasTableauAll.
    - cbn in e. eapply con_nth_in; eauto.
    - assumption.
    - admit.
  Admitted.

End HasTableauLemmas.
