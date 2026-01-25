(** * ATPCompat: helper functions and lemmas for easy ATP output *)

From Corelib Require Import Classes.RelationClasses.

From Stdlib Require Import Classical.
From Stdlib Require Import Lia.

From Tableaux Require Import Syntax.
From Tableaux Require Import Semantics.
From Tableaux Require Import Proofs.
From Tableaux Require Import Skolemization.

Export ConcreteProofInstances.

(** In this file, we define:
      1. a syntax using [string]s for bound variable, in order to make it easy to
         output formulas from ATPs,
      2. semantics for this syntax,
      3. a translation function from this syntax to the internal one,
      4. a proof that the two syntaxes are semantically equivalent,
      5. helper functions for transforming finite substitutions into internal substitutions,
      6. helper lemmas to build a tableau more easily
      7. tactics to simplify extended syntax stuff & solve set-related stuff *)

(** ** 1. Extended syntax *)
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

(** ** 2. Extended semantics **)
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
      | EAnd F G  => rec rho F /\ rec rho G
      | EImp F G  => rec rho F -> rec rho G
      | EEqu F G  => rec rho F <-> rec rho G
      | EEx x F   =>
          exists (v : M),
            rec (fun y => if eqb x y then Some v else rho y) F
      | EAll x F   =>
          forall (v : M),
            rec (fun y => if eqb x y then Some v else rho y) F
      end.

  Definition is_evalid (F : EForm) : Prop :=
    forall (M : Model string string), interpret_eform M (empty_env M string) F.
End ESemantics.

(** ** 3. Syntax translation *)
Section ESyntaxTranslation.
  Fixpoint fv_eterm (t : ETerm) : SetOfString :=
    match t with
    | EVar x   => singleton x
    | EFun f l => fold_left (fun s t => s \union (fv_eterm t)) l empty_set
    end.

  Fixpoint bv_eform (F : EForm) : SetOfString :=
    match F with
    | EBot | ETop | EPred _ _ => empty_set
    | ENeg F => bv_eform F
    | EOr F G | EAnd F G | EImp F G | EEqu F G => (bv_eform F) \union (bv_eform G)
    | EEx x F | EAll x F => add x (bv_eform F)
    end.

  Section IndexOf.
    Context {A : Type} `{EqBool A}.

    Fixpoint index_of (x : A) (l : list A) : option nat :=
    match l with
    | [] => None
    | y :: ys => if eqb x y
               then Some 0
               else bind (index_of x ys) (fun n => Some (S n))
    end.

    Lemma index_of_spec :
      forall (x : A) (n : nat) (l : list A),
        index_of x l = Some n -> nth_error l n = Some x.
    Proof using Type.
      intros ??? e. generalize dependent n. induction l as [|y ys IHys].
      - intros ? e. inversion e.
      - intros ? e; cbn in *. rewrite -match_eq_dec_eq_bool in e.
        destruct eqDec; cbn.
        + injection e => <-. cbn. rewrite e0 //.
        + destruct (index_of x ys) eqn:eid; cbn in *.
          * injection e => en. rewrite -en; cbn.
            now apply IHys.
          * inversion e.
    Qed.

    Lemma index_of_inj :
      forall (x y : A) (n : nat) (l : list A),
        index_of x l = Some n -> index_of y l = Some n -> x = y.
    Proof using Type.
      intros ???? ex ey. generalize dependent n; induction l as [|z zs IHzs]; intros n ex ey.
      - inversion ex.
      - cbn in *. rewrite -!match_eq_dec_eq_bool in ex, ey.
        repeat (destruct eqDec; cbn in * ).
        + now rewrite e0.
        + rewrite -ex in ey. destruct (index_of y zs); cbn in *.
          * injection ey => contra; inversion contra.
          * inversion ey.
        + rewrite -ey in ex. destruct (index_of x zs); cbn in *.
          * injection ex => contra; inversion contra.
          * inversion ex.
        + destruct n.
          * destruct (index_of x zs), (index_of y zs); cbn in *.
            -- injection ex => contra; inversion contra.
            -- inversion ey.
            -- inversion ex.
            -- inversion ex.
          * destruct (index_of x zs), (index_of y zs); cbn in *.
            -- apply (IHzs n); f_equal.
               ++ apply eq_add_S. now injection ex => ->.
               ++ apply eq_add_S. now injection ey => ->.
            -- inversion ey.
            -- inversion ex.
            -- inversion ex.
    Qed.

    Lemma In_index_of :
      forall (x : A) (l : list A), In x l -> exists (n : nat), index_of x l = Some n.
    Proof using Type.
      intros x l hin. induction l as [|y ys IHys].
      - inversion hin.
      - cbn. rewrite -match_eq_dec_eq_bool.
        destruct (x == y).
        + now exists 0.
        + destruct hin as [hin | e].
          * apply IHys in hin. destruct hin as [m e].
            exists (S m). destruct (index_of x ys).
            -- cbn. injection e => -> //.
            -- inversion e.
          * exfalso. now apply n.
    Qed.

    Lemma index_of_In :
      forall (x : A) (l : list A) (n : nat), index_of x l = Some n -> In x l.
    Proof using Type.
      intros ??. induction l as [|y ys IHys].
      - intros ? contra; inversion contra.
      - intros ? e; cbn in *. rewrite -match_eq_dec_eq_bool in e. destruct (x == y).
        + now right.
        + left. destruct (index_of x ys); cbn in *.
          * injection e => e'. destruct n.
            -- inversion e'.
            -- apply (IHys n). f_equal. now apply eq_add_S.
          * inversion e.
    Qed.

    Lemma index_of_cons :
      forall (x y : A) (l : list A) (n : nat),
        index_of x (y :: l) = Some (S n) -> index_of x l = Some n.
    Proof using Type.
      intros ???? e; cbn in *. rewrite -match_eq_dec_eq_bool in e.
      destruct (x == y); cbn.
      - injection e => contra. inversion contra.
      - destruct (index_of x l); cbn in *.
        + f_equal. apply eq_add_S. now injection e => ->.
        + inversion e.
    Qed.

    Lemma index_of_cons' :
      forall (x y : A) (l : list A) (n : nat),
        x <> y -> index_of x l = Some n -> index_of x (y :: l) = Some (S n).
    Proof using Type.
      intros ???? e0 e; cbn in *. rewrite -match_eq_dec_eq_bool.
      destruct (x == y); cbn.
      - congruence.
      - destruct (index_of x l); cbn in *.
        + f_equal. apply eq_S. injection e => -> //.
        + inversion e.
    Qed.

    Lemma index_of_nth :
      forall (x : A) (l1 l2 : list A),
        (forall (n : nat), n < min #|l1| #|l2| -> nth_error l1 n = nth_error l2 n) ->
        In x l1 -> In x l2 ->
        index_of x l1 = index_of x l2.
    Proof using Type.
      intros ??. induction l1 as [|y ys IHys].
      - intros []; auto. intros _ contra; inversion contra.
      - intros [].
        + intros _ _ contra; inversion contra.
        + intros h hin hin'. cbn. rewrite -!match_eq_dec_eq_bool.
          destruct (x == y), (x == a); auto.
          * specialize (h 0). cbn in h. specialize (h ltac:(lia)).
            injection h => contra; congruence.
          * specialize (h 0). cbn in h. specialize (h ltac:(lia)).
            injection h => contra; congruence.
          * rewrite (IHys l); auto.
            -- intros. specialize (h (S n1)). cbn in h. now specialize (h ltac:(lia)).
            -- destruct hin; congruence.
            -- destruct hin'; congruence.
    Qed.
  End IndexOf.

  Fixpoint translate_ETerm (m : list string) (t : ETerm) : Term :=
    match t with
    | EVar x   =>
        match index_of x m with
        | None => Free x
        | Some n => Bound n
        end
    | EFun f l => Fun f (map (translate_ETerm m) l)
    end.

  Fixpoint translate_EForm_ (m : list string) (F : EForm) : Form :=
    match F with
    | EBot => Bot
    | ETop => Neg Bot
    | EPred f l => Pred f (map (translate_ETerm m) l)
    | ENeg F => Neg (translate_EForm_ m F)
    | EOr F G => Or (translate_EForm_ m F) (translate_EForm_ m G)
    | EAnd F G => Neg (Or (Neg (translate_EForm_ m F)) (Neg (translate_EForm_ m G)))
    | EImp F G => Or (Neg (translate_EForm_ m F)) (translate_EForm_ m G)
    | EEqu F G => Neg (Or (Neg (Or (Neg (translate_EForm_ m F)) (translate_EForm_ m G)))
                      (Neg (Or (Neg (translate_EForm_ m G)) (translate_EForm_ m F))))
    | EEx x F  => Neg (All (Neg (translate_EForm_ (x :: m) F)))
    | EAll x F => All (translate_EForm_ (x :: m) F)
    end.

  Definition translate_EForm := translate_EForm_ [].

  Fixpoint instantiate_eterm (x : string) (u t : ETerm) : ETerm :=
    match t with
    | EVar y => if eqb x y then u else t
    | EFun f l => EFun f (map (instantiate_eterm x u) l)
    end.

  (* As I don't want to bother with freshness stuff, please make sure that the term [u]
     has no variable appearing in F. *)
  Fixpoint instantiate_eform (x : string) (u : ETerm) (F : EForm) : EForm :=
    match F with
    | EBot | ETop => F
    | EPred f l => EPred f (map (instantiate_eterm x u) l)
    | ENeg F => ENeg (instantiate_eform x u F)
    | EOr F G => EOr (instantiate_eform x u F) (instantiate_eform x u G)
    | EAnd F G => EAnd (instantiate_eform x u F) (instantiate_eform x u G)
    | EImp F G => EImp (instantiate_eform x u F) (instantiate_eform x u G)
    | EEqu F G => EEqu (instantiate_eform x u F) (instantiate_eform x u G)
    | EEx y F => EEx (if eqb x y then x else y)
                  (if eqb x y then F else instantiate_eform x u F)
    | EAll y F => EAll (if eqb x y then x else y)
                   (if eqb x y then F else instantiate_eform x u F)
    end.
End ESyntaxTranslation.

Class ETranslation (A B : Type) :=
  translate : A -> B.

Notation "[[ M ]]" := (translate M).

#[global] Instance etranslation_eform : ETranslation EForm Form :=
  translate_EForm.

#[global] Instance etranslation_term : ETranslation ETerm Term :=
  translate_ETerm [].

Coercion translate_EForm : EForm >-> Form.

(** ** 4. Correspondance of the semantics *)

Section ValidityEquivalence.

  (** Given [sigma] a list of valuation for bound variables in [l] and an environment [rho],
      we provide a new environment suitable for the extended semantics, and prove its
      required properties. *)
  Section ExtendedEnvironment.
    Context {M : Model string string} (bvs : list string) (rho : list M) (sigma : env M string).

    Definition extended_environment : env M string :=
      fun (x : string) =>
        match index_of x bvs with
        | None => sigma x
        | Some n => rho.(n)
        end.

    Lemma extended_environment_comp_None :
      forall (x : string),
        index_of x bvs = None ->
        extended_environment x = sigma x.
    Proof using Type.
      intros. unfold extended_environment.
      destruct (index_of x bvs); auto.
      congruence.
    Qed.

    Lemma extended_environment_comp_Some :
      forall (x : string) (n : nat),
        index_of x bvs = Some n ->
        extended_environment x = rho.(n).
    Proof using Type.
      intros; cbn. unfold extended_environment.
      now rewrite H.
    Qed.
  End ExtendedEnvironment.

  Lemma extend_extended_environment :
    forall {M : Model string string} (bvs : list string) (rho : list M) (sigma : env M string) (s : string)
      (x : M),
      extended_environment (s :: bvs) (x :: rho) sigma =
        fun y : string => if eqb s y then Some x else extended_environment bvs rho sigma y.
  Proof.
    intros. apply funext=>y. unfold extended_environment. cbn.
    rewrite -!match_eq_dec_eq_bool. destruct (s == y), (y == s); try congruence.
    - reflexivity.
    - destruct (index_of y bvs); now cbn.
  Qed.

  (** A general version of the equivalidity theorem: we give [l] a list of bound variables
      and [sigma] their valuation. We have to ensure that both lists have the same size. *)
  Section GenTranslationEquivalidity.
    Lemma gen_interp_term_interp_eterm :
      forall (M : Model string string) (t : ETerm) (bvs : list string) (rho : list M) (sigma : env M string),
      interpret_term rho sigma (translate_ETerm bvs t) =
        interpret_eterm (extended_environment bvs rho sigma) t.
    Proof.
      intros ?????. induction t using eterm_ind; cbn.
      - destruct (index_of x bvs) eqn:hindex_of_bvs.
        + cbn. now erewrite extended_environment_comp_Some.
        + now rewrite extended_environment_comp_None.
      - apply f_equal. induction l as [|x xs IHxs]; auto.
        cbn. rewrite IHxs.
        + now apply Forall_tail in H.
        + apply Forall_inv in H. now rewrite H.
    Qed.

    Lemma gen_translation_equivalidity :
      forall (M : Model string string) (F : EForm) (bvs : list string) (rho : list M) (sigma : env M string),
        [[ M # rho # sigma |- translate_EForm_ bvs F ]] <->
          interpret_eform M (extended_environment bvs rho sigma) F.
    Proof.
      intros M F; induction F.

      (* Cases: top/bottom *)
      - intros; cbn; split; auto.
      - intros; cbn; split; auto.

      (* Cases: predicates *)
      - intros; cbn.
        have e : map (interpret_term rho sigma) (map (translate_ETerm bvs) l) =
                   map (interpret_eterm (extended_environment bvs rho sigma)) l.
        { induction l as [|x xs IHxs]; auto. cbn.
          rewrite IHxs gen_interp_term_interp_eterm; auto. }
        rewrite e //.

      (* Cases: negation *)
      - intros; cbn. now rewrite IHF.

      (* Cases: disjunction *)
      - intros; cbn. now rewrite IHF1 IHF2.

      (* Cases: conjunction *)
      - intros; cbn. rewrite IHF1 IHF2. split; intro h.
        + split; apply NNPP=>save.
          * apply h. now left.
          * apply h. now right.
        + intros [hf1 | hf2]; [now apply hf1|now apply hf2].

      (* Cases: implication *)
      - intros; cbn. rewrite IHF1 IHF2. split; intro h.
        + intro h'. destruct h as [hnf1 | hf2]; auto. exfalso. now apply hnf1.
        + apply NNPP=>save. apply save. left. intro hf1.
          apply save. right. now apply h.

      (* Cases: equivalence *)
      - intros; cbn. rewrite !IHF1 !IHF2. split; intro h.
        + split; intro h'.
          * apply NNPP => save. apply h. left; intros [hnf1 | hf2]; auto.
          * apply NNPP => save. apply h. right; intros [hnf2 | hf1]; auto.
        + intros [h' | h']; apply h'.
          all: rewrite h; apply NNPP => save; apply save; left; intro hf2;
                                       apply save; now right.

      (* Cases: existential *)
      - intros; cbn. split; intros h.
        + apply NNPP => save. apply h. intros x hinterp. apply save.
          exists x. specialize (IHF (s :: bvs) (x :: rho) sigma).
          rewrite -extend_extended_environment. now rewrite -IHF.
        + intros hinterp. destruct h as (v & hinterp'). specialize (hinterp v).
          apply hinterp. rewrite -extend_extended_environment in hinterp'.
          now rewrite IHF.

      (* Cases: universal *)
      - intros; cbn. split; intros h v.
        + rewrite -extend_extended_environment -IHF //.
        + specialize (h v); rewrite -extend_extended_environment in h.
          rewrite IHF //.
    Qed.
  End GenTranslationEquivalidity.

  (** We can use the lemma we just proved to yield the result on closed formulas. *)
  Lemma translation_equivalidity :
    forall (F : EForm) (M : Model string string),
      ([[ M # [] # (empty_env M string) |- [[F]]]]) <->
        (interpret_eform M (empty_env M string) F).
  Proof. intros. apply gen_translation_equivalidity. Qed.

  (* TODO *)
  (* Lemma is_valid_translation_is_valid : *)
  (*   forall (F : EForm), \models (translate_EForm F) <-> is_evalid F. *)
  (* Proof. *)
  (*   intros F; split; intros H M; specialize (H M); *)
  (*     now apply translation_equivalidity. *)
  (* Qed. *)

  (* Lemma hasTableau_is_evalid : *)
  (*   forall (F : EForm) (sko : Skolemization) (Gamma : Con sko) (sigma : Substitution string Term), *)
  (*     hasTableau sko ([[ Gamma ]] ,, Neg [[ F ]]) sigma -> is_evalid (EAnd (ls_to_form (forms Gamma)) F). *)
  (* Proof. *)
  (*   intros ???? htab. apply (hasTableau_sound sko sigma Gamma [[ F ]]) in htab. *)
  (*   rewrite -is_valid_translation_is_valid. *)
  (* Qed. *)
End ValidityEquivalence.

(** ** 5. Helper to transform substitution into internal substitution *)
Section TranslateSubst.
  Fixpoint subst_translation (l : list (string * ETerm)) : string -> Term :=
    match l with
    | [] => fun x => Free x
    | x :: xs => fun y => if (eqb (fst x) y)
                     then [[ snd x ]]
                     else subst_translation xs y
    end.

  Lemma eterm_translation_is_always_locally_closed :
    forall (t : ETerm), @isLocallyClosed _ Term _ [[ t ]].
  Proof.
    intro t. induction t using eterm_ind.
    - unfold isLocallyClosed; cbn. apply empty_is_empty.
    - induction l as [|x xs IHxs]; unfold isLocallyClosed.
      + apply empty_is_empty.
      + cbn. apply is_empty_spec'; intros y. rewrite union_spec; intros [].
        * apply Forall_inv in H. red in H. apply is_empty_spec with (x := y) in H; auto.
        * apply Forall_tail in H. apply IHxs in H. red in H; cbn in H.
          now apply is_empty_spec with (x := y) in H.
  Qed.

  Lemma locally_closed_subst_translation :
    forall (l : list (string * ETerm)) (x : string),
      (forall (x : string) (t : ETerm), In (x, t) l -> @isLocallyClosed _ Term _ [[ t ]]) ->
      isLocallyClosed (subst_translation l x).
  Proof.
    intros l x H. induction l as [|y ys IHys]; unfold isLocallyClosed; cbn.
    - apply empty_is_empty.
    - change (fst y =? x) with (eqb (fst y) x).
      rewrite -match_eq_dec_eq_bool. destruct (fst y == x).
      + eapply (H (fst y)). right. now destruct y.
      + apply IHys. intros; apply (H x0).
        now left.
  Qed.

  Definition translate_substitution (l : list (string * ETerm)) :
    Substitution string Term.
  Proof.
    unshelve econstructor.
    - apply (subst_translation l).
    - intro x; refine (locally_closed_subst_translation l x _).
      intros; apply eterm_translation_is_always_locally_closed.
  Defined.
End TranslateSubst.

(** ** 6. Helpers for [hasTableau] with the full first-order free-variable tableau calculus. *)
Section HasTableauLemmas.
  Context (sko : Skolemization).

  Let sko_record := sko_record sko.
  Let Con := Con sko.

  Lemma con_nth_in :
    forall (Gamma : Con) (i : nat) (F : Form),
      nth_error (forms Gamma) i = Some F -> F \in Gamma.
  Proof using Type.
    intros ??? e. unfold in_ctx. revert e. set l := forms Gamma; clearbody l.
    generalize dependent i. induction l as [|x xs IHxs]; cbn in *;
      intros i e.
    - rewrite nth_error_nil in e; inversion e.
    - destruct i.
      + rewrite nth_error_cons_0 in e.
        injection e => e'. now left.
      + right. apply IHxs with (i := i).
        now rewrite nth_error_cons_succ in e.
  Qed.

  Lemma hasTableauBot :
    forall (Gamma : Con) (sigma : Substitution string Term) (S : SetOfString) (Sf : sko_record) (i : nat),
      nth_error (forms Gamma) i = Some [[ EBot ]] -> hasTableau_ sko Gamma S Sf sigma.
  Proof using Type.
    intros ????? e. apply hasTableauBot.
    eapply con_nth_in; eauto.
  Qed.

  Lemma hasTableauNegTop :
    forall (Gamma : Con) (sigma : Substitution string Term) (S : SetOfString) (Sf : sko_record) (i : nat),
      nth_error (forms Gamma) i = Some [[ ENeg ETop ]] -> hasTableau_ sko Gamma S Sf sigma.
  Proof using Type.
    intros ????? e. eapply hasTableauNegNeg.
    - cbn in e. eapply con_nth_in; eauto.
    - unshelve eapply hasTableauBot; cbn. exact 0. now cbn.
  Qed.

  Lemma hasTableauContr :
    forall (Gamma : Con) (sigma : Substitution string Term) (S : SetOfString) (Sf : sko_record)
      (i j : nat) (F G : EForm),
      nth_error (forms Gamma) i = Some [[ F ]] -> nth_error (forms Gamma) j = Some [[ G ]] ->
      (etranslation_eform (ENeg F))@[sigma] = (etranslation_eform G)@[sigma] ->
      hasTableau_ sko Gamma S Sf sigma.
  Proof using Type.
    intros ????????? e0 e1.
    eapply hasTableauContr; cbn in *.
    - eapply con_nth_in. exact H.
    - eapply con_nth_in. exact e0.
    - assumption.
  Qed.

  Lemma hasTableauNegNeg :
    forall (Gamma : Con) (sigma : Substitution string Term) (S : SetOfString) (Sf : sko_record)
      (i : nat) (F : EForm),
      nth_error (forms Gamma) i = Some [[ ENeg (ENeg F) ]] ->
      hasTableau_ sko (Gamma ,, [[ F ]]) S Sf sigma ->
      hasTableau_ sko Gamma S Sf sigma.
  Proof using Type.
    intros ?????? e htab. eapply hasTableauNegNeg; eauto.
    cbn in e; eapply con_nth_in; eauto.
  Qed.

  Lemma hasTableauAnd :
    forall (Gamma : Con) (sigma : Substitution string Term) (S : SetOfString) (Sf : sko_record)
      (i : nat) (F G : EForm),
      nth_error (forms Gamma) i = Some [[ EAnd F G ]] ->
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
    forall (Gamma : Con) (sigma : Substitution string Term) (S : SetOfString) (Sf : sko_record)
      (i : nat) (F G : EForm),
      nth_error (forms Gamma) i = Some [[ ENeg (EOr F G) ]] ->
      hasTableau_ sko (Gamma ,, [[ ENeg F ]] ,, [[ ENeg G ]]) S Sf sigma ->
      hasTableau_ sko Gamma S Sf sigma.
  Proof using Type.
    intros ??????? e htab. eapply hasTableauNegOr.
    - cbn in e; eapply con_nth_in; eauto.
    - assumption.
  Qed.

  Lemma hasTableauNegImp :
    forall (Gamma : Con) (sigma : Substitution string Term) (S : SetOfString) (Sf : sko_record)
      (i : nat) (F G : EForm),
      nth_error (forms Gamma) i = Some [[ ENeg (EImp F G) ]] ->
      hasTableau_ sko (Gamma ,, [[ ENeg (ENeg F) ]] ,, [[ ENeg G ]] ,, [[ F ]]) S Sf sigma ->
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
    forall (Gamma : Con) (sigma : Substitution string Term) (S S1 S2 : SetOfString) (Sf Sf1 Sf2 : sko_record)
      (i : nat) (F G : EForm),
      nth_error (forms Gamma) i = Some [[ EOr F G ]] ->
      hasTableau_ sko (Gamma ,, [[ F ]]) S1 Sf1 sigma ->
      hasTableau_ sko (Gamma ,, [[ G ]]) S2 Sf2 sigma -> disjoint S1 S2 = true ->
      eqb S (S1 \union S2) = true -> eqb Sf (join Sf1 Sf2) = true ->
      hasTableau_ sko Gamma S Sf sigma.
  Proof using Type.
    intros ??????????? e htab1 htab2. rewrite disjoint_are_disjoint.
    rewrite !eqbIsEq. intros ? -> ->. eapply hasTableauOr.
    all: eauto.
    cbn in *; eapply con_nth_in; eauto.
  Qed.

  Lemma hasTableauImp :
    forall (Gamma : Con) (sigma : Substitution string Term) (S S1 S2 : SetOfString) (Sf Sf1 Sf2 : sko_record)
      (i : nat) (F G : EForm),
      nth_error (forms Gamma) i = Some [[ EImp F G ]] ->
      hasTableau_ sko (Gamma ,, [[ ENeg F ]]) S1 Sf1 sigma ->
      hasTableau_ sko (Gamma ,, [[ G ]]) S2 Sf2 sigma -> disjoint S1 S2 = true ->
      eqb S (S1 \union S2) = true -> eqb Sf (join Sf1 Sf2) = true ->
      hasTableau_ sko Gamma S Sf sigma.
  Proof using Type.
    intros ??????????? e htab1 htab2 hdisjoint e0 e1.
    eapply hasTableauOr.
    1: cbn in *; change (Neg [[ F ]]) with ([[ ENeg F ]]) in e; eassumption.
    all: eauto.
  Qed.

  Lemma hasTableauNegAnd :
    forall (Gamma : Con) (sigma : Substitution string Term) (S S1 S2 : SetOfString) (Sf Sf1 Sf2 : sko_record)
      (i : nat) (F G : EForm),
      nth_error (forms Gamma) i = Some [[ ENeg (EAnd F G) ]] ->
      hasTableau_ sko (Gamma ,, (Or [[ ENeg F ]] [[ ENeg G ]]) ,, [[ ENeg F ]]) S1 Sf1 sigma ->
      hasTableau_ sko (Gamma ,, (Or [[ ENeg F ]] [[ ENeg G ]]) ,, [[ ENeg G ]]) S2 Sf2 sigma ->
      disjoint S1 S2 = true -> eqb S (S1 \union S2) = true -> eqb Sf (join Sf1 Sf2) = true ->
      hasTableau_ sko Gamma S Sf sigma.
  Proof using Type.
    intros ??????????? e htab1 htab2 e0 e1 hdisjoint. eapply hasTableauNegNeg.
    - cbn in *. change (Or (Neg [[ F ]]) (Neg [[ G ]])) with ([[ EOr (ENeg F) (ENeg G) ]]) in e.
      eassumption.
    - unshelve eapply hasTableauOr.
      1-4: shelve.
      1: exact 0.
      1-2: shelve.
      1: reflexivity.
      all: eauto.
  Qed.

  Lemma hasTableauEqu :
    forall (Gamma : Con) (sigma : Substitution string Term) (S S1 S2 : SetOfString) (Sf Sf1 Sf2 : sko_record)
      (i : nat) (F G : EForm),
      nth_error (forms Gamma) i = Some [[ (EEqu F G) ]] ->
      hasTableau_ sko (Gamma ,, [[ ENeg (ENeg (EImp F G)) ]] ,, [[ ENeg (ENeg (EImp G F)) ]] ,,
                         [[ EImp F G ]] ,, [[ EImp G F ]] ,, [[ ENeg F ]] ,, [[ ENeg G ]])
        S1 Sf1 sigma ->
      hasTableau_ sko (Gamma ,, [[ ENeg (ENeg (EImp F G)) ]] ,, [[ ENeg (ENeg (EImp G F)) ]] ,,
                         [[ EImp F G ]] ,, [[ EImp G F ]] ,, [[ G ]] ,, [[ F ]]) S2 Sf2 sigma ->
      disjoint S1 S2 = true -> eqb S (S1 \union S2) = true -> eqb Sf (join Sf1 Sf2) = true ->
      hasTableau_ sko Gamma S Sf sigma.
  Proof using Type.
    intros ??????????? e htab1 htab2 hdisjoint ??. unshelve eapply hasTableauNegOr.
    - exact i.
    - exact (ENeg (EImp F G)).
    - exact (ENeg (EImp G F)).
    - now cbn in *.
    - unshelve eapply hasTableauNegNeg.
      + exact 1.
      + exact (EImp F G).
      + now cbn.
      + unshelve eapply hasTableauNegNeg.
        * exact 1.
        * exact (EImp G F).
        * now cbn.
        * unshelve eapply hasTableauOr.
          1-4: shelve.
          7-9: eauto.
          -- exact 1.
          -- exact (ENeg F).
          -- exact G.
          -- now cbn.
          -- replace S1 with (S1 \union empty_set).
             replace Sf1 with (join Sf1 empty_record).
             2: apply join_unitr.
             2: apply empty_unitr.
             unshelve eapply hasTableauOr.
             1-4: shelve.
             ++ exact 1.
             ++ exact (ENeg G).
             ++ exact F.
             ++ now cbn.
             ++ eassumption.
             ++ unshelve eapply hasTableauContr.
                ** exact 0.
                ** exact 1.
                ** exact F.
                ** exact (ENeg F).
                ** now cbn.
                ** now cbn.
                ** reflexivity.
             ++ rewrite disjoint_are_disjoint.
                eapply empty_disjointr.
             ++ rewrite eqbIsEq //.
             ++ rewrite eqbIsEq; reflexivity.
          -- replace S2 with (empty_set \union S2).
             replace Sf2 with (join empty_record Sf2).
             2: apply join_unitl.
             2: apply empty_unitl.
             unshelve eapply hasTableauOr.
             1-4: shelve.
             ++ exact 1.
             ++ exact (ENeg G).
             ++ exact F.
             ++ now cbn.
             ++ unshelve eapply hasTableauContr.
                ** exact 1.
                ** exact 0.
                ** exact G.
                ** exact (ENeg G).
                ** now cbn.
                ** now cbn.
                ** reflexivity.
             ++ eassumption.
             ++ rewrite disjoint_are_disjoint.
                apply empty_disjointl.
             ++ rewrite eqbIsEq //.
             ++ rewrite eqbIsEq; reflexivity.
  Qed.

  Lemma hasTableauNegEqu :
    forall (Gamma : Con) (sigma : Substitution string Term) (S S1 S2 : SetOfString) (Sf Sf1 Sf2 : sko_record)
      (i : nat) (F G : EForm),
      nth_error (forms Gamma) i = Some [[ ENeg (EEqu F G) ]] ->
      hasTableau_ sko (Gamma ,, [[ EOr (ENeg (EImp F G)) (ENeg (EImp G F)) ]] ,, [[ ENeg (EImp F G) ]]
                         ,, [[ ENeg (ENeg F) ]] ,, [[ ENeg G ]] ,, [[ F ]]) S1 Sf1 sigma ->
      hasTableau_ sko (Gamma ,, [[ EOr (ENeg (EImp F G)) (ENeg (EImp G F)) ]] ,, [[ ENeg (EImp G F) ]]
                         ,, [[ ENeg (ENeg G) ]] ,, [[ ENeg F ]] ,, [[ G ]]) S2 Sf2 sigma ->
      disjoint S1 S2 = true -> eqb S (S1 \union S2) = true -> eqb Sf (join Sf1 Sf2) = true ->
      hasTableau_ sko Gamma S Sf sigma.
  Proof using Type.
    intros ??????????? e htab1 htab2 e1 e2 hdisjoint. unshelve eapply hasTableauNegNeg.
    - exact i.
    - exact (EOr (ENeg (EImp F G)) (ENeg (EImp G F))).
    - now cbn in *.
    - unshelve eapply hasTableauOr.
      1-4: shelve.
      1: exact 0.
      3: reflexivity.
      3-5: eauto.
      + unshelve eapply hasTableauNegImp.
        1: exact 0.
        3: reflexivity.
        assumption.
      + unshelve eapply hasTableauNegImp.
        1: exact 0.
        3: reflexivity.
        assumption.
  Qed.

  Lemma hasTableauAll :
    forall (Gamma : Con) (sigma : Substitution string Term) (S S0 : SetOfString) (Sf : sko_record)
      (i : nat) (F : EForm) (x : string) (y : string),
      nth_error (forms Gamma) i = Some [[ EAll x F ]] -> isFresh y (fv Gamma) = true ->
      S0 = rem y S -> mem y S = true ->
      hasTableau_ sko (Gamma ,, [[ instantiate_eform x (EVar y) F ]]) S0 Sf sigma ->
      hasTableau_ sko Gamma S Sf sigma.
  Proof.
    intros ????????? e hfresh eS hmem htab.
    have eS0 : S = add y S0.
    { rewrite eS add_rem; auto.
      now rewrite -mem_spec. }
    rewrite eS0. eapply hasTableauAll.
    - cbn in e. eapply con_nth_in; eauto.
    - assumption.
    - admit. (* TODO: [isFresh y S -> ~(y \in fv F) -> F{0 \to Free y} = instantiate_eform x (EVar y) F]
              *)
  Admitted.

  Existing Instance fv_ctx.

  Lemma hasTableauNegAll :
    forall (Gamma : Con) (sigma : Substitution string Term) (S : SetOfString) (Sf Sf0 : sko_record)
      (i : nat) (F : EForm) (x : string) (t : ETerm)
      (hsko : is_sko (translate_ETerm [] t) (Neg (translate_EForm_ [x] F)) (fv Gamma)
                (con_sko_record Gamma) = true),
      nth_error (forms Gamma) i = Some [[ ENeg (EAll x F) ]] ->
      Sf0 = rem_symbol (symbol sko [[t]] hsko) (translate_EForm_ [x] F) Sf ->
      in_record (symbol sko [[t]] hsko) Sf ->
      hasTableau_ sko
        (set_con_sko_record
           (add_symbol (symbol sko [[t]] hsko) [[F]] (con_sko_record Gamma))
           (Gamma ,, [[ instantiate_eform x t (ENeg F) ]])) S Sf0 sigma ->
      hasTableau_ sko Gamma S Sf sigma.
  Proof.
    intros ?????????? e0 e1 hin htab.
    have e2 : Sf = add_symbol (symbol sko [[t]] hsko) (translate_EForm_ [x] F) Sf0.
    { rewrite e1. symmetry; now apply add_rem_symbol. }
    rewrite e2.
    apply (hasTableauNegAll sko Gamma S Sf0 sigma (translate_EForm_ [x] F) [[ t ]] hsko).
    - cbn in e0 |- *; eapply con_nth_in; eauto.
    - admit. (* TODO: [is_sko t F Sf S -> ~(y \in fv F) -> F{0 \to t} = instantiate_eform x t F] *)
  Admitted.

  Lemma hasTableauEx :
    forall (Gamma : Con) (sigma : Substitution string Term) (S : SetOfString) (Sf Sf0 : sko_record)
      (i : nat) (F : EForm) (x : string) (t : ETerm)
      (hsko : is_sko [[ t ]] (Neg (translate_EForm_ [x] (ENeg F)))
                (fv Gamma) (con_sko_record Gamma) = true),
      nth_error (forms Gamma) i = Some [[ EEx x F ]] ->
      Sf0 = rem_symbol (symbol sko [[ t ]] hsko)
              (translate_EForm_ [x] (ENeg F)) Sf -> in_record (symbol sko [[ t ]] hsko) Sf ->
      hasTableau_ sko (set_con_sko_record
                         (add_symbol (symbol sko [[t]] hsko) [[ENeg F]] (con_sko_record Gamma))
                         (Gamma ,, [[ ENeg (ENeg (instantiate_eform x t F)) ]] ,,
                            [[ instantiate_eform x t F ]])) S Sf0 sigma ->
      hasTableau_ sko Gamma S Sf sigma.
  Proof using Type.
    intros ?????????? e0 e1 e2 htab. eapply hasTableauNegAll.
    all: eauto.
    Unshelve.
    3: exact i.
    all: eauto.
    unshelve eapply hasTableauNegNeg.
    1: exact 0.
    1: shelve.
    1: reflexivity.
    assumption.
  Qed.

  Lemma hasTableauNegEx :
    forall (Gamma : Con) (sigma : Substitution string Term) (S S0 : SetOfString) (Sf : sko_record)
      (i : nat) (F : EForm) (x : string) (y : string),
      nth_error (forms Gamma) i = Some [[ ENeg (EEx x F) ]] -> isFresh y (fv Gamma) = true ->
      S0 = rem y S -> mem y S = true ->
      hasTableau_ sko (Gamma ,, [[EAll x (ENeg F)]] ,, [[ instantiate_eform x (EVar y) (ENeg F) ]])
        S0 Sf sigma -> hasTableau_ sko Gamma S Sf sigma.
  Proof using Type.
    intros ????????? e hfresh eS hmem htab. unshelve eapply hasTableauNegNeg.
    - exact i.
    - exact (EAll x (ENeg F)).
    - now cbn in e |- *.
    - unshelve eapply hasTableauAll.
      2: exact 0.
      5: reflexivity.
      1-2: shelve.
      all: eauto.
      (* easy *) admit.
  Admitted.
End HasTableauLemmas.

(** ** 7. Tactics *)

Ltac esimpl := native_compute.
