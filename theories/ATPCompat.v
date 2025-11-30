(** * ATPCompat: helper functions and lemmas for easy ATP output *)

From Corelib Require Import Classes.RelationClasses.

From Stdlib Require Import Classical.
From Stdlib Require Import Lia.

From Tableaux Require Import Syntax.
From Tableaux Require Import Semantics.
From Tableaux Require Import Proofs.
From Tableaux Require Import Skolemization.

Export ConcreteSkolemizationInstances.

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
      | EEx x F   => exists (v : M), rec (fun y => match eqDec x y with
                                          | left _ => Some v
                                          | right _ => rho y
                                          end) F
      | EAll x F   => forall (v : M), rec (fun y => match eqDec x y with
                                           | left _ => Some v
                                           | right _ => rho y
                                           end) F
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

  Lemma fv_efun :
    forall (f : string) (l : list ETerm) (t : ETerm) (x : string),
      In t l -> mem x (fv_eterm t) -> mem x (fv_eterm (EFun f l)).
  Proof.
    intros ???? hin hmem. cbn[fv_eterm] in hmem |- *.
    induction l as [|y ys IHys].
    - inversion hin.
    - rewrite mem_fold_left_cons_unionl. apply union_spec. destruct hin as [hin | e].
      + left. now apply IHys.
      + right. rewrite -e //.
  Qed.

  (* Fixpoint fv_eform (F : EForm) : SetOfString := *)
  (*   match F with *)
  (*   | EBot | ETop => empty_set string *)
  (*   | EPred p l => fold_left (fun s t => s \union (fv_eterm t)) l (empty_set string) *)
  (*   | ENeg F => fv_eform F *)
  (*   | EOr F G | EAnd F G | EImp F G | EEqu F G => (fv_eform F) \union (fv_eform G) *)
  (*   | EEx x F | EAll x F => remove x (fv_eform F) *)
  (*   end. *)

  Fixpoint bv_eform (F : EForm) : SetOfString :=
    match F with
    | EBot | ETop | EPred _ _ => empty_set
    | ENeg F => bv_eform F
    | EOr F G | EAnd F G | EImp F G | EEqu F G => (bv_eform F) \union (bv_eform G)
    | EEx x F | EAll x F => add x (bv_eform F)
    end.

  (* Definition WellScoped (F : EForm) := is_empty (fv_eform F). *)

  Section IndexOf.
    Context {A : Type} `{EqDec A}.

    Fixpoint index_of (x : A) (l : list A) : option nat :=
    match l with
    | [] => None
    | y :: ys => match eqDec x y with
               | left _ => Some 0
               | right _ => bind (index_of x ys) (fun n => Some (S n))
               end
    end.

    Lemma index_of_spec :
      forall (x : A) (n : nat) (l : list A),
        index_of x l = Some n -> nth_error l n = Some x.
    Proof using Type.
      intros ??? e. generalize dependent n. induction l as [|y ys IHys].
      - intros ? e. inversion e.
      - intros ? e; cbn in *. destruct eqDec; cbn.
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
      - cbn in *. repeat (destruct eqDec; cbn in * ).
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
      - cbn. destruct (x == y).
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
      - intros ? e; cbn in *. destruct (x == y).
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
      intros ???? e; cbn in *.
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
      intros ???? e0 e; cbn in *.
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
        + intros h hin hin'. cbn. destruct (x == y), (x == a); auto.
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
    | EVar y =>
        match x == y with
        | left _ => u
        | right _ => t
        end
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
    | EEx y F => EEx (match x == y with left _ => x | right _ => y end)
                  (match x == y with
                   | left _ => F
                   | right _ => (instantiate_eform x u F)
                   end)
    | EAll y F => EAll (match x == y with left _ => x | right _ => y end)
                  (match x == y with
                   | left _ => F
                   | right _ => (instantiate_eform x u F)
                   end)
    end.

  (* Lemma WellScoped_no_fv_eterm : *)
  (*   forall (t : ETerm), is_empty (fv_eterm t) -> is_empty (@fv string _ _ (translate_ETerm [] t)). *)
  (* Proof. *)
  (*   intros t hscope; induction t using eterm_rect'; cbn in *. *)
  (*   - assumption. *)
  (*   - induction l. *)
  (*     + now cbn in *. *)
  (*     + cbn in *. Admitted. *)

  (* Lemma WellScoped_no_fv : *)
  (*   forall (F : EForm), WellScoped F -> is_empty (@fv string _ _ (translate_EForm F)). *)
  (* Proof. *)
  (*   intros F hscope; induction F. *)
  (*   - cbn. rewrite is_empty_spec //. *)
  (*   - cbn; rewrite is_empty_spec //. *)
  (*   - cbn in *. admit. *)
  (*   - cbn in *. now apply IHF. *)
  (*   - admit. *)
  (*   - admit. *)
  (*   - admit. *)
  (*   - admit. *)
  (*   - admit. *)
  (*   - admit. *)
  (* Admitted. *)

  (* Definition LocallyClosedETerm (t : ETerm) (rho : list string) := *)
  (*   forall (x : string), mem x (fv_eterm t) -> (In x rho -> False). *)

  (* Lemma LocallyClosed_tail : *)
  (*   forall (t : ETerm) (x : string) (rho : list string), *)
  (*     LocallyClosedETerm t (x :: rho) -> LocallyClosedETerm t rho. *)
  (* Proof. intros ??? hclosed y hmem hin. eapply hclosed; eauto. now left. Qed. *)

  (* Lemma LocallyClosedETerm_translate_all : *)
  (*   forall (t : ETerm) (rho sigma : list string), *)
  (*     LocallyClosedETerm t rho -> LocallyClosedETerm t sigma -> *)
  (*     translate_ETerm rho t = translate_ETerm sigma t. *)
  (* Proof. *)
  (*   intros ??? closedr closeds. induction t using eterm_ind. *)
  (*   - red in closedr, closeds. cbn[fv_eterm] in closedr, closeds. *)
  (*     specialize (closedr x (singleton_spec x)). *)
  (*     specialize (closeds x (singleton_spec x)). *)
  (*     cbn. destruct (index_of x rho) eqn:xrho, (index_of x sigma) eqn:xsig. *)
  (*     + now apply index_of_In, closedr in xrho. *)
  (*     + now apply index_of_In, closedr in xrho. *)
  (*     + now apply index_of_In, closeds in xsig. *)
  (*     + reflexivity. *)
  (*   - cbn. f_equal. *)
  (*     have hr : forall (t : ETerm), In t l -> LocallyClosedETerm t rho. { *)
  (*       clear H closeds. intros t hin x hmem hin'. *)
  (*       specialize (closedr x). cbn[fv_eterm] in closedr. *)
  (*       apply fv_efun with (f := f) (l := l) in hmem; auto. *)
  (*     } *)
  (*     have hs : forall (t : ETerm), In t l -> LocallyClosedETerm t sigma. { *)
  (*       clear H closedr. intros t hin x hmem hin'. *)
  (*       specialize (closeds x). cbn[fv_eterm] in closeds. *)
  (*       apply fv_efun with (f := f) (l := l) in hmem; auto. *)
  (*     } *)
  (*     have H' : forall (t : ETerm), In t l -> translate_ETerm rho t = translate_ETerm sigma t. { *)
  (*       intros. apply Forall_In with (x := t) in H; auto. *)
  (*     } *)
  (*     clear closedr closeds H. *)
  (*     induction l as [|x xs IHxs]; auto. *)
  (*     cbn. rewrite H'. *)
  (*     + now right. *)
  (*     + rewrite IHxs; auto. *)
  (*       * intros; apply hr. now left. *)
  (*       * intros; apply hs. now left. *)
  (*       * intros; apply H'. now left. *)
  (* Qed. *)

  (* Lemma instantiate_commutes_term : *)
  (*   forall (t : ETerm) (x : string) (u : ETerm) (rho sigma : list string) (n : nat), *)
  (*     (LocallyClosedETerm u rho /\ LocallyClosedETerm u sigma) -> *)
  (*     index_of x rho = Some n  -> *)
  (*     translate_ETerm rho (instantiate_eterm x u t) = *)
  (*       (translate_ETerm rho t){n \to translate_ETerm sigma u}. *)
  (* Proof. *)
  (*   intros t; induction t using eterm_ind. *)
  (*   - intros y ???? [closedr closeds] e; cbn. destruct eqDec; cbn. *)
  (*     + destruct (index_of x rho) eqn:index; cbn. *)
  (*       * destruct (eq_dec_nat n n0) eqn:enat; auto. *)
  (*         subst. rewrite e in index. *)
  (*         2: congruence. *)
  (*         apply LocallyClosedETerm_translate_all; auto. *)
  (*       * subst. rewrite e in index. inversion index. *)
  (*     + destruct (index_of x rho) eqn:index; cbn; auto. *)
  (*       destruct (eq_dec_nat n n1) eqn:enat; auto. *)
  (*       rewrite -e0 in index. *)
  (*       have ex : x = y. { eapply index_of_inj; eauto. } *)
  (*       congruence. *)
  (*   - intros; cbn. rewrite !map_map. *)
  (*     have hmap : map (fun t => translate_ETerm rho (instantiate_eterm x u t)) l = *)
  (*                   map (fun t => (translate_ETerm rho t){n \to translate_ETerm sigma u}) l. *)
  (*     { induction l as [|y ys IHys]; auto. *)
  (*       cbn. rewrite IHys. *)
  (*       - now apply Forall_tail in H. *)
  (*       - apply Forall_In with (x := y) in H. *)
  (*         + erewrite H. *)
  (*           2,3: eassumption. *)
  (*           reflexivity. *)
  (*         + now right. } *)
  (*     rewrite hmap //. *)
  (* Qed. *)

  (* Lemma WellScoped_instantiate_commutes : *)
  (*   forall (F : EForm) (x : string) (rho : list string) (sigma : list string) (t : ETerm) (n : nat), *)
  (*     (forall (y : string), mem y (fv_eterm t) -> ~(mem y (bv_eform F))) -> *)
  (*     LocallyClosedETerm t (x :: rho) -> LocallyClosedETerm t sigma -> index_of x rho = Some n -> *)
  (*     translate_EForm_ rho (instantiate_eform x t F) = *)
  (*       (translate_EForm_ rho F){n \to translate_ETerm sigma t}. *)
  (* Proof. *)
  (*   intros F x rho sigma t. revert rho sigma. induction F; auto; intros rho sigma n hclosedF hclosedr hcloseds e; *)
  (*     cbn. *)
  (*   - rewrite !map_map. *)
  (*     have hmap : map (fun u => translate_ETerm rho (instantiate_eterm x t u)) l = *)
  (*                   map (fun u => (translate_ETerm rho u){n \to translate_ETerm sigma t}) l. *)
  (*     { induction l as [|y ys IHys]; auto. *)
  (*       cbn. erewrite instantiate_commutes_term. *)
  (*       3: eassumption. *)
  (*       2: { apply LocallyClosed_tail in hclosedr; split; eauto. } *)
  (*       rewrite IHys //. } *)
  (*     rewrite hmap //. *)
  (*   - erewrite IHF; eauto. *)
  (*   - erewrite IHF1, IHF2; eauto. *)
  (*     + intros y hmem hmem'.  apply (hclosedF y); auto. *)
  (*       rewrite mem_union; now right. *)
  (*     + intros y hmem hmem'.  apply (hclosedF y); auto. *)
  (*       rewrite mem_union; now left. *)
  (*   - erewrite IHF1, IHF2; eauto. *)
  (*     + intros y hmem hmem'.  apply (hclosedF y); auto. *)
  (*       rewrite mem_union; now right. *)
  (*     + intros y hmem hmem'.  apply (hclosedF y); auto. *)
  (*       rewrite mem_union; now left. *)
  (*   - erewrite IHF1, IHF2; eauto. *)
  (*     + intros y hmem hmem'.  apply (hclosedF y); auto. *)
  (*       rewrite mem_union; now right. *)
  (*     + intros y hmem hmem'.  apply (hclosedF y); auto. *)
  (*       rewrite mem_union; now left. *)
  (*   - erewrite IHF1, IHF2; eauto. *)
  (*     + intros y hmem hmem'.  apply (hclosedF y); auto. *)
  (*       rewrite mem_union; now right. *)
  (*     + intros y hmem hmem'.  apply (hclosedF y); auto. *)
  (*       rewrite mem_union; now left. *)
  (*   - destruct (x == s); cbn. *)
  (*     + rewrite e0. *)
  (*       have en : n = 0. { admit. } (* todo: easy *) *)
  (*       rewrite !en in e |- *. admit. (* yes: overshadowed *) *)
  (*     + rewrite -(IHF (s :: rho) sigma (n + 1)); auto. *)
  (*       * intros y hmem hmem'. apply (hclosedF y); auto. *)
  (*         (* todo: mem_add *) admit. *)
  (*       * intros y hmem hin. repeat destruct hin as [hin | e0]. *)
  (*         -- apply (hclosedr y); auto. now left. *)
  (*         -- apply (hclosedF y); auto. *)
  (*            (* todo: mem_add *) admit. *)
  (*         -- apply (hclosedr y); auto. now right. *)
  (*       * rewrite PeanoNat.Nat.add_1_r; apply index_of_cons'; auto. *)
  (*   - destruct (x == s); cbn. *)
  (*     + rewrite e0. *)
  (*       have en : n = 0. { admit. } (* todo: easy *) *)
  (*       rewrite !en in e |- *. admit. (* yes: overshadowed *) *)
  (*     + rewrite -(IHF (s :: rho) sigma (n + 1)); auto. *)
  (*       * intros y hmem hmem'. apply (hclosedF y); auto. *)
  (*         (* todo: mem_add *) admit. *)
  (*       * intros y hmem hin. repeat destruct hin as [hin | e0]. *)
  (*         -- apply (hclosedr y); auto. now left. *)
  (*         -- apply (hclosedF y); auto. *)
  (*            (* todo: mem_add *) admit. *)
  (*         -- apply (hclosedr y); auto. now right. *)
  (*       * rewrite PeanoNat.Nat.add_1_r; apply index_of_cons'; auto. *)
  (*   Admitted. *)

(* Pred s *)
(*     (map (fun t : Term_ string string => t {#| rho | - 1 \to Free x}) (map (translate_ETerm rho) l)) = *)
  (*   Pred s (map (translate_ETerm sigma) l) *)
  Lemma instantiate_var_as_free_in_term :
    forall (t : ETerm) (rho sigma : list string) (s : string) (n : nat),
      index_of s rho = Some n ->
      (forall m, m < n -> nth_error rho m = nth_error sigma m) ->
      nth_error sigma n = None ->
      (translate_ETerm rho t) {n \to Free s} = translate_ETerm sigma t.
  Proof.
    intros t; induction t using eterm_ind'; intros rho sigma s n es erho hnone.
    - cbn; destruct (index_of x rho) eqn:ex.
      + destruct (index_of x sigma) eqn:ex'.
        * cbn. destruct (n == n0).
          -- subst. apply index_of_inj with (x := x) in es; auto.
             subst. have h : index_of s rho = index_of s sigma.
             { apply index_of_nth.
               - intros. apply erho.
                 have hlt : #|sigma| <= n0 by now rewrite nth_error_None in hnone.
                 lia.
               - now apply index_of_In in ex.
               - now apply index_of_In in ex'. }
             have e : n0 = n1 by congruence.
             rewrite e in hnone. apply index_of_spec in ex'. congruence.
          -- have h : index_of x rho = index_of x sigma.
             { apply index_of_nth.
               - intros. apply erho.
                 have hlt : #|sigma| <= n by now rewrite nth_error_None in hnone. lia.
               - now apply index_of_In in ex.
               - now apply index_of_In in ex'. }
             congruence.
        * cbn. Admitted.

  Lemma instantiate_var_as_free_in_form :
    forall (F : EForm) (rho sigma : list string) (s : string) (n : nat),
      index_of s rho = Some n ->
      (forall m, m < n -> nth_error rho m = nth_error sigma m) ->
      nth_error sigma n = None ->
      (translate_EForm_ rho F) {n \to Free s} = translate_EForm_ sigma F.
  Proof.
    intros F; induction F; intros rho sigma x n ex erho hnone; cbn; auto.
    - rewrite map_map. f_equal. induction l as [|t ts IHts]; auto.
      cbn. erewrite IHts, instantiate_var_as_free_in_term; eauto.
    - rewrite (IHF _ sigma); auto.
    - rewrite (IHF1 _ sigma); auto. rewrite (IHF2 _ sigma); auto.
    - rewrite (IHF1 _ sigma); auto. rewrite (IHF2 _ sigma); auto.
    - rewrite (IHF1 _ sigma); auto. rewrite (IHF2 _ sigma); auto.
    - rewrite (IHF1 _ sigma); auto. rewrite (IHF2 _ sigma); auto.
    - destruct (x == s).
      + (* in this case, [n + 1] does not appear in the FVs of F so the opening does nothing.
           Also, it makes the translations equal (as [rho] and [sigma] are equal in all the other
           values *) admit.
      + rewrite (IHF (s :: rho) (s :: sigma) x (n + 1)).
        * cbn. destruct (x == s); try congruence.
          destruct (index_of x rho); cbn.
          -- rewrite PeanoNat.Nat.add_1_r. injection ex => -> //.
          -- inversion ex.
        * intros; destruct m; cbn; auto.
          apply erho. rewrite PeanoNat.Nat.add_1_r in H; lia.
        * rewrite PeanoNat.Nat.add_1_r nth_error_cons_succ //.
        * reflexivity.
    - destruct (x == s).
      + (* in this case, [n + 1] does not appear in the FVs of F so the opening does nothing.
           Also, it makes the translations equal (as [rho] and [sigma] are equal in all the other
           values *) admit.
      + rewrite (IHF (s :: rho) (s :: sigma) x (n + 1)).
        * cbn. destruct (x == s); try congruence.
          destruct (index_of x rho); cbn.
          -- rewrite PeanoNat.Nat.add_1_r. injection ex => -> //.
          -- inversion ex.
        * intros; destruct m; cbn; auto.
          apply erho. rewrite PeanoNat.Nat.add_1_r in H; lia.
        * rewrite PeanoNat.Nat.add_1_r nth_error_cons_succ //.
        * reflexivity.
  Admitted.
End ESyntaxTranslation.

Class ETranslation (A B : Type) :=
  translate : A -> B.

Notation "[[ M ]]" := (translate M).

#[global] Instance etranslation_eform : ETranslation EForm Form :=
  translate_EForm.

#[global] Instance etranslation_term : ETranslation ETerm Term :=
  translate_ETerm [].

Coercion translate_EForm : EForm >-> Form.

(** ** 4. Correspondance of the syntax *)

Section ValidityEquivalence.
  Lemma interp_term_interp_eterm :
    forall (M : Model string string) (t : ETerm) (rho : list M) (sigma : env M string),
      interpret_term rho sigma [[ t ]] = interpret_eterm sigma t.
  Proof.
    intros ????. induction t using eterm_ind; cbn; auto.
    rewrite map_map.
    have Hmap : map (fun u => interpret_term rho sigma [[ u ]]) l = map (interpret_eterm sigma) l.
    { induction l as [|x xs IHxs]; auto.
      cbn. rewrite IHxs.
      - now apply Forall_tail in H.
      - apply Forall_In with (x := x) in H.
        + rewrite H //.
        + now right. }
    rewrite Hmap //.
  Qed.

  Lemma interpret_eterm_map_interpret_term :
    forall (M : Model string string) (l : list ETerm),
      map (interpret_eterm (empty_env M string)) l =
        map (fun u => interpret_term [] (empty_env M string) [[ u ]]) l.
  Proof.
    intros ??. induction l as [|x xs IHxs]; auto.
    cbn; rewrite interp_term_interp_eterm IHxs //.
  Qed.

  Lemma is_valid_translation_is_valid_ :
    forall (F : EForm) (M : Model string string),
      ([[ M # [] # (empty_env M string) |- [[F]]]]) <->
        (interpret_eform M (empty_env M string) F).
  Proof.
    intros F; induction F;
      intros M; split; intros hvalid.
    all: try (cbn in *; auto; fail).

    (** Cases: pred *)
    - cbn in *; rewrite map_map in hvalid; rewrite interpret_eterm_map_interpret_term //.
    - cbn in *; rewrite map_map -interpret_eterm_map_interpret_term //.

    (** Cases: neg *)
    - cbn in *; intro hvalid'; apply hvalid. now rewrite IHF.
    - cbn in *; intro hvalid'; apply hvalid. now rewrite -IHF.

    (** Cases: or *)
    - cbn in *; destruct hvalid as [hvalid1 | hvalid2].
      + left; now rewrite -IHF1.
      + right; now rewrite -IHF2.
    - cbn in *; destruct hvalid as [hvalid1 | hvalid2].
      + left; now rewrite IHF1.
      + right; now rewrite IHF2.

    (** Cases: and *)
    - cbn in *; split.
      + apply NNPP => hnf1. apply hvalid. left. intro hf1. apply hnf1.
        rewrite -IHF1 //.
      + apply NNPP => hnf2. apply hvalid. right. intro hf2. apply hnf2.
        rewrite -IHF2 //.
    - cbn in *; intros [hf1 | hf2].
      + apply hf1. rewrite IHF1. apply hvalid.
      + apply hf2. rewrite IHF2. apply hvalid.

    (** Cases: imp *)
    - cbn in *; intro hf1. destruct hvalid as [hnf1 | hf2].
      + exfalso. apply hnf1. rewrite IHF1 //.
      + rewrite -IHF2 //.
    - cbn in *; apply NNPP => save. apply save. right.
      rewrite IHF2. apply hvalid. apply NNPP => hnf1. apply save. left. rewrite IHF1 //.

    (** Cases: equ *)
    - cbn in *; split.
      + intros hf1. apply NNPP => hnf2. apply hvalid. left. intros [hnf1 | hf2].
        * apply hnf1. rewrite IHF1 //.
        * apply hnf2. rewrite -IHF2 //.
      + intros hf2. apply NNPP => hnf1. apply hvalid. right. intros [hnf2 | hf1].
        * apply hnf2. rewrite IHF2 //.
        * apply hnf1. rewrite -IHF1 //.
    - cbn in *; intros [himp | himp]; apply himp;
        rewrite IHF2 IHF1 hvalid; apply imply_to_or; tauto.

    (** Cases: ex *)
    - cbn in *.
      apply NNPP => save. apply hvalid => x hF.
      apply save. exists x.

      (* TODO: show this: *)
      have H : forall M x rho (F : Form) s,
          [[ M # [x] # rho |- F ]] =
            [[ M # [] # (fun y => match s == y with
                               | left _ => Some x
                               | right _ => rho y
                               end) |- (F{0 \to Free s}) ]].
      { admit. }
      rewrite (H _ _ _ _ s) in hF.
      rewrite (instantiate_var_as_free_in_form _ _ []) in hF.
      + cbn; destruct (s == s); auto. exfalso; now apply n.
      + intros m contra; inversion contra.
      + reflexivity.
      + admit. (* TODO: generalize IHF and this is free *)
  Admitted.

  Lemma is_valid_translation_is_valid :
    forall (F : EForm), \models (translate_EForm F) <-> is_evalid F.
  Proof.
    intros F; split; intros H M; specialize (H M);
      now apply is_valid_translation_is_valid_.
  Qed.

  Lemma hasTableau_is_evalid :
    forall (F : EForm) (sko : Skolemization) (sigma : Substitution string Term),
      hasTableau sko {{ Neg [[ F ]] }} sigma -> is_evalid F.
  Proof.
    intros ??? htab. apply (hasTableau_sound sko [[ F ]] sigma) in htab.
    now rewrite -is_valid_translation_is_valid.
  Qed.
End ValidityEquivalence.

(** ** 5. Helper to transform substitution into internal substitution *)
Section TranslateSubst.
  Fixpoint subst_translation (l : list (string * ETerm)) : string -> Term :=
    match l with
    | [] => fun x => Free x
    | x :: xs => fun y => match ((fst x) == y) with
                     | left _ => [[ snd x ]]
                     | right _ => subst_translation xs y
                     end
    end.

  Lemma eterm_translation_is_always_locally_closed :
    forall (t : ETerm), @isLocallyClosed _ Term _ [[ t ]].
  Proof.
    intro t. induction t using eterm_ind.
    - unfold isLocallyClosed; cbn. apply empty_is_empty.
    - induction l as [|x xs IHxs]; unfold isLocallyClosed; cbn.
      + apply empty_is_empty.
      + rewrite empty_unitl.
        have Hbv := Forall_In _ _ H x (ltac:(now right)).
        red in Hbv. unfold is_empty in Hbv; cbn in Hbv.
        rewrite Hbv. apply IHxs, In_Forall=>u hu.
        apply Forall_In with (x := u) in H; auto.
        now left.
  Qed.

  Lemma locally_closed_subst_translation :
    forall (l : list (string * ETerm)) (x : string),
      (forall (x : string) (t : ETerm), In (x, t) l -> @isLocallyClosed _ Term _ [[ t ]]) ->
      isLocallyClosed (subst_translation l x).
  Proof.
    intros l x H. induction l as [|y ys IHys]; unfold isLocallyClosed; cbn.
    - apply empty_is_empty.
    - destruct (fst y == x).
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
      hasTableau_ sko (Gamma ,, Neg [[ F ]] ,, Neg [[ G ]]) S Sf sigma ->
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
    forall (Gamma : Con) (sigma : Substitution string Term) (S1 S2 : SetOfString) (Sf1 Sf2 : sko_record)
      (i : nat) (F G : EForm),
      nth_error (forms Gamma) i = Some [[ EOr F G ]] ->
      hasTableau_ sko (Gamma ,, [[ F ]]) S1 Sf1 sigma ->
      hasTableau_ sko (Gamma ,, [[ G ]]) S2 Sf2 sigma -> disjoint S1 S2 ->
      hasTableau_ sko Gamma (S1 \union S2) (join Sf1 Sf2) sigma.
  Proof using Type.
    intros ????????? e htab1 htab2. eapply hasTableauOr.
    1: cbn in *; eapply con_nth_in; eauto.
    all: assumption.
  Qed.

  Lemma hasTableauImp :
    forall (Gamma : Con) (sigma : Substitution string Term) (S S1 S2 : SetOfString) (Sf Sf1 Sf2 : sko_record)
      (i : nat) (F G : EForm),
      nth_error (forms Gamma) i = Some [[ EImp F G ]] ->
      hasTableau_ sko (Gamma ,, [[ ENeg F ]]) S1 Sf1 sigma ->
      hasTableau_ sko (Gamma ,, [[ G ]]) S2 Sf2 sigma -> disjoint S1 S2 ->
      S = S1 \union S2 -> Sf = join Sf1 Sf2 ->
      hasTableau_ sko Gamma S Sf sigma.
  Proof using Type.
    intros ??????????? e htab1 htab2 hdisjoint e0 e1.
    rewrite e0 e1; eapply hasTableauOr.
    1: cbn in *; change (Neg [[ F ]]) with ([[ ENeg F ]]) in e; eassumption.
    all: assumption.
  Qed.

  Lemma hasTableauNegAnd :
    forall (Gamma : Con) (sigma : Substitution string Term) (S S1 S2 : SetOfString) (Sf Sf1 Sf2 : sko_record)
      (i : nat) (F G : EForm),
      nth_error (forms Gamma) i = Some [[ ENeg (EAnd F G) ]] ->
      hasTableau_ sko (Gamma ,, (Or [[ ENeg F ]] [[ ENeg G ]]) ,, [[ ENeg F ]]) S1 Sf1 sigma ->
      hasTableau_ sko (Gamma ,, (Or [[ ENeg F ]] [[ ENeg G ]]) ,, [[ ENeg G ]]) S2 Sf2 sigma ->
      S = S1 \union S2 -> Sf = join Sf1 Sf2 ->
      disjoint S1 S2 -> hasTableau_ sko Gamma S Sf sigma.
  Proof using Type.
    intros ??????????? e htab1 htab2 e0 e1 hdisjoint. eapply hasTableauNegNeg.
    - cbn in *. change (Or (Neg [[ F ]]) (Neg [[ G ]])) with ([[ EOr (ENeg F) (ENeg G) ]]) in e.
      eassumption.
    - rewrite e0 e1. unshelve eapply hasTableauOr.
      1: exact 0.
      3: reflexivity.
      all: assumption.
  Qed.

  Lemma hasTableauEqu :
    forall (Gamma : Con) (sigma : Substitution string Term) (S S1 S2 : SetOfString) (Sf Sf1 Sf2 : sko_record)
      (i : nat) (F G : EForm),
      nth_error (forms Gamma) i = Some [[ (EEqu F G) ]] ->
      hasTableau_ sko (Gamma ,, Neg [[ ENeg (EImp F G) ]] ,, Neg [[ ENeg (EImp G F) ]] ,,
                         [[ EImp F G ]] ,, [[ EImp G F ]] ,, [[ ENeg F ]] ,, [[ ENeg G ]])
        S1 Sf1 sigma ->
      hasTableau_ sko (Gamma ,, Neg [[ ENeg (EImp F G) ]] ,, Neg [[ ENeg (EImp G F) ]] ,,
                         [[ EImp F G ]] ,, [[ EImp G F ]] ,, [[ G ]] ,, [[ F ]]) S2 Sf2 sigma ->
      S = S1 \union S2 -> Sf = join Sf1 Sf2 ->
      disjoint S1 S2 -> hasTableau_ sko Gamma S Sf sigma.
  Proof using Type.
    intros ??????????? e htab1 htab2 -> -> hdisjoint. unshelve eapply hasTableauNegOr.
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
          -- exact 1.
          -- exact (ENeg F).
          -- exact G.
          -- now cbn.
          -- replace S1 with (S1 \union empty_set).
             replace Sf1 with (join Sf1 empty_record).
             2: apply join_unitr.
             2: apply empty_unitr.
             unshelve eapply hasTableauOr.
             ++ exact 1.
             ++ exact (ENeg G).
             ++ exact F.
             ++ now cbn.
             ++ assumption.
             ++ unshelve eapply hasTableauContr.
                ** exact 0.
                ** exact 1.
                ** exact F.
                ** exact (ENeg F).
                ** now cbn.
                ** now cbn.
                ** reflexivity.
             ++ apply empty_disjointr.
          -- replace S2 with (empty_set \union S2).
             replace Sf2 with (join empty_record Sf2).
             2: apply join_unitl.
             2: apply empty_unitl.
             unshelve eapply hasTableauOr.
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
             ++ assumption.
             ++ apply empty_disjointl.
          -- assumption.
  Qed.

  Lemma hasTableauNegEqu :
    forall (Gamma : Con) (sigma : Substitution string Term) (S S1 S2 : SetOfString) (Sf Sf1 Sf2 : sko_record)
      (i : nat) (F G : EForm),
      nth_error (forms Gamma) i = Some [[ ENeg (EEqu F G) ]] ->
      hasTableau_ sko (Gamma ,, [[ EOr (ENeg (EImp F G)) (ENeg (EImp G F)) ]] ,, [[ ENeg (EImp F G) ]]
                         ,, [[ ENeg (ENeg F) ]] ,, [[ ENeg G ]] ,, [[ F ]]) S1 Sf1 sigma ->
      hasTableau_ sko (Gamma ,, [[ EOr (ENeg (EImp F G)) (ENeg (EImp G F)) ]] ,, [[ ENeg (EImp G F) ]]
                         ,, [[ ENeg (ENeg G) ]] ,, [[ ENeg F ]] ,, [[ G ]]) S2 Sf2 sigma ->
      S = S1 \union S2 -> Sf = join Sf1 Sf2 ->
      disjoint S1 S2 -> hasTableau_ sko Gamma (S1 \union S2) (join Sf1 Sf2) sigma.
  Proof using Type.
    intros ??????????? e htab1 htab2 -> -> hdisjoint. unshelve eapply hasTableauNegNeg.
    - exact i.
    - exact (EOr (ENeg (EImp F G)) (ENeg (EImp G F))).
    - now cbn in *.
    - unshelve eapply hasTableauOr.
      1: exact 0.
      3: reflexivity.
      + unshelve eapply hasTableauNegImp.
        1: exact 0.
        3: reflexivity.
        assumption.
      + unshelve eapply hasTableauNegImp.
        1: exact 0.
        3: reflexivity.
        assumption.
      + assumption.
  Qed.

  Lemma hasTableauAll :
    forall (Gamma : Con) (sigma : Substitution string Term) (S : SetOfString) (Sf : sko_record)
      (i : nat) (F : EForm)
      (x : string) (y : string),
      nth_error (forms Gamma) i = Some [[ EAll x F ]] -> isFresh y S ->
      hasTableau_ sko (Gamma ,, [[ instantiate_eform x (EVar y) F ]]) S Sf sigma ->
      hasTableau_ sko Gamma (add y S) Sf sigma.
  Proof.
    intros ???????? e hfresh htab. eapply hasTableauAll.
    - cbn in e. eapply con_nth_in; eauto.
    - assumption.
    - admit. (* TODO: [isFresh y S -> ~(y \in fv F) -> F{0 \to Free y} = instantiate_eform x (EVar y) F]
              *)
  Admitted.

  Existing Instance fv_ctx.

  Lemma hasTableauNegAll :
    forall (Gamma : Con) (sigma : Substitution string Term) (S : SetOfString) (Sf : sko_record)
      (i : nat) (F : EForm) (x : string) (t : ETerm) (f : string)
      (hsko : is_sko (translate_ETerm [] t) (Neg (translate_EForm_ [x] F)) (fv Gamma) Sf),
      nth_error (forms Gamma) i = Some [[ ENeg (EAll x F) ]] -> symbol sko [[ t ]] hsko = f ->
      hasTableau_ sko (Gamma ,, [[ instantiate_eform x t (ENeg F) ]]) S Sf sigma ->
      hasTableau_ sko Gamma S (add_symbol f (translate_EForm_ [x] F) Sf) sigma.
  Proof.
    intros ????????? hsko e [] htab.
    apply (hasTableauNegAll sko Gamma S Sf sigma (translate_EForm_ [x] F) [[ t ]] hsko).
    - cbn in e |- *; eapply con_nth_in; eauto.
    - admit. (* TODO: [is_sko t F Sf S -> ~(y \in fv F) -> F{0 \to t} = instantiate_eform x t F] *)
  Admitted.

  Lemma hasTableauEx :
    forall (Gamma : Con) (sigma : Substitution string Term) (S : SetOfString) (Sf : sko_record)
      (i : nat) (F : EForm) (x : string) (t : ETerm) (f : string)
      (hsko : is_sko [[ t ]] (Neg (translate_EForm_ [x] (ENeg F))) (fv Gamma) Sf),
      nth_error (forms Gamma) i = Some [[ EEx x F ]] -> symbol sko [[ t ]] hsko = f ->
      hasTableau_ sko (Gamma ,, [[ ENeg (ENeg (instantiate_eform x t F)) ]] ,,
                         [[ instantiate_eform x t F ]]) S Sf sigma ->
      hasTableau_ sko Gamma S (add_symbol f (translate_EForm_ [x] (ENeg F)) Sf) sigma.
  Proof using Type.
    intros ????????? hsko e e' htab. unshelve eapply hasTableauNegAll.
    1: exact i.
    1: shelve.
    - eassumption.
    - assumption.
    - assumption.
    - unshelve eapply hasTableauNegNeg.
      1: exact 0.
      1: shelve.
      1: reflexivity.
      assumption.
  Qed.

  Lemma hasTableauNegEx :
    forall (Gamma : Con) (sigma : Substitution string Term) (S : SetOfString) (Sf : sko_record)
      (i : nat) (F : EForm) (x : string) (y : string),
      nth_error (forms Gamma) i = Some [[ ENeg (EEx x F) ]] -> isFresh y S ->
      hasTableau_ sko (Gamma ,, [[EAll x (ENeg F)]] ,, [[ instantiate_eform x (EVar y) (ENeg F) ]])
        S Sf sigma -> hasTableau_ sko Gamma (add y S) Sf sigma.
  Proof using Type.
    intros ???????? e hfresh htab. unshelve eapply hasTableauNegNeg.
    - exact i.
    - exact (EAll x (ENeg F)).
    - now cbn in e |- *.
    - unshelve eapply hasTableauAll.
      1: exact 0.
      3: reflexivity.
      all: auto.
  Qed.
End HasTableauLemmas.

(** ** 7. Tactics *)

Ltac esimpl :=
  cbn;
  repeat (destruct eqDec; cbn);
  try congruence.

Ltac set_decide :=
  cbn; unfold disjoint;
  try (repeat split; cbn); esimpl;
  repeat (progress (rewrite !empty_unitl || rewrite !empty_unitr || erewrite union_idemp));
  repeat (progress (rewrite !empty_disjointl || rewrite !empty_disjointr));
  repeat (progress (match goal with
  | [ |- forall x : (SetOfTerm_.SetOfX_.In ?y ?S), ?P ] =>
      let H := fresh x in intro H; inversion H; subst
  | [ |- forall x : (SetOfString_.SetOfX_.In ?y ?S), ?P ] =>
      let H := fresh x in intro H; inversion H; subst
  | [ |-  ~(SetOfTerm_.SetOfX_.In ?y ?S) ] =>
      let H := fresh "H" in intro H; inversion H; subst
  | [ |-  ~(SetOfString_.SetOfX_.In ?y ?S) ] =>
      let H := fresh "H" in intro H; inversion H; subst
  | [ H : SetOfTerm_.SetOfX_.Raw.InT ?x SetOfTerm_.SetOfX_.Raw.Leaf |- _ ] => inversion H
  | [ H : SetOfString_.SetOfX_.Raw.InT ?x SetOfString_.SetOfX_.Raw.Leaf |- _ ] => inversion H
  | [ e : Free ?x = Free ?y |- _ ] => injection e => e'; subst
  | [ e : ?x = ?y |- _ ] => try (inversion e; fail)
  | _ => idtac
  end));
  try (SetOfTerm_.SetOfXDecide.fsetdec);
  try (SetOfString_.SetOfXDecide.fsetdec).
