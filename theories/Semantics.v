(** * Semantics: semantics of first-order logic. *)

From Corelib Require Import Morphisms.

From Stdlib Require Import Classical.
From Stdlib Require Import Lia.
From Stdlib Require Import Logic.IndefiniteDescription.

From Tableaux Require Import Prelude.All.
From Tableaux Require Import Syntax.

Section SemanticsDef.
  Context {pred func var : Atom}.

  Class Model :=
    { car :> Atom
    ; interp_func : func -> list car -> car
    ; interp_pred : pred -> list car -> Prop
    ; non_empty : car }.

  Definition env (M : Model) (A : Type) := A -> option M.

  Definition empty_env (M : Model) (A : Type) : env M A := fun _ => None.

  Class Interpret (M : Model) (A B : Type) :=
    interpret : list M -> env M var -> A -> B.

  #[global] Instance interpret_list {A B : Type} (M : Model) `{@Interpret M A B} :
    Interpret M (list A) (list B) :=
    fun rho sigma =>
      fix F (t : list A) : list B :=
        match t with
        | [] => []
        | x :: xs => interpret rho sigma x :: F xs
        end.

  #[global] Instance interpret_term (M : Model) : Interpret M (Term func var) M :=
    fun rho sigma =>
      fix F (t : Term func var) : M :=
        match t with
        | Bound n => option_get non_empty (nth_error rho n)
        | Free  x => option_get non_empty (sigma x)
        | Fun f l => interp_func f (map F l)
        end.

  #[global] Instance interpret_form (M : Model) : Interpret M (Form pred func var) Prop :=
    fix rec (rho : list M) (sigma : env M var) (F : Form pred func var) : Prop :=
      match F with
      | Bot        => False
      | Pred p l => interp_pred p (map (interpret_term M rho sigma) l)
      | Neg F      => ~ (rec rho sigma F)
      | Or F G   => rec rho sigma F \/ rec rho sigma G
      | All F    => forall (x : M), rec (x :: rho) sigma F
      end.

  Definition is_valid (F : Form pred func var) :=
    forall (M : Model), interpret_form M [] (empty_env M var) F.

  Definition is_satisfiable (F : Form pred func var) :=
    exists (M : Model), forall (mu : env M var),
      interpret_form M [] mu F.

  Definition equiv (F G : Form pred func var) :=
    forall (M : Model) (rho : list M) (sigma : env M var),
      interpret_form M rho sigma F <-> interpret_form M rho sigma G.

  Definition imply (F G : Form pred func var) :=
    forall (M : Model) (sigma : env M var),
      interpret_form M [] sigma F -> interpret_form M [] sigma G.

  #[global] Instance equiv_refl : Reflexive equiv.
  Proof using Type.
    intros F M. reflexivity.
  Qed.

  #[global] Instance equiv_sym : Symmetric equiv.
  Proof using Type.
    intros F G Hequ M. specialize (Hequ M). now symmetry.
  Qed.

  #[global] Instance equiv_trans : Transitive equiv.
  Proof using Type.
    intros F G H hequ1 hequ2 M rho sigma. specialize (hequ1 M rho sigma); specialize (hequ2 M rho sigma).
    rewrite hequ1 hequ2 //.
  Qed.

  #[global] Instance equiv_equiv : Equivalence equiv.
  Proof using Type.
    constructor.
    - apply equiv_refl.
    - apply equiv_sym.
    - apply equiv_trans.
  Qed.

  Lemma equiv_imply :
    forall (F G : Form pred func var),
      equiv F G -> imply F G.
  Proof using Type.
    intros ?? hequiv M sigma. specialize (hequiv M [] sigma). apply hequiv.
  Qed.

  #[global] Instance equiv_proper_interp (M : Model) :
    Proper (equiv ==> iff) (interpret_form M [] (empty_env M var)).
  Proof using Type.
    intros F G hequ.
    now specialize (hequ M).
  Qed.
End SemanticsDef.

Arguments Model : clear implicits.
Arguments Interpret {_ _ _} _ _ _.
Arguments interpret {_ _ _} _ {_ _ _} _ _ _.

Notation "|= F" := (is_valid F) (at level 40).
Notation "[[ M # rho # sigma '|= F ]]" := (interpret M rho sigma F).
Notation "F \equiv G" := (equiv F G) (at level 30).
Notation "Gamma |= F" := (is_valid (Or (Neg (ls_to_form Gamma)) F)) (at level 40).

Section SemanticsFacts.
  Context {pred func var : Atom} `{set_nat : set nat}.

  Let Form := Form pred func var.
  Let Term := Term func var.

  Lemma ls_to_form_commutes :
    forall (Gamma : list Form) (F G : Form),
      ls_to_form (F :: G :: Gamma) \equiv ls_to_form (Neg (Or (Neg F) (Neg G)) :: Gamma).
  Proof using Type.
    intros. split; intros h; cbn in *.
    - intros [hFG | hGamma].
      + apply NNPP in hFG. destruct hFG as [hnF | hnG].
        * apply h. now left.
        * apply h. right. intro h'; apply h'. now left.
      + apply h. right. intro h'; apply h'. now right.
    - intros [hF | hG].
      + apply h. left. intro h'; apply h'. now left.
      + apply NNPP in hG; destruct hG as [hG | hG].
        * apply h. left. intro h'; apply h'. now right.
        * apply h; now right.
  Qed.

  Lemma is_satisfiable_is_not_countersat :
    forall (F : Form),
      is_satisfiable F -> |= Neg F -> False.
  Proof using Type.
    intros F hsat hfalse. destruct hsat as (M & hsat).
    specialize (hfalse M); specialize (hsat (empty_env M var)).
    now apply hfalse.
  Qed.

  Lemma is_satisfiable_equiv :
    forall (F G : Form), F \equiv G -> is_satisfiable F <-> is_satisfiable G.
  Proof using Type.
    intros F G hequiv. split; intros (M & h); exists M; intros mu; specialize (h mu).
    - now rewrite -(hequiv M).
    - now rewrite (hequiv M).
  Qed.

  Lemma in_form_list_models :
    forall (F : Form) (Gamma : list Form),
      List.In F Gamma -> Gamma |= F.
  Proof using Type.
    intros ?? Hin. induction Gamma as [|G Gs IHGs]; inversion Hin.
    - rewrite !H in IHGs |- *.
      intros M; cbn. apply NNPP=>rem. apply rem. right.
      apply NNPP=>rem'. apply rem. left. intros H0. apply H0. now left.
    - intros M; cbn. specialize (IHGs H M). destruct IHGs as [HGs | HF].
      + left. intro H0. apply H0. now right.
      + now right.
  Qed.

  Lemma explosion_principle :
    forall (F : Form) (Gamma : list Form),
      Gamma |= Bot -> Gamma |= F.
  Proof using Type.
    intros F Gamma Hmodels M. cbn.
    specialize (Hmodels M). cbn in Hmodels. destruct Hmodels as [H | contra].
    + now left.
    + inversion contra.
  Qed.

  Lemma models_iff :
    forall (F : Form) (Gamma : list Form),
      (Gamma |= F) <-> ((Neg F :: Gamma) |= Bot).
  Proof using Type.
    intros F Gamma. split.
    - intros Hmodels M; cbn. specialize (Hmodels M). cbn in Hmodels.
      destruct Hmodels.
      + left. intros H0; apply H0. now right.
      + left. intros H0; apply H0. left; intro H1; now apply H1.
    - intros Hmodels M; specialize (Hmodels M); cbn in Hmodels |- *.
      destruct Hmodels; auto. apply NNPP=>rem. apply H. intros [HF | HGamma].
      + apply rem. right. now apply NNPP.
      + apply rem. now left.
  Qed.

  Lemma models_P_neg_P :
    forall (F : Form) (Gamma : list Form),
      Gamma |= F -> Gamma |= Neg F -> Gamma |= Bot.
  Proof using Type.
    intros F Gamma HF HNF M.
    specialize (HF M); specialize (HNF M); cbn in HF, HNF |- *.
    destruct HF, HNF; auto.
  Qed.

  Lemma in_form_list_interp :
    forall {F : Form} {Gamma : list Form} {M : Model pred func}
      {rho : list M} {sigma : env M var},
      List.In F Gamma -> [[ M # rho # sigma '|= ls_to_form Gamma ]] -> [[ M # rho # sigma '|= F ]].
  Proof using Type.
    intros ????? hin hinterp; induction Gamma as [|G Gs IHGs]; inversion hin; subst.
    - cbn in hinterp |- *. apply NNPP => save. apply hinterp; now left.
    - apply IHGs; auto. apply NNPP => save; apply hinterp; now right.
  Qed.

  Lemma extend_with_equiv_form :
    forall (F G : Form) (Gamma : list Form) (M : Model pred func)
      (rho : list M) (sigma : env M var),
      [[ M # rho # sigma '|= ls_to_form Gamma ]] -> F \equiv G -> List.In G Gamma ->
      [[ M # rho # sigma '|= ls_to_form (F :: Gamma) ]].
  Proof using Type.
    intros ?????? hinterp hequiv hin. cbn. intros [hnF | hnG]; auto.
    have hG := in_form_list_interp hin hinterp.
    specialize (hequiv M rho sigma). unfold interpret in hG.
    rewrite -hequiv in hG; auto.
  Qed.

  Lemma extend_with_imply_form :
    forall (F G : Form) (Gamma : list Form) (M : Model pred func)
      (sigma : env M var),
      [[ M # [] # sigma '|= ls_to_form Gamma ]] -> imply G F -> List.In G Gamma ->
      [[ M # [] # sigma '|= ls_to_form (F :: Gamma) ]].
  Proof using Type.
    intros ????? hinterp himply hin. cbn. intros [hnF | hnG]; auto.
    have hG := in_form_list_interp hin hinterp.
    now apply hnF, himply.
  Qed.

  Lemma interp_list_commute :
    forall (F G : Form) (Gamma : list Form) (M : Model pred func)
      (rho : list M) (sigma : env M var),
      [[ M # rho # sigma '|= ls_to_form (Neg (Or (Neg F) (Neg G)) :: Gamma) ]] ->
      [[ M # rho # sigma '|= ls_to_form (F :: G :: Gamma) ]].
  Proof using Type.
    intros ?????? hinterp. cbn in *. intros [hnF | hinterp'].
    - apply hinterp. left. intros h; apply h. now left.
    - apply NNPP in hinterp'; destruct hinterp' as [hnG | hnG].
      + apply hinterp. left; intro h; apply h. now right.
      + apply hinterp; now right.
  Qed.

  Lemma neg_neg_equiv :
    forall (F : Form), F \equiv Neg (Neg F).
  Proof using Type.
    intros F M; cbn. split.
    - intros H H'; now apply H'.
    - apply NNPP.
  Qed.

  Lemma neg_equiv :
    forall (F G : Form), F \equiv G -> Neg F \equiv Neg G.
  Proof using Type.
    intros F G H M rho sigma. specialize (H M). cbn; rewrite H //.
  Qed.

  Lemma or_equiv :
    forall (F1 F2 G1 G2 : Form), F1 \equiv G1 -> F2 \equiv G2 -> Or F1 F2 \equiv Or G1 G2.
  Proof using Type.
    intros ???? H1 H2 M rho sigma.
    specialize (H1 M rho sigma); specialize (H2 M rho sigma); cbn.
    rewrite H1 H2 //.
  Qed.

  Lemma or_comm :
    forall (F G : Form), Or F G \equiv Or G F.
  Proof using Type.
    intros F G M. cbn. firstorder.
  Qed.

  Lemma ls_to_form_app :
    forall (Gamma Gamma' : list Form),
      ls_to_form (Gamma ++ Gamma')%list \equiv Neg (Or (Neg (ls_to_form Gamma)) (Neg (ls_to_form Gamma'))).
  Proof using Type.
    intros ??; induction Gamma as [|F Fs IHFs].
    - cbn; split; intro hinterp.
      + intros [hnG | contra]; auto.
      + apply NNPP => save; apply hinterp. now right.
    - cbn. apply neg_equiv. etransitivity.
      + apply or_equiv.
        * reflexivity.
        * apply neg_equiv, IHFs.
      + split; intro hinterp; cbn in *.
        * destruct hinterp; auto.
          apply NNPP => save. apply H. intros []; auto.
          apply save. left. intro hinterp'; apply hinterp'. now right.
        * destruct hinterp; auto.
          apply NNPP => hinterp. apply H. intros [].
          -- apply hinterp; now left.
          -- apply hinterp; right. intro h0. apply h0. now left.
  Qed.

  Lemma isLocallyClosed_interp_env :
    forall (M : Model pred func) (rho0 rho1 : list M) (sigma : env M var) (t : Term),
      isLocallyClosed t ->
      interpret_term M rho0 sigma t = interpret_term M rho1 sigma t.
  Proof using Type.
    intros ??????. induction t using term_ind.
    - red in H. cbn in H. apply is_empty_spec with (x := n) in H.
      + inversion H.
      + now apply singleton_spec.
    - now cbn.
    - cbn. have hmap : map (interpret_term M rho0 sigma) l =
                         map (interpret_term M rho1 sigma) l.
      { induction l as [|u us IHus]; cbn; auto.
        rewrite IHus.
        - red in H |- *. cbn in H.
          now apply is_empty_union2 in H.
        - now apply Forall_tail in X.
        - apply Forall_In with (x := u) in X.
          2: now right.
          rewrite X; auto.
          red in H; cbn in H. unfold isLocallyClosed.
          now apply is_empty_union1 in H. }
      rewrite hmap //.
  Qed.

  Lemma term_env_inst_commutes :
    forall (M : Model pred func) (rho : list M) (sigma : env M var) (t u : Term),
      isLocallyClosed u ->
      interpret_term M rho sigma (t {#|rho| \to u}) =
        interpret_term M (rho ++ [ [[ M # rho # sigma '|= u ]] ])%list sigma t.
  Proof using Type.
    intros ??????. induction t using term_ind.
    - cbn. rewrite -match_eq_dec_eq_bool; destruct (#|rho| == n).
      + rewrite nth_error_app2.
        * rewrite e; apply le_n.
        * rewrite e; cbn. rewrite PeanoNat.Nat.sub_diag; now cbn.
      + cbn. destruct (nth_error rho n) eqn:e.
        * have hlt : n < #|rho|.
          { apply Compare_dec.not_ge. intro hgt. inversion hgt; auto.
            subst. apply nth_error_split in e.
            destruct e as [l1 [l2 [e0 e1] ] ].
            subst. rewrite length_app e1 in H0.
            cbn in H0. lia. }
          rewrite nth_error_app1; auto.
          now rewrite e.
        * have hgt : #|rho ++ [ [[ M # rho # sigma '|= u ]] ]|  <= n.
          { rewrite nth_error_None in e.
            have hlt : #|rho| < n by lia.
            rewrite last_length. lia. }
          rewrite -nth_error_None in hgt.
          now rewrite hgt.
    - now cbn.
    - cbn. rewrite map_map.
      have hmap : (map (fun x : Term => interpret_term M rho sigma x {#| rho | \to u}) l) =
                    (map (interpret_term M (rho ++ [ [[M # rho # sigma '|= u]] ])%list sigma) l).
      { induction l as [|v vs IHvs]; auto; cbn.
        rewrite IHvs.
        - now apply Forall_tail in X.
        - apply Forall_In with (x := v) in X.
          2: now right.
          rewrite X //. }
      rewrite hmap //.
  Qed.

  Lemma form_env_inst_commutes :
    forall (M : Model pred func) (rho : list M) (sigma : env M var) (F : Form) (t : Term),
      isLocallyClosed t ->
      interpret_form M rho sigma (F {#|rho| \to t}) =
        interpret_form M (rho ++ [ [[ M # rho # sigma '|= t ]] ])%list sigma F.
  Proof using Type.
    intros ??????. revert rho. induction F; auto; cbn; intros rho.
    - rewrite map_map.
      have hmap : (map (fun u => interpret_term M rho sigma u {#|rho| \to t}) l) =
                    (map (interpret_term M (rho ++ [ [[ M # rho # sigma '|= t ]] ])%list sigma) l).
      { induction l as [|v vs IHvs]; auto; cbn.
        rewrite IHvs term_env_inst_commutes; auto. }
      rewrite hmap //.
    - erewrite IHF; eauto.
    - erewrite IHF1, IHF2; eauto.
    - apply prodext=>x. have e := (IHF (x :: rho)).
      cbn in e. rewrite PeanoNat.Nat.add_1_r e.
      do 4 f_equal. unfold interpret.
      apply isLocallyClosed_interp_env; auto.
  Qed.

  Lemma instantiate_imply_all :
    forall (F : Form) (t : Term),
      isLocallyClosed t ->
      imply (All F) (F {0 \to t}).
  Proof using Type.
    intros F x hclosed M sigma hinterp; cbn in *.
    rewrite form_env_inst_commutes.
    - red. apply hclosed.
    - apply hinterp.
  Qed.

  Lemma isClosed_interp_term_env_eq :
    forall (M : Model pred func) (t : Term) (rho : list M) (sigma mu : env M var),
      isClosed t ->
      [[ M # rho # sigma '|= t ]] = [[ M # rho # mu '|= t ]].
  Proof using Type.
    intros ????? hclosed; induction t using term_ind; cbn; auto.
    - unfold isClosed in hclosed; cbn in hclosed;
        apply is_empty_spec with (x := a) in hclosed.
      + inversion hclosed.
      + now apply singleton_spec.
    - apply f_equal. induction l as [|u us IHus]; cbn; auto.
      rewrite IHus.
      + unfold isClosed in hclosed |- *; cbn in *.
        rewrite set_fold_left in hclosed. now apply is_empty_union2 in hclosed.
      + now apply Forall_tail in X.
      + apply Forall_inv in X; rewrite X //.
        unfold isClosed in hclosed |- *; cbn in *.
        rewrite set_fold_left in hclosed. apply is_empty_union1 in hclosed.
        now rewrite empty_unitl in hclosed.
  Qed.

  Lemma isClosed_interp_form_env_eq :
    forall (M : Model pred func) (F : Form) (rho : list M) (sigma mu : env M var),
      isClosed F ->
      [[ M # rho # sigma '|= F ]] = [[ M # rho # mu '|= F ]].
  Proof using Type.
    intros ????? hclosed; revert rho; induction F; cbn; auto.
    - intro; apply f_equal. induction l as [|t ts IHts]; cbn; auto.
      rewrite IHts; unfold isClosed in hclosed |- *; cbn in *.
      + rewrite set_fold_left in hclosed; now apply is_empty_union2 in hclosed.
      + f_equal. change ([[ M # rho # sigma '|= t ]] = [[ M # rho # mu '|= t ]]).
        apply isClosed_interp_term_env_eq. unfold isClosed;
          rewrite set_fold_left empty_unitl in hclosed; now apply is_empty_union1 in hclosed.
    - intros; rewrite IHF //.
    - intros; rewrite IHF1; [| rewrite IHF2 //];
        unfold isClosed in hclosed |- *; cbn in *.
      + now apply is_empty_union1 in hclosed.
      + now apply is_empty_union2 in hclosed.
    - intro; apply prodext=>x; rewrite IHF; auto.
  Qed.

  Definition subst_to_env (M : Model pred func)
    (sigma : Substitution var Term) : env M var :=
    fun x => Some ([[ M # [] # empty_env M var '|= sigma x ]]).

  Lemma subst_commutes_with_env_terms :
    forall (M : Model pred func) (t : Term) (rho : list M) (sigma : Substitution var Term),
      [[ M # rho # empty_env M var '|= t@[sigma] ]] =
        [[ M # rho # subst_to_env M sigma '|= t ]].
  Proof using Type.
    intros. induction t using term_ind; cbn; try reflexivity.
    - apply isLocallyClosed_interp_env. apply isSubst.
    - apply f_equal. induction l as [|u us IHus]; cbn; auto.
      rewrite IHus.
      + now apply Forall_tail in X.
      + apply Forall_inv in X. rewrite X //.
  Qed.

  Lemma subst_commutes_with_env_forms :
    forall (M : Model pred func) (F : Form) (rho : list M) (sigma : Substitution var Term),
      [[ M # rho # empty_env M var '|= F@[sigma] ]] <->
        [[ M # rho # subst_to_env M sigma '|= F ]].
  Proof using Type.
    intros M F. induction F; cbn.
    - reflexivity.
    - intros.
      have e : map (interpret_term M rho (empty_env M var)) (map (fun t : Term => t@[sigma]) l) =
                 map (interpret_term M rho (subst_to_env M sigma)) l.
      { induction l as [|t ts IHts]; cbn; auto.
        rewrite IHts. f_equal.
        change ([[ M # rho # empty_env M var '|= t@[sigma] ]] =
                  [[ M # rho # subst_to_env M sigma '|= t ]]).
        apply subst_commutes_with_env_terms. }
      now rewrite e.
    - intros ??. rewrite IHF //.
    - intros; rewrite IHF1 IHF2 //.
    - intros. split; intros h x.
      + rewrite -IHF //.
      + rewrite IHF //.
  Qed.
End SemanticsFacts.

(** ** Replacement model *)

(** We define a [ReplacementModel] to validate Skolemization.

    This is a model where the function to interpret functions is replaced by another function,
    which makes the given function symbol together with the given variables true whenever
    the delta formula is true. To do so, we use the term given by [satisfy_delta] together with
    a choice function that makes it possible to extract this term.

    This choice function is unavoidable, as in and of itself, Skolemization uses the axiom of
    choice. *)
Section ReplaceInterpFunc.
  Context {pred func var : Atom} (M : Model pred func) (F : Form pred func var).

  Lemma satisfy_delta :
    forall (mu : env M var),
    exists (c : M), [[ M # [] # mu '|= Neg (All F) ]] -> [[ M # [c] # mu '|= Neg F ]].
  Proof using Type.
    intros ?. destruct (classic ([[M # [] # mu '|= Neg (All F)]])) as [hdelta | hndelta].
    - apply NNPP => save. apply hdelta. intro c. apply NNPP => hdelta'.
      apply save. exists c. now intro.
    - exists non_empty. intro. exfalso. now apply hndelta.
  Qed.

  (** Application of the axiom of choice on [satisfying_delta]. *)
  Definition satisfying_symbol (mu : env M var) :
    { c : M | [[ M # [] # mu '|= Neg (All F) ]] -> [[ M # [c] # mu '|= Neg F ]] }.
  Proof using Type. apply constructive_indefinite_description, satisfy_delta. Qed.

  Context (f : func) (vs : list var).

  Fixpoint mk_env (l : list (var * M)) : env M var :=
    match l with
    | [] => empty_env M var
    | (x, c) :: xs =>
        fun (y : var) => if eqb x y then Some c
                      else mk_env xs y
    end.

  Definition replace_interp_func (f' : func) (l : list M) : M :=
    if eqb f f' then proj1_sig (satisfying_symbol (mk_env (combine vs l)))
    else @interp_func _ _ M f' l.
End ReplaceInterpFunc.

Section RealReplacementModel.
  Context `{set_nat : set nat} {pred func var : Atom} (M : Model pred func).

  Definition ReplacementModel (f : func -> list M -> M) :=
    {| car := M
    ;  interp_func := f
    ;  interp_pred := interp_pred
    ;  non_empty := non_empty |}.

  Let Form := Form pred func var.
  Let Term := Term func var.

  (** Properties of [ReplacementModel] with [replace_interp_func]. *)
  Context (F : Form) (f : func) (vs : list var).

  Let M' := ReplacementModel (replace_interp_func M F f vs).
  Let t := Fun f (map (fun v : var => Free v) vs).

  Lemma satisfying_symbol_prop :
    forall (mu : env M var),
      exists (c : M),
        interpret_term M' [] mu t = c /\
          ([[ M # [] # mu '|= Neg (All F) ]] -> [[ M # [c] # mu '|= Neg F ]]).
  Proof.
    intros mu. exists (proj1_sig (satisfying_symbol M F mu)); split.
    - cbn; unfold replace_interp_func.
      rewrite -match_eq_dec_eq_bool; destruct (f == f).
      2: { exfalso; now apply n. }
      admit. (* yes: [mu] only matters on the given input. *)
    - apply (proj2_sig (satisfying_symbol M F mu)).
  Admitted.

  Lemma no_skolem_same_interp_term :
    forall (rho : list M) (mu : env M var) (u : Term),
      ~set_in f (function_symbols u) ->
      interpret_term M' rho mu u = interpret_term M rho mu u.
  Proof using F vs.
    intros ??? hfresh. induction u using term_ind; auto.
    cbn; unfold replace_interp_func.
    cbn in hfresh; rewrite set_fold_left in hfresh.
    rewrite -match_eq_dec_eq_bool; destruct (f == f0).
    - exfalso; apply hfresh. rewrite union_spec; left. now apply singleton_spec.
    - apply f_equal.
      apply NNPP => save; apply hfresh; rewrite union_spec; right; apply NNPP => hfresh';
        clear hfresh n; apply save; clear save.
      induction l as [|u us IHus]; auto; cbn.
      rewrite IHus.
      + now apply Forall_tail in X.
      + intro hin. apply hfresh'. cbn; rewrite set_fold_left union_spec; now right.
      + apply Forall_inv in X. rewrite X //.
        intro hin. apply hfresh'; cbn; rewrite set_fold_left union_spec empty_unitl; now left.
  Qed.

  Lemma no_skolem_same_interp_form :
    forall (rho : list M) (mu : env M var) (G : Form),
      ~set_in f (function_symbols G) ->
      interpret_form M' rho mu G = interpret_form M rho mu G.
  Proof using F t.
    intros ??? hnin; revert rho; induction G; intro rho; cbn; auto.
    - apply f_equal; cbn in hnin. induction l as [|u us IHus]; cbn; auto.
      rewrite IHus.
      + intro hin; apply hnin; cbn.
        rewrite set_fold_left union_spec; now right.
      + rewrite no_skolem_same_interp_term //.
        intro hin; apply hnin; cbn.
        rewrite set_fold_left union_spec empty_unitl; now left.
    - rewrite IHG; auto.
    - rewrite IHG1.
      + intro hin. apply hnin. rewrite union_spec; now left.
      + rewrite IHG2 //. intro hin; apply hnin; rewrite union_spec; now right.
    - apply prodext => c. rewrite IHG; auto.
  Qed.

  Lemma satisfies_opening_with_sko :
    forall (mu : env M var),
      ~set_in f (function_symbols F) ->
      [[ M # [] # mu '|= Neg (All F) ]] -> [[ M' # [] # mu '|= Neg F {0 \to Fun f (map (fun v => Free v) vs)} ]].
  Proof using set_nat.
    intros mu hnin hinterp.
    change [[ M' # [] # mu '|= (Neg F) {0 \to t} ]]; unfold interpret.
    rewrite (form_env_inst_commutes M' [] mu (Neg F) t).
    - unfold t, isLocallyClosed; cbn.
      induction vs; try now cbn.
      cbn. now rewrite empty_unitl.
    - rewrite app_nil_l.
      destruct (satisfying_symbol_prop mu) as (c & ht & himp).
      unfold interpret. rewrite ht.
      apply himp in hinterp.
      rewrite no_skolem_same_interp_form; auto.
  Qed.
End RealReplacementModel.
