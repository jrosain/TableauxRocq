(** * Semantics: semantics of first-order logic. *)

From Corelib Require Import Morphisms.

From Stdlib Require Import Classical.

From Tableaux Require Import Prelude.All.
From Tableaux Require Import Syntax.

Section SemanticsDef.
  Context {pred func var : Atom}.

  Class Model :=
    { car :> Type
    ; interp_func : func -> list car -> car
    ; interp_pred : pred -> list car -> Prop
    ; non_empty : car }.

  Definition env (M : Model) (A : Type) := A -> option M.

  Definition empty_env (M : Model) (A : Type) : env M A := fun _ => None.

  Class Interpret (M : Model) (A B : Type) :=
    interpret : list M -> env M var -> A -> B.

  #[global] Instance interpret_term `{M : Model} : Interpret M (Term_ func var) M :=
    fun rho sigma =>
      fix F (t : Term_ func var) : M :=
        match t with
        | Bound n => option_get non_empty (nth_error rho n)
        | Free  x => option_get non_empty (sigma x)
        | Fun f l => interp_func f (map F l)
        end.

  #[global] Instance interpret_form_ (M : Model) : Interpret M (Form_ pred func var) Prop :=
    fix rec (rho : list M) (sigma : env M var) (F : Form_ pred func var) : Prop :=
      match F with
      | Bot        => False
      | Pred p l => interp_pred p (map (interpret_term rho sigma) l)
      | Neg F      => ~ (rec rho sigma F)
      | Or F G   => rec rho sigma F \/ rec rho sigma G
      | All F    => forall (x : M), rec (x :: rho) sigma F
      end.

  Definition is_valid (F : Form_ pred func var) :=
    forall (M : Model), interpret_form_ M [] (empty_env M var) F.

  Definition is_countersat (F : Form_ pred func var) :=
    forall (M : Model), ~(interpret_form_ M [] (empty_env M var) F).

  Definition equiv (F G : Form_ pred func var) :=
    forall (M : Model), interpret_form_ M [] (empty_env M var) F <->
                     interpret_form_ M [] (empty_env M var) G.

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
    intros F G H hequ1 hequ2 M. specialize (hequ1 M); specialize (hequ2 M).
    rewrite hequ1 hequ2 //.
  Qed.

  #[global] Instance equiv_equiv : Equivalence equiv.
  Proof using Type.
    constructor.
    - apply equiv_refl.
    - apply equiv_sym.
    - apply equiv_trans.
  Qed.

  #[global] Instance equiv_proper_interp (M : Model) :
    Proper (equiv ==> iff) (interpret_form_ M [] (empty_env M var)).
  Proof using Type.
    intros F G hequ.
    now specialize (hequ M).
  Qed.
End SemanticsDef.

Arguments Model : clear implicits.
Arguments Interpret {_ _ _} _ _ _.
Arguments interpret {_ _ _} _ {_ _ _} _ _ _.

Notation "\models F" := (is_valid F) (at level 40).
Notation "[[ M # rho # sigma |- F ]]" := (interpret M rho sigma F).
Notation "F \equiv G" := (equiv F G) (at level 30).

Fixpoint ls_to_form {pred func var : Atom} (Gamma : list (Form_ pred func var))
  : Form_ pred func var :=
  match Gamma with
  | [] => Neg Bot
  | F :: Fs => Neg (Or (Neg F) (Neg (ls_to_form Fs)))
  end.

Notation "Gamma \models F" := (is_valid (Or (Neg (ls_to_form Gamma)) F)) (at level 40).

Section SemanticsFacts.
  Context {pred func var : Atom}.

  Let Form := Form_ pred func var.
  Let Term := Term_ func var.

  Lemma in_form_list_models :
    forall (F : Form) (Gamma : list Form),
      List.In F Gamma -> Gamma \models F.
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
      Gamma \models Bot -> Gamma \models F.
  Proof using Type.
    intros F Gamma Hmodels M. cbn.
    specialize (Hmodels M). cbn in Hmodels. destruct Hmodels as [H | contra].
    + now left.
    + inversion contra.
  Qed.

  Lemma models_iff :
    forall (F : Form) (Gamma : list Form),
      (Gamma \models F) <-> ((Neg F :: Gamma) \models Bot).
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
      Gamma \models F -> Gamma \models Neg F -> Gamma \models Bot.
  Proof using Type.
    intros F Gamma HF HNF M.
    specialize (HF M); specialize (HNF M); cbn in HF, HNF |- *.
    destruct HF, HNF; auto.
  Qed.

  Lemma extend_with_equiv_form :
    forall (F G : Form) (Gamma : list Form),
      (F :: Gamma) \models Bot -> F \equiv G -> List.In G Gamma -> Gamma \models Bot.
  Proof using Type.
    intros F G Gamma hext hequiv hin M.
    specialize (hext M); cbn in *. left; intro save. destruct hext; auto.
    apply H. intros [HF | HG]; auto.
    have HG := in_form_list_models G Gamma hin M. cbn in HG. destruct HG; auto.
    apply HF. now rewrite hequiv.
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
    intros F G H M. specialize (H M). cbn; rewrite H //.
  Qed.

  Lemma or_equiv :
    forall (F1 F2 G1 G2 : Form), F1 \equiv G1 -> F2 \equiv G2 -> Or F1 F2 \equiv Or G1 G2.
  Proof using Type.
    intros ???? H1 H2 M.
    specialize (H1 M); specialize (H2 M); cbn.
    rewrite H1 H2 //.
  Qed.

  Lemma or_comm :
    forall (F G : Form), Or F G \equiv Or G F.
  Proof using Type.
    intros F G M. cbn. firstorder.
  Qed.

  Lemma extend_with_double_equiv_form :
    forall (F1 F2 G : Form) (Gamma : list Form),
      (F1 :: F2 :: Gamma) \models Bot -> Neg (Or (Neg F1) (Neg F2)) \equiv G -> List.In G Gamma -> Gamma \models Bot.
  Proof using Type.
    intros F1 F2 G Gamma hext hequiv hin M.
    specialize (hext M); cbn in *. left; intro save. destruct hext; auto.
    specialize (hequiv M). apply H. intro H'.
    have H0 : ~ interpret_form_ M [] (empty_env M var) F1 \/
                (~ interpret_form_ M [] (empty_env M var) F2 \/
                   ~ interpret_form_ M [] (empty_env M var) (ls_to_form Gamma)).
    { destruct H'.
      - now left.
      - right. now apply NNPP. }
    clear H H'. rewrite -or_assoc in H0. destruct H0.
    - have HG : ~(interpret_form_ M [] (empty_env M var) G).
      { rewrite -hequiv. cbn. intro. now apply H0. }
      apply HG. have H1 := (in_form_list_models G Gamma hin M); cbn in H1.
      destruct H1; auto. exfalso. now apply H0.
    - now apply H.
  Qed.

  Lemma double_extend_with_equiv_form :
    forall (F1 F2 G : Form) (Gamma : list Form),
      (F1 :: Gamma) \models Bot -> (F2 :: Gamma) \models Bot -> Or F1 F2 \equiv G -> List.In G Gamma -> Gamma \models Bot.
  Proof using Type.
    intros ???? HF1 HF2 hequ hin M.
    specialize (HF1 M); specialize (HF2 M).
    cbn in HF1, HF2 |- *. left; intro save. destruct HF1; auto.
    apply H. intros [HF1 | contra]; auto.
    destruct HF2; auto. apply H0. intros [HF2 | contra]; auto.
    have H1 : ~ interpret_form_ M [] (empty_env M var) G.
    { rewrite -hequ; cbn. intros []; auto. }
    apply in_form_list_models in hin. specialize (hin M). destruct hin; auto.
  Qed.

  (* Lemma term_env_inst_commutes : *)
  (*   forall (M : Model pred func) (rho : list M) (sigma : env M var) (t u : Term) (n : nat), *)
  (*     (nth_error rho n = Some [[ M # rho # sigma |- t ]]) -> *)
  (*     interpret_term rho sigma (u {n \to t}) = *)
  (*       interpret_term rho sigma u. *)
  (* Proof using Type. *)
  (*   intros ?????? e. induction u using term_ind; cbn; auto. *)
  (*   - destruct (n == n0); subst. *)
  (*     + now rewrite e. *)
  (*     + reflexivity. *)
  (*   - rewrite map_map. *)
  (*     have hmap : (map (fun u => interpret_term rho sigma u {n \to t}) l) = *)
  (*                   (map (interpret_term rho sigma) l). *)
  (*     { induction l as [|v vs IHvs]; auto. *)
  (*       cbn. rewrite IHvs. *)
  (*       - now apply Forall_tail in X. *)
  (*       - apply Forall_In with (x := v) in X. *)
  (*         2: now right. *)
  (*         now rewrite X. } *)
  (*     rewrite hmap //. *)
  (* Qed. *)

  (* Lemma form_env_inst_commutes : *)
  (*   forall (M : Model pred func) (rho0 rho1 : list M) (sigma : env M var) (F : Form) (t : Term) (n : nat), *)
  (*     (forall x, [[ M # rho0 # sigma |- t ]] = [[ M # x :: rho0 # sigma |- t ]]) -> *)
  (*     (nth_error rho1 n = Some [[ M # rho0 # sigma |- t ]]) -> *)
  (*     interpret_form_ M rho0 sigma (F {n \to t}) = *)
  (*       interpret_form_ M rho1 sigma F. *)
  (* Proof. *)
  (*   intros ???????? e. generalize dependent n; generalize dependent rho0; revert rho1. *)
  (*   induction F; auto; cbn; intros rho1 rho0 hequ n e. *)
  (*   - rewrite map_map. *)
  (*     have hmap : (map (fun u => interpret_term rho0 sigma u {n \to t}) l) = *)
  (*                   (map (interpret_term rho1 sigma) l). *)
  (*     { induction l as [|v vs IHvs]; auto; cbn. *)
  (*       admit. (* rewrite term_env_inst_commutes; auto. now rewrite IHvs. *) } *)
  (*     rewrite hmap //. *)
  (*   - erewrite IHF; eauto. *)
  (*   - erewrite IHF1, IHF2; eauto. *)
  (*   - apply prodext=>x. erewrite IHF; eauto. *)
  (*     (* rewrite PeanoNat.Nat.add_1_r nth_error_S; cbn. *) *)
  (*     Admitted. *)

  (* Lemma instantiate_by_free_equiv_all : *)
  (*   forall (F : Form) (x : var), *)
  (*     isFresh x (fv F) -> *)
  (*     (F {0 \to Free x}) \equiv All F. *)
  (* Proof. *)
  (*   intros F x hfresh M; cbn. split. *)
  (*   - intros hinterp y. unshelve erewrite form_env_inst_commutes in hinterp. *)
  (*     + exact [y]. *)
  (*     + assumption. *)
  (*     + reflexivity. *)
  (*     + admit. *)
  (*   - intros hinterp. unshelve erewrite form_env_inst_commutes. *)
End SemanticsFacts.
