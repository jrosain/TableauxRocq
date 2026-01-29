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
      6. helper lemmas to build a tableau more easily *)

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

  Fixpoint ls_to_eform (l : list EForm) : EForm :=
    match l with
    | [] => ETop
    | F :: Fs => EAnd F (ls_to_eform Fs)
    end.
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

    Lemma index_of_In' :
      forall (x : A) (l : list A) (n : nat), index_of x l = Some n -> List.In x l.
    Proof using Type.
      intros ??? e. have h := index_of_In x l n e.
      clear e. induction l as [|y ys IHys]; try now cbn in *.
      cbn in h |- *. destruct h; auto.
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

    Lemma index_of_rapp :
      forall (x : A) (l : list A),
        ~(List.In x l) -> index_of x (l ++ [x]) = Some #|l|.
    Proof using Type.
      intros ?? hnin. induction l as [|y ys IHys]; cbn.
      - rewrite EqBool_refl //.
      - cbn in hnin. destruct (y == x).
        + exfalso. apply hnin. now left.
        + have hnin' : ~(List.In x ys).
          { intro hin. apply hnin. now right. }
          specialize (IHys hnin'). rewrite -match_eq_dec_eq_bool.
          destruct (x == y); try congruence.
          rewrite IHys; now cbn.
    Qed.

    Lemma index_of_rapp' :
      forall (x y : A) (l : list A) (n : nat),
        ~(List.In x l) -> x <> y -> index_of y (l ++ [x]) = Some n -> n < #|l|.
    Proof using Type.
      intros ???? hnin e e'. generalize dependent n. induction l as [|z zs IHzs]; cbn;
        intros n e'.
      - cbn in e'. rewrite -match_eq_dec_eq_bool in e'. destruct (y == x); congruence. 
      - cbn in hnin, e, e'.
        rewrite -match_eq_dec_eq_bool in e'. destruct (y == z).
        + injection e' => <-; lia.
        + have h0 : ~List.In x zs.
          { intro hnin'. apply hnin; now right. }
          specialize (IHzs h0). destruct (index_of y (zs ++ [x])) eqn:eindex; cbn in *.
          * specialize (IHzs (Nat.pred n)).
            have e0 : Some n1 = Some (Nat.pred n).
            { injection e' => <-. rewrite PeanoNat.Nat.pred_succ //. }
            specialize (IHzs e0). lia.
          * inversion e'.
    Qed.

    Lemma index_of_rapp'' :
      forall (x y : A) (l : list A) (n : nat),
        ~(List.In x l) -> x <> y -> index_of y (l ++ [x]) = index_of y l.
    Proof using Type.
      intros ??? hnin e e'. induction l as [|z zs IHzs]; cbn.
      - rewrite -match_eq_dec_eq_bool. destruct (y == x); congruence.
      - rewrite -!match_eq_dec_eq_bool. destruct (y == z); auto.
        rewrite IHzs; auto.
        intro hin; apply e. now right.
    Qed.

    Lemma index_of_length :
      forall (x : A) (l : list A) (n : nat),
        index_of x l = Some n -> n < #|l|.
    Proof using Type.
      intros ??. induction l as [|y ys IHys]; cbn in *.
      - now intros.
      - intros; rewrite -match_eq_dec_eq_bool in H0.
        destruct (x == y).
        + injection H0 => <-. lia.
        + destruct (index_of x ys) eqn:e; cbn in *.
          * specialize (IHys (Nat.pred n)).
            have e1 : Some n1 = Some (Nat.pred n).
            { apply f_equal. injection H0 => <-. lia. }
            specialize (IHys e1).  replace n with (S (Nat.pred n)).
            { now apply Arith_base.lt_n_S_stt. }
            apply PeanoNat.Nat.succ_pred_pos. injection H0 => <-. lia.
          * inversion H0.
    Qed.

    Lemma index_of_prefix :
      forall (x : A) (l l0 l1 : list A) (n0 n1 : nat),
        List.In x l -> index_of x (l ++ l0) = Some n0 -> index_of x (l ++ l1) = Some n1 -> n0 = n1.
    Proof using Type.
      intros ?????? hin. revert n0 n1. induction l as [|y ys IHys];
        intros ?? e0 e1.
      - apply index_of_In' in e0. now cbn in e0.
      - cbn in e0, e1. rewrite -!match_eq_dec_eq_bool in e0, e1.
        destruct (x == y).
        + injection e0 => <-; now injection e1 => <-.
        + destruct (index_of x (ys ++ l0));
            destruct (index_of x (ys ++ l1)); cbn in *.
          * injection e0 => e0'; injection e1 => e1'.
            have e : Nat.pred n0 = Nat.pred n1.
            { apply IHys.
              2-3: apply f_equal; lia.
              destruct hin; auto. congruence. }
            have en0 : S (Nat.pred n0) = n0.
            { apply PeanoNat.Nat.succ_pred_pos. lia. }
            have en1 : S (Nat.pred n1) = n1.
            { apply PeanoNat.Nat.succ_pred_pos. lia. }
            lia.
          * inversion e1.
          * inversion e0.
          * inversion e0.
    Qed.

    Lemma index_of_None :
      forall (x : A) (l : list A),
        index_of x l = None -> ~List.In x l.
    Proof using Type.
      intros ?? e hin. induction l as [|y ys IHys]; cbn in *; auto.
      destruct hin.
      - rewrite -match_eq_dec_eq_bool in e. destruct (x == y); auto.
        inversion e.
      - rewrite -match_eq_dec_eq_bool in e. destruct (x == y); auto.
        + inversion e.
        + apply IHys; auto. destruct (index_of x ys); auto.
          inversion e.
    Qed.
  End IndexOf.

  Fixpoint translate_ETerm (m : list string) (t : ETerm) : Term :=
    match t with
    | EVar x =>
        match index_of x m with
        | None => Free x
        | Some n => Bound n
        end
    | EFun f l => Fun f (map (translate_ETerm m) l)
    end.

  Section ClosedIn.
    Context {Container : Type} (mem : string -> Container -> Prop).

    Fixpoint closed_in (m : Container) (t : ETerm) : Prop :=
      let fix closed_in_list (l : list ETerm) : Prop :=
        match l with
        | [] => True
        | u :: us => closed_in m u /\ closed_in_list us
        end in
      match t with
      | EVar x => mem x m
      | EFun f l => closed_in_list l
      end.
  End ClosedIn.

  Definition mem_list (x : string) (l : list string) :=
    index_of x l = None.

  Lemma closed_in_nil :
    forall (t : ETerm), closed_in mem_list [] t.
  Proof.
    intros t; induction t using eterm_ind; cbn; unfold mem_list; auto.
    induction l as [|u us IHus]; cbn; auto.
    split.
    - now apply Forall_inv in H.
    - apply IHus. now apply Forall_tail in H.
  Qed.

  Lemma closed_in_translate_ETerm :
    forall (t : ETerm) (m m' : list string),
      closed_in mem_list m t ->
      closed_in mem_list m' t ->
      translate_ETerm m t = translate_ETerm m' t.
  Proof.
    intros ??? hclosed hclosed'; induction t using eterm_ind; unfold mem_list; cbn in *.
    - rewrite hclosed hclosed' //.
    - apply f_equal. induction l as [|u us IHus]; cbn; auto.
      rewrite IHus.
      + now apply Forall_tail in H.
      + apply hclosed.
      + apply hclosed'.
      + apply Forall_inv in H. rewrite H //.
        * apply hclosed.
        * apply hclosed'.
  Qed.

  Lemma closed_in_union_closed_in_left :
    forall (t : ETerm) (s s' : SetOfString_.SetOfX_.t),
      closed_in (fun x s => ~set_in x s) (s \union s') t -> closed_in (fun x s => ~set_in x s) s t.
  Proof.
    intros. destruct t using eterm_ind; cbn in *.
    - intro hin. apply H. rewrite union_spec. now left.
    - induction l as [|t ts IHts]; cbn; auto. split.
      + apply Forall_inv in H0. apply H0. apply H.
      + apply IHts.
        * now apply Forall_tail in H0.
        * apply H.
  Qed.

  Lemma closed_in_union_closed_in_right :
    forall (t : ETerm) (s s' : SetOfString_.SetOfX_.t),
      closed_in (fun x s => ~set_in x s) (s \union s') t -> closed_in (fun x s => ~set_in x s) s' t.
  Proof.
    intros. destruct t using eterm_ind; cbn in *.
    - intro hin. apply H. rewrite union_spec. now right.
    - induction l as [|t ts IHts]; cbn; auto. split.
      + apply Forall_inv in H0. apply H0. apply H.
      + apply IHts.
        * now apply Forall_tail in H0.
        * apply H.
  Qed.

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

  (** Warning: this function is not correct _in general_. Indeed, if [u] has free variables
      in the bound variables of [F], the formula will be changed.

      When using this function, one should probably presuppose that no free variable of [u]
      can be bound by [F]. *)
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

  Lemma instantiate_shadowed_term :
    forall (t u : ETerm) (x : string) (rho rho' : list string),
      (translate_ETerm (rho ++ x :: rho' ++ [x]) t)
        {#| rho | + #| rho' | + 1 \to translate_ETerm rho' u} =
        translate_ETerm (rho ++ x :: rho') t.
  Proof.
    intros. induction t using eterm_ind; try reflexivity; cbn.
    - destruct (index_of x0 (rho ++ x :: rho' ++ [x])) eqn:e0;
        destruct (index_of x0 (rho ++ x :: rho')) eqn:e1; cbn.
      + have hin := index_of_In' _ _ _ e1.
        have e : n = n0.
        { replace rho' with (List.app rho' []) in e1.
          have h := index_of_prefix x0 (rho ++ x :: rho') [x] [].
          eapply h; eauto.
          1-2: rewrite -!app_assoc in e0 e1 |- *; eauto.
          apply app_nil_r. }
        have hlt : n < #|rho ++ x :: rho'|.
        { apply (index_of_length x0); rewrite e //. }
        rewrite -match_eq_dec_eq_bool.
        destruct ((#|rho| + #|rho'| + 1) == n); auto.
        exfalso. have h : n < #| rho | + #| rho' | + 1.
        { rewrite length_app in hlt. cbn in hlt. lia. }
        lia.
      + destruct (x == x0).
        * subst. have h : (rho ++ x0 :: rho').(#|rho|) = Some x0.
          { rewrite nth_error_app2; auto.
            rewrite PeanoNat.Nat.sub_diag. now cbn. }
          apply nth_error_In in h. apply index_of_None in e1. exfalso. now apply e1.
        * apply index_of_In' in e0.
          apply index_of_None in e1.
          have h : List.In x0 [x].
          { replace (rho ++ x :: rho' ++ [x])%list with ((rho ++ x :: rho') ++ [x])%list in e0.
            2: { rewrite -!app_assoc app_comm_cons //. }
             apply in_app_or in e0. destruct e0; auto. exfalso. now apply n0. }
          cbn in h. destruct h; auto.
          -- exfalso; now apply n0.
          -- inversion H.
      + apply index_of_In' in e1.
        apply index_of_None in e0.
        exfalso. apply e0. rewrite app_comm_cons app_assoc. apply in_or_app. now left.
      + reflexivity.
    - apply f_equal. rewrite map_map.
      induction l as [|v vs IHvs]; auto.
      cbn. rewrite IHvs.
      + now apply Forall_tail in H.
      + apply Forall_inv in H. rewrite H //.
  Qed.

  Lemma instantiate_shadowed_form :
    forall (F : EForm) (t : ETerm) (x : string) (rho rho' : list string),
      (translate_EForm_ (rho ++ x :: rho' ++ [x]) F)
        {#| rho | + #| rho' | + 1 \to translate_ETerm rho' t} =
        translate_EForm_ (rho ++ x :: rho') F.
  Proof.
    intros F t. induction F; try reflexivity.
    - intros. cbn. apply f_equal. induction l; auto.
      cbn; rewrite IHl. rewrite instantiate_shadowed_term //.
    - intros; cbn. rewrite IHF //.
    - intros; cbn. rewrite IHF1 IHF2 //.
    - intros; cbn. rewrite IHF1 IHF2 //.
    - intros; cbn. rewrite IHF1 IHF2 //.
    - intros; cbn. rewrite IHF1 IHF2 //.
    - intros; cbn. do 3 apply f_equal.
      have h := (IHF x (s :: rho) rho').
      cbn in h. rewrite -h. f_equal. lia.
    - intros; cbn. apply f_equal.
      have h := (IHF x (s :: rho) rho').
      cbn in h. rewrite -h. f_equal. lia.
  Qed.

  Lemma instantiate_eterm_commutes_instantiate_term :
    forall (x : string) (t u : ETerm) (rho : list string),
      ~(List.In x rho) ->
      (translate_ETerm (rho ++ [x]) t) {#|rho| \to translate_ETerm rho u} =
        translate_ETerm rho (instantiate_eterm x u t).
  Proof.
    intros ?????. induction t using eterm_ind; cbn.
    - rewrite -match_eq_dec_eq_bool.
      destruct (x0 == x); cbn.
      + destruct (x == x0); try congruence.
        destruct (index_of x0 (rho ++ [x])) eqn:eindex; cbn; subst.
        * have e : #|rho| = n.
          { have eindex' := index_of_rapp x rho H.
            specialize (eindex' ltac:(typeclasses eauto)).
            rewrite eindex in eindex'. injection eindex' => -> //. }
          rewrite -match_eq_dec_eq_bool. destruct (#|rho| == n); congruence.
        * have hin : In x (rho ++ [x]).
          { clear; induction rho; cbn.
            - now right.
            - now left. }
          apply In_index_of in hin. destruct hin as (k & contra). congruence.
      + destruct (x == x0); try congruence.
        destruct (index_of x0 (rho ++ [x])) eqn:eindex; cbn; subst.
        * have hlt := index_of_rapp' x x0 rho n1 H n0 eindex.
          have hneq : n1 <> #|rho|. { lia. }
          rewrite -match_eq_dec_eq_bool. destruct (#|rho| == n1); try congruence.
          destruct (index_of x0 rho) eqn:index'; cbn in *.
          -- rewrite index_of_rapp'' in eindex; auto.
             rewrite index' in eindex. injection eindex => -> //.
          -- rewrite index_of_rapp'' in eindex; auto.
             rewrite index' in eindex. inversion eindex.
        * destruct (index_of x0 rho) eqn:eindex'; cbn in *; auto.
          rewrite index_of_rapp'' in eindex; auto.
          rewrite eindex in eindex'. inversion eindex'.
    - apply f_equal. induction l as [|v vs IHvs]; cbn; auto.
      rewrite IHvs.
      + now apply Forall_tail in H0.
      + apply Forall_inv in H0. rewrite H0 //.
  Qed.

  Lemma instantiate_eform_commutes_instantiate_form :
    forall (x : string) (t : ETerm) (F : EForm) (rho : list string),
      ~(List.In x rho) -> closed_in mem_list rho t ->
      closed_in (fun x s => ~ set_in x s) (bv_eform F) t ->
      (translate_EForm_ (rho ++ [x]) F) {#|rho| \to translate_ETerm rho t} =
        translate_EForm_ rho (instantiate_eform x t F).
  Proof.
    intros ???. induction F; intros rho hin hclosed hclosed'; cbn in *; try reflexivity.
    - intros. rewrite !map_map.
      apply f_equal. induction l as [|u us IHus]; cbn; auto.
      rewrite IHus instantiate_eterm_commutes_instantiate_term //.
    - rewrite IHF //.
    - rewrite IHF1 //.
      + eapply closed_in_union_closed_in_left; eauto.
      + rewrite IHF2 //. eapply closed_in_union_closed_in_right; eauto.
    - rewrite IHF1 //.
      + eapply closed_in_union_closed_in_left; eauto.
      + rewrite IHF2 //. eapply closed_in_union_closed_in_right; eauto.
    - rewrite IHF1 //.
      + eapply closed_in_union_closed_in_left; eauto.
      + rewrite IHF2 //. eapply closed_in_union_closed_in_right; eauto.
    - rewrite IHF1 //.
      + eapply closed_in_union_closed_in_left; eauto.
      + rewrite IHF2 //. eapply closed_in_union_closed_in_right; eauto.
    - specialize (IHF (s :: rho)). do 3 apply f_equal.
      have h : closed_in mem_list (s :: rho) t. {
        clear hin IHF. induction t using eterm_ind'; cbn in *.
        - unfold mem_list in *; cbn.
          rewrite -match_eq_dec_eq_bool. destruct (x0 == s).
          + exfalso. apply hclosed'. rewrite union_spec. left.
            subst. rewrite singleton_spec //.
          + rewrite hclosed. now cbn.
        - induction l as [|t ts IHts]; cbn in *; auto. split.
          + apply H.
            * now right.
            * apply hclosed.
            * apply hclosed'.
          + apply IHts.
            * intros. apply H; auto.
            * apply hclosed.
            * apply hclosed'. }
      have e : translate_ETerm rho t = translate_ETerm (s :: rho) t.
      { apply closed_in_translate_ETerm; auto. }
      rewrite -!match_eq_dec_eq_bool.
      destruct (x == s).
      + rewrite e0.
        have h0 := instantiate_shadowed_form F t s [] rho.
        rewrite !app_nil_l in h0. rewrite h0 //.
       + cbn in IHF. rewrite e PeanoNat.Nat.add_1_r IHF; auto.
        intros [e' | hin']; try congruence.
        eapply closed_in_union_closed_in_right; eauto.
    - specialize (IHF (s :: rho)). apply f_equal; cbn.
      have h : closed_in mem_list (s :: rho) t. {
        clear hin IHF. induction t using eterm_ind'; cbn in *.
        - unfold mem_list in *; cbn.
          rewrite -match_eq_dec_eq_bool. destruct (x0 == s).
          + exfalso. apply hclosed'. rewrite union_spec. left.
            subst. rewrite singleton_spec //.
          + rewrite hclosed. now cbn.
        - induction l as [|t ts IHts]; cbn in *; auto. split.
          + apply H.
            * now right.
            * apply hclosed.
            * apply hclosed'.
          + apply IHts.
            * intros. apply H; auto.
            * apply hclosed.
            * apply hclosed'. }
      have e : translate_ETerm rho t = translate_ETerm (s :: rho) t.
      { apply closed_in_translate_ETerm; auto. }
      rewrite -!match_eq_dec_eq_bool.
      destruct (x == s).
      + rewrite e0.
        have h0 := instantiate_shadowed_form F t s [] rho.
        rewrite !app_nil_l in h0. rewrite h0 //.
      + cbn in IHF. rewrite e PeanoNat.Nat.add_1_r IHF; auto.
        intros [e' | hin']; try congruence.
        eapply closed_in_union_closed_in_right; eauto.
  Qed.
End ESyntaxTranslation.

Class ETranslation (A B : Type) :=
  translate : A -> B.

#[global] Instance translate_list {A B : Type} `{ETranslation A B} :
  ETranslation (list A) (list B) := map translate.

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
      interpret_term M rho sigma (translate_ETerm bvs t) =
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
        have e : map (interpret_term M rho sigma) (map (translate_ETerm bvs) l) =
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

  Lemma ls_to_eform_ls_to_form :
    forall (Gamma : list EForm) (M : Model string string) (rho : list M) (sigma : env M string),
      ([[ M # rho # sigma |- [[ls_to_eform Gamma]]]]) <->
        (interpret_form_ M rho sigma (ls_to_form [[Gamma]])).
  Proof.
    intros. induction Gamma as [|F Fs IHFs]; cbn.
    - reflexivity.
    - split; intros h h'; apply h; destruct h'.
      + now left.
      + right. now rewrite IHFs.
      + now left.
      + right. now rewrite -IHFs.
  Qed.

  Lemma is_valid_translation_is_valid :
    forall (Gamma : list EForm) (F : EForm),
      @translate _ (list Form) _ Gamma \models [[ F ]]  <->
        is_evalid (EImp (ls_to_eform Gamma) F).
  Proof.
    intros Gamma F; split; intros H M; specialize (H M).
    - rewrite -translation_equivalidity. cbn in *.
      destruct H as [hGamma | hF]; auto.
      left. rewrite ls_to_eform_ls_to_form //.
    - rewrite -translation_equivalidity in H. cbn in *.
      destruct H as [hGamma | hF]; auto.
      left. rewrite -ls_to_eform_ls_to_form //.
  Qed.

  Fixpoint ls_to_econtext (Gamma : list EForm) : Con :=
    match Gamma with
    | [] => {{ }}
    | F :: Fs => ls_to_econtext Fs ,, [[ F ]]
    end.


  Theorem hasTableau_is_evalid :
    forall (F : EForm) (sko : Skolemization) (Gamma : list EForm) (sigma : Substitution string Term),
      @isClosed string Con _ (ls_to_econtext Gamma ,, Neg (translate_EForm F)) ->
      hasTableau sko (ls_to_econtext Gamma ,, Neg (translate_EForm F)) sigma ->
      is_evalid (EImp (ls_to_eform Gamma) F).
  Proof.
    intros ????? htab. apply (hasTableau_sound sko sigma (ls_to_econtext Gamma) [[ F ]]) in htab; auto.
    unfold is_valid in htab. intros M.
    specialize (htab M).
    have e : empty_env M string = extended_environment [] [] (empty_env M string).
    { now apply funext=>x. }
    rewrite e -gen_translation_equivalidity. cbn.
    cbn in htab. destruct htab as [hGamma | hF].
    - left. intro h. apply hGamma.
      have e' : (translate_EForm_ [] (ls_to_eform Gamma)) =
                  (ls_to_form (ls_to_econtext Gamma)).
      { clear. induction Gamma as [|G Gs IHGs]; cbn in *; try reflexivity.
        now rewrite -IHGs. }
      rewrite -e' //.
    - right. exact hF.
  Qed.
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
Module ExtendedRules.
  Section HasTableauLemmas.
    Context (sko : Skolemization).

    Let sko_record := sko_record sko.

    Lemma con_nth_in :
      forall (Gamma : Con) (i : nat) (F : Form),
        Gamma.(i) = Some F -> F \in Gamma.
    Proof using Type.
      intros ??? e. unfold in_ctx. revert e. set l := Gamma; clearbody l.
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
      forall (Gamma : Con) (sigma : Substitution string Term) (symbs : sko_record) (i : nat),
        Gamma.(i) = Some [[ EBot ]] -> hasTableau_ sko Gamma symbs sigma.
    Proof using Type.
      intros ???? e. apply hasTableauBot.
      eapply con_nth_in; eauto.
    Qed.

    Lemma hasTableauNegTop :
      forall (Gamma : Con) (sigma : Substitution string Term) (symbs : sko_record) (i : nat),
        Gamma.(i) = Some [[ ENeg ETop ]] -> hasTableau_ sko Gamma symbs sigma.
    Proof using Type.
      intros ???? e. eapply hasTableauNegNeg.
      - cbn in e. eapply con_nth_in; eauto.
      - unshelve eapply hasTableauBot; cbn. exact 0. now cbn.
    Qed.

    Lemma hasTableauContr :
      forall (Gamma : Con) (sigma : Substitution string Term) (symbs : sko_record)
        (i j : nat) (F G : EForm),
        Gamma.(i) = Some [[ F ]] -> Gamma.(j) = Some [[ G ]] ->
        (etranslation_eform (ENeg F))@[sigma] = (etranslation_eform G)@[sigma] ->
        hasTableau_ sko Gamma symbs sigma.
    Proof using Type.
      intros ??????? e0 e1 e.
      eapply hasTableauContr; cbn in *.
      - eapply con_nth_in. exact e0.
      - eapply con_nth_in. exact e1.
      - auto.
    Qed.

    Lemma hasTableauNegNeg :
      forall (Gamma : Con) (sigma : Substitution string Term) (symbs : sko_record)
        (i : nat) (F : EForm),
        Gamma.(i) = Some [[ ENeg (ENeg F) ]] ->
        hasTableau_ sko (Gamma ,, [[ F ]]) symbs sigma ->
        hasTableau_ sko Gamma symbs sigma.
    Proof using Type.
      intros ????? e htab. eapply hasTableauNegNeg; eauto.
      cbn in e; eapply con_nth_in; eauto.
    Qed.

    Lemma hasTableauAnd :
      forall (Gamma : Con) (sigma : Substitution string Term) (symbs : sko_record) (i : nat) (F G : EForm),
        Gamma.(i) = Some [[ EAnd F G ]] ->
        hasTableau_ sko (Gamma ,, Neg (Neg [[ F ]]) ,, Neg (Neg [[ G ]]) ,, [[ F ]] ,, [[ G ]]) symbs sigma ->
        hasTableau_ sko Gamma symbs sigma.
    Proof using Type.
      intros ?????? e htab. eapply hasTableauNegOr.
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
      forall (Gamma : Con) (sigma : Substitution string Term) (symbs : sko_record) (i : nat) (F G : EForm),
        Gamma.(i) = Some [[ ENeg (EOr F G) ]] ->
        hasTableau_ sko (Gamma ,, [[ ENeg F ]] ,, [[ ENeg G ]]) symbs sigma ->
        hasTableau_ sko Gamma symbs sigma.
    Proof using Type.
      intros ?????? e htab. eapply hasTableauNegOr.
      - cbn in e; eapply con_nth_in; eauto.
      - assumption.
    Qed.

    Lemma hasTableauNegImp :
      forall (Gamma : Con) (sigma : Substitution string Term) (symbs : sko_record)
        (i : nat) (F G : EForm),
        Gamma.(i) = Some [[ ENeg (EImp F G) ]] ->
        hasTableau_ sko (Gamma ,, [[ ENeg (ENeg F) ]] ,, [[ ENeg G ]] ,, [[ F ]]) symbs sigma ->
        hasTableau_ sko Gamma symbs sigma.
    Proof using Type.
      intros ?????? e htab. eapply hasTableauNegOr.
      - cbn in *; change (Neg [[ F ]]) with ([[ ENeg F ]]) in e; eauto.
      - unshelve eapply hasTableauNegNeg.
        + exact 1.
        + exact F.
        + now cbn.
        + assumption.
    Qed.

    Lemma hasTableauOr :
      forall (Gamma : Con) (sigma : Substitution string Term) (symbs : sko_record) (i : nat) (F G : EForm),
        Gamma.(i) = Some [[ EOr F G ]] ->
        hasTableau_ sko (Gamma ,, [[ F ]]) symbs sigma ->
        hasTableau_ sko (Gamma ,, [[ G ]]) symbs sigma ->
        hasTableau_ sko Gamma symbs sigma.
    Proof using Type.
      intros ?????? e htab1 htab2. eapply hasTableauOr.
      - eapply con_nth_in; eauto.
      - assumption.
      - assumption.
    Qed.

    Lemma hasTableauImp :
      forall (Gamma : Con) (sigma : Substitution string Term) (symbs : sko_record) (i : nat) (F G : EForm),
        Gamma.(i) = Some [[ EImp F G ]] ->
        hasTableau_ sko (Gamma ,, [[ ENeg F ]]) symbs sigma ->
        hasTableau_ sko (Gamma ,, [[ G ]]) symbs sigma ->
        hasTableau_ sko Gamma symbs sigma.
    Proof using Type.
      intros ?????? e htab1 htab2.
      eapply hasTableauOr.
      1: cbn in *; change (Neg [[ F ]]) with ([[ ENeg F ]]) in e; eassumption.
      all: eauto.
    Qed.

    Lemma hasTableauNegAnd :
      forall (Gamma : Con) (sigma : Substitution string Term) (symbs : sko_record) (i : nat) (F G : EForm),
        Gamma.(i) = Some [[ ENeg (EAnd F G) ]] ->
        hasTableau_ sko (Gamma ,, (Or [[ ENeg F ]] [[ ENeg G ]]) ,, [[ ENeg F ]]) symbs sigma ->
        hasTableau_ sko (Gamma ,, (Or [[ ENeg F ]] [[ ENeg G ]]) ,, [[ ENeg G ]]) symbs sigma ->
        hasTableau_ sko Gamma symbs sigma.
    Proof using Type.
      intros ?????? e htab1 htab2. eapply hasTableauNegNeg.
      - cbn in *. change (Or (Neg [[ F ]]) (Neg [[ G ]])) with ([[ EOr (ENeg F) (ENeg G) ]]) in e.
        eassumption.
      - unshelve eapply hasTableauOr.
        1: exact 0.
        1-2: shelve.
        1: reflexivity.
        all: eauto.
    Qed.

    Lemma hasTableauEqu :
      forall (Gamma : Con) (sigma : Substitution string Term) (symbs : sko_record) (i : nat) (F G : EForm),
        Gamma.(i) = Some [[ (EEqu F G) ]] ->
        hasTableau_ sko (Gamma ,, [[ ENeg (ENeg (EImp F G)) ]] ,, [[ ENeg (ENeg (EImp G F)) ]] ,,
                           [[ EImp F G ]] ,, [[ EImp G F ]] ,, [[ ENeg F ]] ,, [[ ENeg G ]])
          symbs sigma ->
        hasTableau_ sko (Gamma ,, [[ ENeg (ENeg (EImp F G)) ]] ,, [[ ENeg (ENeg (EImp G F)) ]] ,,
                           [[ EImp F G ]] ,, [[ EImp G F ]] ,, [[ G ]] ,, [[ F ]]) symbs sigma ->
        hasTableau_ sko Gamma symbs sigma.
    Proof using Type.
      intros ?????? e htab1 htab2. unshelve eapply hasTableauNegOr.
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
            -- unshelve eapply hasTableauOr.
               ++ exact 1.
               ++ exact (ENeg G).
               ++ exact F.
               ++ now cbn.
               ++ auto.
               ++ unshelve eapply hasTableauContr.
                  ** exact 0.
                  ** exact 1.
                  ** exact F.
                  ** exact (ENeg F).
                  ** now cbn.
                  ** now cbn.
                  ** reflexivity.
            -- unshelve eapply hasTableauOr.
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
    Qed.

    Lemma hasTableauNegEqu :
      forall (Gamma : Con) (sigma : Substitution string Term) (symbs : sko_record) (i : nat) (F G : EForm),
        Gamma.(i) = Some [[ ENeg (EEqu F G) ]] ->
        hasTableau_ sko (Gamma ,, [[ EOr (ENeg (EImp F G)) (ENeg (EImp G F)) ]] ,, [[ ENeg (EImp F G) ]]
                           ,, [[ ENeg (ENeg F) ]] ,, [[ ENeg G ]] ,, [[ F ]]) symbs sigma ->
        hasTableau_ sko (Gamma ,, [[ EOr (ENeg (EImp F G)) (ENeg (EImp G F)) ]] ,, [[ ENeg (EImp G F) ]]
                           ,, [[ ENeg (ENeg G) ]] ,, [[ ENeg F ]] ,, [[ G ]]) symbs sigma ->
        hasTableau_ sko Gamma symbs sigma.
    Proof using Type.
      intros ?????? e htab1 htab2. unshelve eapply hasTableauNegNeg.
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
    Qed.

    Lemma hasTableauAll :
      forall (Gamma : Con) (sigma : Substitution string Term) (symbs : sko_record)
        (i : nat) (F : EForm) (x : string) (y : string),
        Gamma.(i) = Some [[ EAll x F ]] ->
        mem y (bv_eform F) = false -> 
        hasTableau_ sko (Gamma ,, [[ instantiate_eform x (EVar y) F ]]) symbs sigma ->
        hasTableau_ sko Gamma symbs sigma.
    Proof using Type.
      intros ??????? e hmem htab. unshelve eapply hasTableauAll.
      1: exact y.
      1: shelve.
      - cbn in e. eapply con_nth_in; eauto.
      - replace [x] with (List.app [] [x]).
        2: now cbn.
        rewrite (instantiate_eform_commutes_instantiate_form x (EVar y) F []); auto.
        + now cbn.
        + cbn. now rewrite mem_spec' in hmem.
    Qed.

    Existing Instance fv_ctx.

    Lemma hasTableauNegAll :
      forall (Gamma : Con) (sigma : Substitution string Term) (symbs : sko_record)
        (i : nat) (F : EForm) (x : string) (t : ETerm)
        (hsko : is_sko (translate_ETerm [] t) (Neg (translate_EForm_ [x] F)) (fv Gamma) symbs = true),
        Gamma.(i) = Some [[ ENeg (EAll x F) ]] ->
        closed_in (fun x s => ~ set_in x s) (bv_eform F) t ->
        hasTableau_ sko (Gamma ,, [[ instantiate_eform x t (ENeg F) ]])
          (add_symbol (symbol sko [[t]] hsko) (translate_EForm_ [x] F) symbs) sigma ->
        hasTableau_ sko Gamma symbs sigma.
    Proof using Type.
      intros ???????? e hclosed htab.
      apply (hasTableauNegAll sko Gamma symbs sigma (translate_EForm_ [x] F) [[ t ]] hsko).
      - cbn in e |- *; eapply con_nth_in; eauto.
      - have e' : (translate_EForm_ [x] (ENeg F)) {0 \to [[t]]} =
                    [[instantiate_eform x t (ENeg F)]].
        { replace [x] with (List.app [] [x]).
          2: now cbn.
          rewrite (instantiate_eform_commutes_instantiate_form x t (ENeg F) []); auto; cbn.
          apply closed_in_nil. }
        rewrite -e' in htab. now cbn in htab.
    Qed.

    Lemma hasTableauEx :
      forall (Gamma : Con) (sigma : Substitution string Term) (symbs : sko_record)
        (i : nat) (F : EForm) (x : string) (t : ETerm)
        (hsko : is_sko (translate_ETerm [] t) (Neg (Neg (translate_EForm_ [x] F))) (fv Gamma) symbs = true),
        Gamma.(i) = Some [[ EEx x F ]] ->
        closed_in (fun x s => ~ set_in x s) (bv_eform F) t ->
        hasTableau_ sko (Gamma ,, [[ ENeg (ENeg (instantiate_eform x t F)) ]] ,,
                           [[ instantiate_eform x t F ]])
          (add_symbol (symbol sko [[t]] hsko) (Neg (translate_EForm_ [x] F)) symbs) sigma ->
        hasTableau_ sko Gamma symbs sigma.
    Proof using Type.
      intros ???????? e hclosed htab. eapply hasTableauNegAll.
      Unshelve.
      4: exact i.
      4: exact (ENeg F).
      1: apply e.
      all: eauto.
      change [[instantiate_eform x t (ENeg (ENeg F))]] with
        [[ENeg (ENeg (instantiate_eform x t F))]].
      unshelve eapply hasTableauNegNeg.
      1: exact 0.
      1: shelve.
      1: reflexivity.
      assumption.
    Qed.

    Lemma hasTableauNegEx :
      forall (Gamma : Con) (sigma : Substitution string Term) (symbs : sko_record)
        (i : nat) (F : EForm) (x : string) (y : string),
        Gamma.(i) = Some [[ ENeg (EEx x F) ]] ->
        mem y (bv_eform (ENeg F)) = false ->
        hasTableau_ sko (Gamma ,, [[EAll x (ENeg F)]] ,, [[ instantiate_eform x (EVar y) (ENeg F) ]])
          symbs sigma -> hasTableau_ sko Gamma symbs sigma.
    Proof using Type.
      intros ??????? e hmem htab. unshelve eapply hasTableauNegNeg.
      - exact i.
      - exact (EAll x (ENeg F)).
      - now cbn in e |- *.
      - unshelve eapply hasTableauAll.
        1: exact 0.
        4: reflexivity.
        1: shelve.
        all: eauto.
    Qed.
  End HasTableauLemmas.
End ExtendedRules.
