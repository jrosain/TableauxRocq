(** * SyntaxInstance: instantiation of the atoms using strings *)

From Tableaux Require Export Prelude.All.
From Tableaux Require Export Syntax.

From Stdlib Require Import Lia.
From Stdlib Require Import Structures.Orders.

Definition Term := Term string string.
Definition Form := Form string string string.

(** *** Sets of formulas *)

(** We instantiate [MSetsAVL] with formulas to get sets of formulas. *)

(** First, we add a propositional & boolean function to compare terms. *)
Fixpoint lt_term (t u : Term) : Prop :=
  match t, u with
  | Bound n, Bound m => n < m
  | Bound _, _ => True
  | Free x, Free y => SOrd.lt x y
  | Free _, Bound _ => False
  | Free _, _ => True
  | Fun f lf, Fun g lg =>
      SOrd.lt f g \/
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
      match SOrd.compare x y with
      | Lt => true
      | _ => false
      end
  | Free _, Bound _ => false
  | Free _, _ => true
  | Fun f lf, Fun g lg =>
      match SOrd.compare f g with
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
  - have hspec := SOrd.compare_spec a s.
    destruct (SOrd.compare a s) eqn:hcomp.
    + inversion hspec; subst; cbn in *.
      split; intro contra.
      * inversion contra.
      * exfalso. now apply SOrd.lt_strorder in contra.
    + inversion hspec; split; auto.
    + inversion hspec; split; intro contra.
      * inversion contra.
      * exfalso. have hcontr : SOrd.lt s s.
        { etransitivity; eauto. }
        now apply SOrd.lt_strorder in hcontr.
  - have hspec := SOrd.compare_spec f s.
    destruct (SOrd.compare f s) eqn:hcomp.
    + inversion hspec; subst. split; intro h.
      * right; split; auto.
        erewrite <-ltb_list_lt_list; eauto.
        intros. eapply Ind.Forall_In in H; eauto.
      * destruct h.
        -- apply SOrd.lt_strorder in H0; auto.
        -- destruct H0 as [_ hlt].
           erewrite ltb_list_lt_list; eauto.
           intros; eapply Ind.Forall_In in H; eauto.
    + inversion hspec; split; auto.
    + inversion hspec; split.
      * intro contra; inversion contra.
      * intros [ hlt | [e hlt] ].
        -- have hlt' : SOrd.lt s s by etransitivity; eauto.
           now apply SOrd.lt_strorder in hlt'.
        -- subst. rewrite SSet.XOrdProps.ME.compare_refl in hcomp; inversion hcomp.
Qed.

Lemma ltb_term_false :
  forall (t u : Term),
    ltb_term t u = false -> t <> u -> ltb_term u t = true.
Proof.
  intro t; induction t using term_ind; intros ? hnlt ne; destruct u; cbn in *; try easy.
  - have hspec := NOrd.compare_spec n n0.
    destruct (PeanoNat.Nat.compare n n0); inversion hspec; try easy;
      destruct (PeanoNat.Nat.compare n0 n) eqn:hcomp; try easy.
    + exfalso; apply ne; now subst.
    + apply Compare_dec.nat_compare_Gt_gt in hcomp; lia.
    + apply PeanoNat.Nat.compare_eq in hcomp; lia.
    + apply Compare_dec.nat_compare_Gt_gt in hcomp; lia.
  - have hspec := SOrd.compare_spec a s.
    destruct (SOrd.compare a s); inversion hspec; try easy;
      destruct (SOrd.compare s a) eqn:hcomp; try easy.
    + exfalso; apply ne; now subst.
    + rewrite SSet.Raw.MX.compare_gt_iff in hcomp; subst.
      now apply SOrd.lt_strorder in hcomp.
    + apply SSet.Raw.MX.compare_eq in hcomp; subst.
      exfalso; now apply ne.
    + rewrite SSet.Raw.MX.compare_gt_iff in hcomp.
      have contra : SOrd.lt s s by etransitivity; eauto.
      now apply SOrd.lt_strorder in contra.
  - have hspec := SOrd.compare_spec f s.
    destruct (SOrd.compare f s); inversion hspec; try easy;
      destruct (SOrd.compare s f) eqn:hcomp; try easy.
    + subst. have ne' : l <> l0.
      { intro; apply ne; now subst. }
      apply ltb_list_false; auto.
      intros; eapply Forall_In in H; eauto.
    + subst. rewrite SSet.Raw.MX.compare_refl in hcomp. inversion hcomp.
    + apply SSet.Raw.MX.compare_eq in hcomp; subst.
      now apply SOrd.lt_strorder in H0.
    + rewrite SSet.Raw.MX.compare_gt_iff in hcomp.
      have contra : SOrd.lt s s by etransitivity; eauto.
      now apply SOrd.lt_strorder in contra.
Qed.

(** We do the same for formulas. *)
Fixpoint lt_form (F G : Form) : Prop :=
  match F, G with
  | Bot, Bot => False
  | Bot, _ => True
  | _, Bot => False

  | Pred p l, Pred p' l' =>
      SOrd.lt p p' \/
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
      match SOrd.compare p p' with
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
  - have hspec := SOrd.compare_spec p s.
    destruct (SOrd.compare p s); inversion hspec.
    + subst; split.
      * intro hltb. right; split; auto.
        rewrite -ltb_list_lt_list; eauto.
        intros; apply ltb_term_lt_term.
      * intros [ contra | [ _ hlt ] ].
        -- now apply SOrd.lt_strorder in contra.
        -- rewrite ltb_list_lt_list; eauto.
           intros; apply ltb_term_lt_term.
    + split; auto.
    + split.
      * intro contra; inversion contra.
      * intros [ hlt | [ e _ ] ].
        -- have hlt' : SOrd.lt s s by etransitivity; eauto.
           now apply SOrd.lt_strorder in hlt'.
        -- subst; now apply SOrd.lt_strorder in H.
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
  - have hspec := SOrd.compare_spec p s.
    destruct (SOrd.compare p s); inversion hspec; cbn in *.
    + destruct (SOrd.compare s p) eqn:hcomp; try easy.
      * apply ltb_list_false; auto.
        -- intros. apply ltb_term_false; auto.
        -- intro; subst; now apply ne.
      * subst. now rewrite SSet.XOrdProps.ME.compare_refl in hcomp.
    + destruct (SOrd.compare s p) eqn:hcomp; try easy.
    + destruct (SOrd.compare s p) eqn:hcomp; try easy.
      * apply SSet.Raw.MX.compare_eq in hcomp; subst.
        inversion hspec. now apply SOrd.lt_strorder in H0.
      * rewrite SSet.Raw.MX.compare_gt_iff in hcomp.
        have contra : SOrd.lt s s by etransitivity; eauto.
        now apply SOrd.lt_strorder in contra.
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
    + apply SOrd.lt_strorder.
    + intros [ contra | [_ contra ] ].
      * now apply SOrd.lt_strorder in contra.
      * induction l as [|t l' IHl']; auto.
        cbn in contra. destruct contra as [ contra | [ _ contra ] ].
        -- now apply Ind.Forall_inv in H.
        -- apply IHl'; auto. now apply Ind.Forall_tail in H.
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
           ++ clear e0 e1 f s0. generalize dependent l; generalize dependent l1;
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
      * now apply SOrd.lt_strorder in contra.
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
        -- clear e0 e1 p s s0. generalize dependent l; generalize dependent l1;
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
Module FSet := MSetAVL.Make OrderedForm.

