(** * Skolemization: a generic class for Skolemization *)

From Tableaux Require Import Prelude.All.
From Tableaux Require Import Syntax.
From Tableaux Require Import Semantics.

(** In this file, we implement first-order Skolemization in the framework of Cantone
    and Nicolosi-Asmundo (in their paper _A Sound Framework for δ-Rule Variants
    in Free-Variable Semantic Tableaux_). The goal is to be able to be
    Skolemization-independent in the definition of tableaux and make it work seamlessly
    for different instances of this class. *)
Section SkolemizationDef.
  Context {pred func var : Atom} `{set_nat : set nat}.

  Let set_var := set_atom var.
  Let set_func := set_atom func.

  Section SkoRecord.
    (** A [SkoRecord_] is, morally, a key-value map, with keys being function symbols
        and values first-order formulas. *)
    Record SkoRecordData :=
      { record :> Type
      ; record_eqb :: EqBool record

      ; value_record : func -> record -> option (Form_ pred func var)
      ; join : record -> record -> record
      ; diff_record : record -> record -> record
      ; single_record : func -> Form_ pred func var -> record
      ; empty_record : record }.
    #[global] Arguments value_record {_} _ _.
    #[global] Arguments diff_record {_} _ _.
    #[global] Arguments join {_} _ _.
    #[global] Arguments empty_record {_}.

    Section SkoRecordDataDefs.
      Context {RecordData : SkoRecordData}.

      Definition in_record (f : func) (r : RecordData) : Prop :=
        match value_record f r with
        | None => False
        | Some _ => True
        end.

      Definition mem_record (f : func) (r : RecordData) : bool :=
        match value_record f r with
        | None => false
        | Some _ => true
        end.

      Lemma mem_record_spec :
        forall (f : func) (r : RecordData),
          mem_record f r = true <-> in_record f r.
      Proof using Type.
        intros. rewrite /mem_record /in_record.
        destruct (value_record f r).
        - tauto.
        - easy.
      Qed.
    End SkoRecordDataDefs.

    Class SkoRecordSpecs (RecordData : SkoRecordData) :=
      { record_ext :
        forall (r1 r2 : RecordData),
          r1 = r2 <->
            (forall (f : func), in_record f r1 <-> in_record f r2)
      ; single_spec :
        forall (f g : func) (F : Form_ pred func var),
          in_record g (single_record RecordData f F) <-> g = f
      ; join_spec :
        forall (f : func) (r1 r2 : RecordData),
          in_record f (join r1 r2) <-> in_record f r1 \/ in_record f r2
      ; diff_record_spec  :
        forall (f : func) (r1 r2 : RecordData),
          in_record f (diff_record r1 r2) <->
            in_record f r1 /\ ~ in_record f r2
      ; value_record_spec1 :
        forall (f : func), @value_record RecordData f empty_record = None
      }.

    Record SkoRecord_ :=
      { data :> SkoRecordData
      ; specs :: SkoRecordSpecs data }.
  End SkoRecord.

  Record SkolemizationData :=
    { sko_record : SkoRecord_
    ; is_sko :> Term_ func var -> Form_ pred func var -> set_var -> sko_record -> bool
    ; symbol :
        forall (t : Term_ func var) (F : Form_ pred func var) (S : set_var) (Sf : sko_record),
          is_sko t F S Sf = true -> func
    ; args :
      forall (t : Term_ func var) (F : Form_ pred func var) (S : set_var) (Sf : sko_record),
        is_sko t F S Sf = true -> list (Term_ func var) }.

  Class isSkolemization (data : SkolemizationData) :=
    { is_func :
      forall {t : Term_ func var} {F : Form_ pred func var} {S : set_var} {Sf : sko_record data}
        (Hsko : is_sko data t F S Sf = true),
        t = Fun (symbol data t F S Sf Hsko) (args data t F S Sf Hsko)
    ; locally_closed :
      forall {t : Term_ func var} {F : Form_ pred func var} {S : set_var} {Sf : sko_record data}
        (Hsko : is_sko data t F S Sf = true), isLocallyClosed t }.

  Record Skolemization_ :=
    { skoData :> SkolemizationData
    ; is_skolemization :: isSkolemization skoData }.
End SkolemizationDef.

Coercion specs : SkoRecord_ >-> SkoRecordSpecs.
Coercion is_skolemization : Skolemization_ >-> isSkolemization.

Arguments SkoRecordData : clear implicits.
Arguments SkoRecord_ : clear implicits.

Arguments SkolemizationData : clear implicits.
Arguments Skolemization_ _ _ _ {_}.
Arguments sko_record {_ _ _} _.
Arguments is_sko {_ _ _ _} _ _ _ _.
Arguments symbol {_ _ _} _ _ {_ _ _} _.
Arguments args {_ _ _} _ _ {_ _ _} _.

Section SkoSymbolLemmas.
  Context {pred func var : Atom} {record : SkoRecord_ pred func var}.

  Existing Instance eqb_atom.

  Definition add_symbol (f : func) (F : Form_ pred func var) (r : record) : record :=
    join (single_record record f F) r.

  Definition rem_symbol (f : func) (F : Form_ pred func var) (r : record) : record :=
    diff_record r (single_record record f F).

  Lemma add_symbol_spec1 :
    forall (f : func) (F : Form_ pred func var) (r : record),
      in_record f (add_symbol f F r).
  Proof using Type.
    intros. unfold add_symbol.
    rewrite join_spec. left.
    now rewrite single_spec.
  Qed.

  Lemma add_symbol_spec2 :
    forall (f g : func) (G : Form_ pred func var) (r : record),
      in_record f r -> in_record f (add_symbol g G r).
  Proof using Type.
    intros ???? hin; unfold add_symbol.
    rewrite join_spec. now right.
  Qed.

  Lemma add_symbol_inv :
    forall (f g : func) (G : Form_ pred func var) (r : record),
      in_record f (add_symbol g G r) -> f = g \/ in_record f r.
  Proof using Type.
    intros ???? hin. rewrite /add_symbol join_spec in hin. destruct hin as [hin | hin].
    - rewrite single_spec in hin. now left.
    - now right.
  Qed.

  Lemma rem_symbol_spec1 :
    forall (f : func) (F : Form_ pred func var) (r : record),
      ~ in_record f (rem_symbol f F r).
  Proof using Type.
    intros ??? hin; unfold rem_symbol in hin.
    rewrite diff_record_spec in hin. destruct hin as (_ & h). apply h.
    now rewrite single_spec.
  Qed.

  Lemma rem_symbol_spec2 :
    forall (f g : func) (G : Form_ pred func var) (r : record),
      in_record f (rem_symbol g G r) -> in_record f r.
  Proof using Type.
    intros ???? h. unfold rem_symbol in h.
    rewrite diff_record_spec in h. now destruct h as [hin _].
  Qed.

  Lemma rem_symbol_spec3 :
    forall (f g : func) (G : Form_ pred func var) (r : record),
      f <> g -> in_record f r -> in_record f (rem_symbol g G r).
  Proof using Type.
    intros ???? n e. unfold rem. rewrite diff_record_spec.
    split; auto. intro contra. apply n.
    now rewrite single_spec in contra.
  Qed.

  Lemma add_rem_symbol :
    forall (f : func) (F : Form_ pred func var) (r : record),
      in_record f r -> add_symbol f F (rem_symbol f F r) = r.
  Proof using Type.
    intros ??? hin. rewrite record_ext; intros g; split; intro h.
    - apply add_symbol_inv in h. destruct h as [ e | h ]; subst; auto.
      eapply rem_symbol_spec2; eauto.
    - unfold add_symbol. rewrite join_spec.
      destruct (f == g) as [e | n].
      + left. rewrite e. now rewrite single_spec.
      + right. eapply rem_symbol_spec3; eauto.
  Qed.

  Lemma join_unitr :
    forall (r : record),
      join r empty_record = r.
  Proof using Type.
    intro; rewrite record_ext; intros f; split.
    - rewrite join_spec; intros [h | contra]; auto.
      unfold in_record in contra. now rewrite value_record_spec1 in contra.
    - rewrite join_spec; intros h; auto.
  Qed.

  Lemma join_unitl :
    forall (r : record),
      join empty_record r = r.
  Proof using Type.
    intro; rewrite record_ext; intros f; split.
    - rewrite join_spec; intros [contra | h]; auto.
      unfold in_record in contra. now rewrite value_record_spec1 in contra.
    - rewrite join_spec; intros h; auto.
  Qed.
End SkoSymbolLemmas.

(** ** Some classic instances *)
Section SkolemizationInstances.
  Context {pred func var : Atom} `{set_term : set (Term_ func var)}.

  Let set_var := set_atom var.
  Let set_func := set_atom func.

  Existing Instance set_func.

  (** An instance of [SkoRecord] with sets. *)
  Definition SkoRecordData_sets :
    SkoRecordData pred func var.
  Proof.
    unshelve econstructor.
    - exact set_func.
    - exact set_eqb.
    - exact (fun f s => if mem f s then Some (Neg Bot) else None).
    - exact union.
    - exact diff.
    - exact (fun f _ => singleton f).
    - exact empty_set.
  Defined.

  Lemma SkoRecordData_sets_in :
    forall (f : func) (r : SkoRecordData_sets),
      in_record f r <-> set_in f r.
  Proof using Type.
    intros; split; intro h.
    - rewrite -mem_spec. rewrite -mem_record_spec in h. rewrite -h.
      unfold mem_record, value_record; cbn.
      destruct (mem f r); auto.
    - rewrite -mem_record_spec. rewrite -mem_spec in h. rewrite -h.
      unfold mem_record, value_record; cbn.
      destruct (mem f r); auto.
  Qed.

  #[global] Instance SkoRecordSpecs_sets :
    SkoRecordSpecs SkoRecordData_sets.
  Proof using Type.
    unshelve econstructor.
    - intros. split; intro h.
      + rewrite set_ext in h. intro; now rewrite !SkoRecordData_sets_in.
      + rewrite set_ext. intro; now rewrite -!SkoRecordData_sets_in.
    - intros; cbn. split; intro h.
      + unfold in_record, value_record in h. cbn in h.
        destruct (mem g (singleton f)) eqn:e.
        * rewrite mem_spec in e. now apply singleton_spec in e.
        * inversion h.
      + have H : set_in g (singleton f).
        { now rewrite singleton_spec. }
        now rewrite SkoRecordData_sets_in.
    - intros. rewrite !SkoRecordData_sets_in.
      unfold join. cbn. apply union_spec.
    - intros. rewrite !SkoRecordData_sets_in.
      unfold diff_record. cbn. apply diff_spec.
    - intros; cbn. destruct (mem f \{ \}) eqn:e; auto.
      rewrite mem_spec in e. now apply empty_spec in e.
  Qed.

  Definition sko_record_sets : SkoRecord_ pred func var.
  Proof.
    unshelve econstructor.
    - exact SkoRecordData_sets.
    - typeclasses eauto.
  Defined.

  (* Use this function to avoid repeating the match on useless terms *)
  Definition SkoWrapper_is_sko (t : Term_ func var) (P : func -> list (Term_ func var) -> bool) : bool :=
    match t with
    | Bound _ | Free _ => false
    | Fun f l => P f l
    end.

  (* Use this function to get the skolem symbol (it abstracts away the impossible cases) *)
  Definition SkoWrapper_symbol (t : Term_ func var) {P : func -> list (Term_ func var) -> bool}
    (hsko : SkoWrapper_is_sko t P = true) : func.
    refine
      (match t as t0 return t = t0 -> func with
       | Bound _ | Free _ => fun e => False_rect func _
       | Fun f _ => fun _ => f
       end eq_refl).
    all: now rewrite e in hsko.
  Defined.

  Definition SkoWrapper_args (t : Term_ func var) {P : func -> list (Term_ func var) -> bool}
    (hsko : SkoWrapper_is_sko t P = true) : list (Term_ func var).
  Proof.
    refine
      (match t as t0 return t = t0 -> list (Term_ func var) with
       | Bound _ | Free _ => fun e => False_rect (list (Term_ func var)) _
       | Fun _ l => fun _ => l
       end eq_refl).
    all: now rewrite e in hsko.
  Defined.

  Definition is_fv_in (S : set_atom var) (t : Term_ func var) : bool :=
    match t with
    | Bound _ | Fun _ _ => false
    | Free x => mem x S
    end.

  Definition only_fv_in (S : set_atom var) (t : Term_ func var) : bool :=
    match t with
    | Bound _ | Free _ => false
    | Fun f l => forallb (is_fv_in S) l
    end.

  Definition OuterSkolemizationData : SkolemizationData pred func var.
  Proof.
    unshelve econstructor.
    - exact sko_record_sets. (* in outer skolemization, we only worry about freshness of the
                                symbols *)
    - intros t _ S Sf.
      (* We want to check (i) that all the list [l] is composed of all the free variables of
         the set [S], and (ii) that the symbol [f] is fresh in the set of skolem symbols already
         appearing in the branch *)
      exact (SkoWrapper_is_sko t
               (fun f l => andb (only_fv_in S t) (isFresh f Sf))).
    - intros t ??? hsko. apply (SkoWrapper_symbol t hsko).
    - intros t ??? hsko. apply (SkoWrapper_args t hsko).
  Defined.

  Lemma isSkolemization_OuterSkolemizationData :
    isSkolemization OuterSkolemizationData.
  Proof.
    constructor.
    - intros. destruct t; cbn in *; try (inversion Hsko; fail).
      reflexivity.
    - intros; destruct t; cbn in *; try (inversion Hsko; fail).
      (* other way of isLocallyClosed_Fun_isLocallyClosed_list *)
  Admitted.

  Definition OuterSkolemization : Skolemization_ pred func var.
  Proof.
    unshelve econstructor.
    - exact OuterSkolemizationData.
    - exact isSkolemization_OuterSkolemizationData.
  Defined.

  Definition InnerSkolemizationData : SkolemizationData pred func var.
  Proof.
    unshelve econstructor.
    - exact sko_record_sets. (* in inner skolemization, we also only care about freshness of the
                                symbols *)
    - intros t F _ Sf.
      (* We want to check (i) that the list [l] is composed of all the free variables appearing
         in the Skolemized formula [F], and (ii) that the symbol [f] is fresh in the set of
         Skolem symbols already appearing in the branch. *)
      exact (SkoWrapper_is_sko t (fun f l => andb (only_fv_in (fv F) t) (isFresh f Sf))).
    - intros t ??? hsko. apply (SkoWrapper_symbol t hsko).
    - intros t ??? hsko. apply (SkoWrapper_args t hsko).
  Defined.

  Lemma isSkolemization_InnerSkolemizationData :
    isSkolemization InnerSkolemizationData.
  Proof. Admitted.

  Definition InnerSkolemization : Skolemization_ pred func var.
  Proof.
    unshelve econstructor.
    - exact InnerSkolemizationData.
    - exact isSkolemization_InnerSkolemizationData.
  Defined.
End SkolemizationInstances.

Module ConcreteSkolemizationInstances.
  Export ConcreteSyntaxInstances.

  Definition Skolemization := Skolemization_ string string string.
End ConcreteSkolemizationInstances.
