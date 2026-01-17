(** * Skolemization: a generic class for Skolemization *)

From Tableaux Require Import Prelude.All.
From Tableaux Require Import Syntax.

(** In this file, we implement first-order Skolemization in the framework of Cantone
    and Nicolosi-Asmundo (in their paper _A Sound Framework for δ-Rule Variants
    in Free-Variable Semantic Tableaux_). The goal is to be able to be
    Skolemization-independent in the definition of tableaux and make it work seamlessly
    for different instances of this class. *)
Section SkolemizationDef.
  Context {pred func var : Atom}.

  Let set_var := set_atom var.
  Let set_func := set_atom func.

  Class SkoRecord_ :=
    { record :> Type
    ; record_eqb :: EqBool record
    ; join : record -> record -> record
    ; add_symbol : func -> Form_ pred func var -> record -> record
    ; empty_record : record

    ; join_unitr : forall (r : record), join r empty_record = r
    ; join_unitl : forall (r : record), join empty_record r = r }.

  Class Skolemization_ :=
    { sko_record : SkoRecord_
    ; is_sko :> Term_ func var -> Form_ pred func var -> set_var -> sko_record -> bool
    ; symbol :
        forall (t : Term_ func var) (F : Form_ pred func var) (S : set_var) (Sf : sko_record),
          is_sko t F S Sf = true -> func }.
End SkolemizationDef.

Arguments SkoRecord_ : clear implicits.

Arguments Skolemization_ : clear implicits.
Arguments sko_record {_ _ _} _.
Arguments is_sko {_ _ _ _} _ _ _ _.
Arguments symbol {_ _ _} _ _ {_ _ _} _.

(** ** Some classic instances *)
Section SkolemizationInstances.
  Context {pred func var : Atom} `{set_term : set (Term_ func var)}.

  Let set_var := set_atom var.
  Let set_func := set_atom func.

  (** An instance of [SkoRecord] with sets. *)
  Definition sko_record_sets : SkoRecord_ pred func var.
  Proof.
    unshelve econstructor.
    - exact set_func.
    - exact union.
    - exact empty_set.
    - exact set_eqb.
    - intros f _ r. exact (add f r).
    - apply empty_unitr.
    - apply empty_unitl.
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

  Instance OuterSkolemization : Skolemization_ pred func var.
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
  Defined.

  Instance InnerSkolemization : Skolemization_ pred func var.
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
  Defined.
End SkolemizationInstances.

Module ConcreteSkolemizationInstances.
  Export ConcreteSyntaxInstances.

  Definition Skolemization := Skolemization_ string string string.

  Existing Instance OuterSkolemization.
  Existing Instance InnerSkolemization.
End ConcreteSkolemizationInstances.
