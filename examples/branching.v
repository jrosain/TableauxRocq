Set Warnings "-native-compiler".
From Tableaux Require Import All.
Import ExtendedSyntaxNotation.

(** In this file, we give an example of a tableau proof of the following branching
    formula:
      [exists x, P x -> P a /\ P b],
    both in outer and inner Skolemization.

    We start by defining the drinker formula using the extended syntax: *)
Definition branching : EForm :=
  '? "x" :(("P" ''('"x")) '=> ("P" ''("a" '())) '&& ("P" ''("b" '()))).

(** In the proofs (be it in outer or in inner), we create two metavariables by instantiating
    the formula twice, and replace one of them by [a] and the other one by [b].

    Here, we do not create any new skolem symbol. *)
Definition subst := translate_substitution [("X", "a" '()) ; ("X2", "b" '())].

Definition outer_branching_proof : ExtendedRuleTree.
Proof.
  (** We start by creating a new free variable [X]. *)
  apply (mkUnaryNode (GammaNegEx (Neg [[ branching ]]) "X")).

  (** Then, the proof progresses as expected. *)
  apply (mkUnaryNode
           (AlphaNegImp (Neg [[ (("P" ''('"X")) '=> ("P" ''("a" '())) '&& ("P" ''("b" '()))) ]]))).

  (** Now, we have a branching rule with the negation of the conjunction. Therefore, we have
      to apply [mkBinaryNode] instead, and we will have two goals left. *)
  apply (mkBinaryNode (BetaNegAnd (Neg [[ ("P" ''("a" '())) '&& ("P" ''("b" '())) ]]))).

  (** The first branch is the one where the formula _on the left_ is, i.e., here, it will
      be [Neg P(a)]. *)
  { (** Here, we can directly closed the branch, instantiating [X} by [a]. *)
    exact (mkClosure [[ '~ ("P" ''("a" '())) ]] [[ "P" ''('"X") ]]). }

  (** The second branch is the one where the formula _on the right_ is, i.e., here, it will
      be [Neg P(b)]. *)
  { (** In this case, we need to create a new free variable [X2]. *)
    apply (mkUnaryNode (GammaNegEx (Neg [[ branching ]]) "X2")).

    (** Then, we continue by applying the same previous step, where we replace [X] by [X2]. *)
    apply (mkUnaryNode
           (AlphaNegImp (Neg [[ (("P" ''('"X2")) '=> ("P" ''("a" '())) '&& ("P" ''("b" '()))) ]]))).

    (** Finally, we claim that this is enough to close the tableau. *)
    exact (mkClosure [[ '~ ("P" ''("b" '())) ]] [[ "P" ''('"X2") ]]). }
Defined.

(** Let's see if this is indeed a proof. *)
Theorem hasTableau_outer_branching_proof :
  hasTableau OuterSkolemization [Neg (translate_EForm branching)] subst.
Proof. tableaux outer_branching_proof. Qed.
(** Yay!! *)

(* Theorem hasTableau_inner_branching_proof : *)
(*   hasTableau InnerSkolemization [Neg (translate_EForm branching)] subst. *)
(* Proof. tableaux outer_branching_proof. Qed. *)
