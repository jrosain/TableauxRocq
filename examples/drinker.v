From Tableaux Require Import All.

(** In this file, we give an example of a tableau proof of the drinker principle:
      [exists x, P x -> forall y, P y],
    both in outer and inner Skolemization.

    We start by defining the drinker formula using the extended syntax: *)
Definition drinker0 : EForm :=
  EEx "x" (EImp (EPred "P" [EVar "x"]) (EAll "y" (EPred "P" ([EVar "y"])))).

(** As this is a bit verbose, some notations (that have to be imported) can be used instead: *)
Import ExtendedSyntaxNotation.
Definition drinker : EForm :=
  '? "x" :("P" ''('"x") '=> '! "y" :("P" ''('"y"))).

(** These two really define the same formula: *)
Goal drinker0 = drinker. reflexivity. Qed.

(** The extended notation, defined in the module [ExtendedSyntaxNotation], uses a "quoting"
    system, i.e., it uses quotes for connectors, variables & arguments of functions and
    predicates. The correspondance is as follows:
    - ['!] for [EAll] and ['?] for [EEx], that must be followed by a variable and the token
      [:(], which should then contain a formula [F] followed by the closing of a parenthesis,
    - ['||], ['&&], ['=>] and ['<=>] for, respectively, [EOr], [EAnd], [EImp] and [EEqu],
    - ['~] for [ENeg],
    - [P ''(t1 ,, .. ,, tn)] for a predicate,
    - [f '(t1 ,, .. ,, tn)] for a function,
    - and ['x] for a simple variable. *)

(** In the outer Skolemization proof, we have to instantiate the drinker formula twice by
    [X] then [X2] as the first Skolemization step yields [f X]. We can then instantiate
    [X2] by [f X] to bring the proof to closure.

    In TableauxRocq, we can give this substitution as a finite list and automatically
    translate it to the system's internal substitution type using [translate_substitution]. *)
Definition outer_subst := translate_substitution [("X2", "f" '('"X"))].

(** We can now define the proof tree of this formula. This is done by defining the object
    called [ExtendedRuleTree]. This object records the extension rule applied, as well as
    the formula on which it is applied and, potentially, the term it generates. *)
Definition outer_drinker_proof : ExtendedRuleTree.
Proof.
  (** The first step will be to apply the [GammaNegEx] rule on the [drinker] formula,
      generating the free variable [X].

      This is a unary rule, so in order to build an [ExtendedRuleTree], we can make use
      of [mkUnaryNode]. Note the use of the double brackets, that are needed to translate
      the formula from the extended syntax to the internal one. *)
  apply (mkUnaryNode (GammaNegEx (Neg [[ drinker ]]) "X")).

  (** The second step is to apply the negated implication on the underlying formula.
      Here, as we must specify the formula, there are two options: first, write down
      the formula by hand (as an automated theorem prover would do), or use the utility
      function [get_neg_ex]. This returns an [option Form], but in this case, we know that
      this will always be [Some ...], so we can use [option_get] to ... get the formula.

      Indeed: *)
  Transparent eqb. Eval cbn in (option_get Bot (get_neg_ex (Neg [[ drinker ]]))). Opaque eqb.

  (** Beware that, using this method, the bound variable [0] appears. It needs to be
      replaced by the free variable we just created, i.e., [X]. *)
  apply (mkUnaryNode (AlphaNegImp (option_get Bot (get_neg_ex (Neg [[ drinker ]]))){0 \to Free "X"})).

  (** We can now apply the first Skolemization rule, generating the Skolem symbol [f X]. *)
  apply (mkUnaryNode (DeltaNegAll (Neg [[ '! "y" :("P" ''('"y"))  ]])
                        [[ "f" '('"X") ]])).

  (** Then, we have to apply back the drinker formula, which generates a new metavariable [X2] *)
  apply (mkUnaryNode (GammaNegEx (Neg [[ drinker ]]) "X2")).

  (** We can use the same trick as before to split the formulas, replacing [X] by [X2]. *)
  apply (mkUnaryNode (AlphaNegImp (option_get Bot (get_neg_ex (Neg [[ drinker ]]))){0 \to Free "X2"})).

  (** Now, we claim that there is a contradiction with the substitution [X2 -> f X], so we can
      simply say that the proof finishes here. *)
  exact Leaf.

  (** Very importantly, this proof must be [Defined]. *)
Defined.

(** Now, behold the full power of reflection: *)
Theorem hasTableau_outer_drinker_proof :
  hasTableau OuterSkolemization [Neg (translate_EForm drinker)] outer_subst.
Proof. tableaux outer_drinker_proof. Qed.

(** In inner Skolemization, we only have to Skolemize once as ["X"] does not appear in the
    body of the Skolemized formula. As before, we provide the substitution using a finite list,
    and call the [translate_substitution] function. *)
Definition inner_subst := translate_substitution [("X", EFun "c" [])].

(** Let's do the proof. *)
Definition inner_drinker_proof : ExtendedRuleTree.
Proof.
  (** The proof proceeds as before for the first two steps *)
  apply (mkUnaryNode (GammaNegEx (Neg [[ drinker ]]) "X")).
  apply (mkUnaryNode (AlphaNegImp (option_get Bot (get_neg_ex (Neg [[ drinker ]]))){0 \to Free "X"})).

  (** We can now apply the first Skolemization rule, generating the Skolem symbol [c]. *)
  apply (mkUnaryNode (DeltaNegAll (Neg [[ '! "y" :("P" ''('"y")) ]])
                        [[ "c" '() ]])).

  (** This is enough to have a contradiction. *)
  exact Leaf.
Defined.

Theorem hasTableau_inner_drinker_proof :
  hasTableau InnerSkolemization [Neg (translate_EForm drinker)] inner_subst.
Proof. tableaux inner_drinker_proof. Qed.
