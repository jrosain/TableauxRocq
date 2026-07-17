open Prelude
open SyntaxInstance
open ProofInstance
open LocallyNamelessClasses
open ExtendedSyntax

type sko = Outer | Inner

val sko_str : sko -> string

val interp_sko : sko -> SkolemizationInstances.coq_Skolemization

module Inference : sig
  type t
  type rule =
    False | NotTrue | Hyp | NotNot | And | NotOr | NotImplies | Or | Implies |
    NotAnd | Iff | NotIff | Exists | NotAll | Forall | NotEx

  val mk : rule -> string list -> coq_ETerm option -> t
end

type sub
val mk_sub : string -> coq_ETerm -> sub

module Decl : sig
  type t
  type role = Axiom | Conj | NegConj | LocDef | ProofStep

  val mk : string -> role -> coq_EForm -> Inference.t -> t
  val mk_def : string -> role -> coq_EForm -> t
  val mk_hyp : string -> role -> coq_EForm list -> Inference.t -> t
  val mk_sub : (sub list) -> sko -> t
end

exception NoSuchName of string
exception DefCycleFound of string list
exception ProofCycleFound of string list
exception MultipleSubEncountered
exception MalformedProof of string

val interp_decl_list :
  Decl.t list -> (coq_Form list * (RocqStr.t, coq_Term) coq_Substitution * sko * coq_RuleTree)
