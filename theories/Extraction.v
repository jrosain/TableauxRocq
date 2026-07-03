From Tableaux Require Import Core.
From Tableaux Require Import Checker.

Extraction Language OCaml.
Set Extraction Output Directory "../checker/lib/".

(** ** Extraction for constants and basic inductives *)
From Stdlib Require Import ExtrOcamlBasic.
From Stdlib Require Export ExtrOcamlString.
From Stdlib Require Import ExtrOcamlNatInt.

Extract Inlined Constant map => "List.map".
Extract Inlined Constant app => "List.append".
Extract Inlined Constant rev => "List.rev".
Extract Inlined Constant fold_left => "(fun f a l -> List.fold_left f l a)".
Extract Inlined Constant fold_right => "(fun f a l -> List.fold_right f l a)".
Extract Inlined Constant existsb => "List.exists".
Extract Inlined Constant forallb => "List.for_all".
Extract Inlined Constant filter => "List.filter".

Extract Inlined Constant String.append => "List.append".

Extract Inlined Constant fst => "fst".
Extract Inlined Constant snd => "snd".

Extract Inductive bool => bool [ "true" "false" ].
Extract Inlined Constant negb => "Bool.not".

Extraction Blacklist List String.

(** ** Syntax *)
Extract Inlined Constant eq_bool_string => "(=)".
Extract Inlined Constant eq_bool_nat => "(=)".

(** ** Checking *)
Extract Inlined Constant pr_bool => "Bool.to_string".

(** ** Extraction *)
Extract Inlined Constant pr_form => "(Printer.pr_form pr_term)".
Extract Inlined Constant Ctx.pr_ctx => "(Printer.pr_ctx pr_term)".

Separate Extraction
  ExtendedSyntax.translate_EForm
  ProofInstance.RuleTree
  SkolemizationInstances.OuterSkolemization
  SkolemizationInstances.InnerSkolemization
  Checker.CheckProof.
