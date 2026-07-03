open Syntax
open SyntaxInstance

let rec pr_form_ (pr_tm : coq_Term -> Prelude.RocqStr.t) f =
  match f with
  | Neg Bot -> "$true"
  | Neg (Or (Neg (Or (Neg f, g)), Neg (Or (Neg g', f')))) when f = f' && g = g' ->
     Printf.sprintf "(%s <=> %s)" (pr_form_ pr_tm f) (pr_form_ pr_tm g)
  | Neg (Or (Neg f, Neg g)) -> Printf.sprintf "(%s & %s)" (pr_form_ pr_tm f) (pr_form_ pr_tm g)
  | Or (Neg f, g) -> Printf.sprintf "(%s => %s)" (pr_form_ pr_tm f) (pr_form_ pr_tm g)
  | Neg (All (Neg f)) -> Printf.sprintf "? (%s)" (pr_form_ pr_tm f)

  | Bot -> "$false"
  | Pred (p, ts) ->
     Printf.sprintf "%s(%s)" (Prelude.RocqStr.to_string p) (String.concat ", " (List.map (fun t -> Prelude.RocqStr.to_string (pr_tm t)) ts))
  | Neg f -> Printf.sprintf "~(%s)" (pr_form_ pr_tm f)
  | Or (f, g) -> Printf.sprintf "(%s | %s)" (pr_form_ pr_tm f) (pr_form_ pr_tm g)
  | All f -> Printf.sprintf "! (%s)" (pr_form_ pr_tm f)

let pr_form pr_tm f = Prelude.RocqStr.from_string (pr_form_ pr_tm f)

let pr_ctx_ (pr_tm : coq_Term -> Prelude.RocqStr.t) l =
  Printf.sprintf "[\n\t%s\n]" @@ String.concat "\n\t" (List.map (pr_form_ pr_tm) l)

let pr_ctx pr_tm l = Prelude.RocqStr.from_string (pr_ctx_ pr_tm l)
