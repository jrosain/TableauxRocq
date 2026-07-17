open Prelude
open SyntaxInstance
open ProofInstance
open LocallyNamelessClasses
open ExtendedSyntax

type sko = Outer | Inner

let sko_str = function
  | Outer -> "outer"
  | Inner -> "inner"

let interp_sko = function
  | Outer -> SkolemizationInstances.coq_OuterSkolemization
  | Inner -> SkolemizationInstances.coq_InnerSkolemization

module Inference = struct
  type rule =
    False | NotTrue | Hyp | NotNot | And | NotOr | NotImplies | Or | Implies |
    NotAnd | Iff | NotIff | Exists | NotAll | Forall | NotEx

  type t = { rule: rule; children: string list; new_term: coq_ETerm option }

  let mk rule children new_term =
    { rule; children; new_term = new_term }
end

type sub = (string * coq_ETerm)
let mk_sub name tm = (name, tm)

module Decl = struct
  type role = Axiom | Conj | NegConj | LocDef | ProofStep
  type plain = { name: string; role: role; targets: coq_EForm list; inf: Inference.t option }
  type t = Plain of plain | Subst of ((string * coq_ETerm) list * sko)

  let mk name role target inf =
    Plain { name; role; targets = [target]; inf = Some inf }

  let mk_def name role target =
    Plain { name; role; targets = [target]; inf = None }

  let mk_hyp name role targets inf =
    Plain { name; role; targets; inf = Some inf }

  let mk_sub sub sk = Subst (sub, sk)
end

exception NoSuchName of string
let list_assoc name assoc =
  try List.assoc name assoc
  with
  | Not_found -> raise (NoSuchName name)

let rec referenced_names f names =
  match f with
  | ETop | EBot -> []
  | EPred (p, _) ->
     let name = RocqStr.to_string p in
     if List.mem name names then [name]
     else []
  | ENeg f | EEx (_, f) | EAll (_, f) -> referenced_names f names
  | EOr (f, g) | EAnd (f, g) | EImp (f, g) | EEqu (f, g) ->
     List.append (referenced_names f names) (referenced_names g names)

exception CycleFound of string list

let dfs vertices g visited s =
  let rec explore path visited v =
    if List.mem v path then raise (CycleFound path)
    else if List.mem v visited then visited
    else v :: List.fold_left (explore (v :: path)) visited (list_assoc v g) in
  explore [] visited s

let toposort vertices edges =
  List.fold_left (fun visited v -> dfs vertices edges visited v) [] vertices

exception DefCycleFound of string list

(* Topological sort of the definitions.
   There is an edge between two definitions whenever a definition refers to another one.
   This way, a formula can be normalized by replacing the symbols in the order given by
   the topological sort. *)
let sort_normalization defs =
  let open Decl in
  let _ = List.iter (fun d -> assert (List.length d.targets = 1)) defs in
  let vertices = List.map (fun d -> d.name) defs in
  let edges = List.map (fun d -> (d.name, referenced_names (List.hd d.targets) vertices)) defs in
  try
    toposort vertices edges
  with CycleFound path -> raise (DefCycleFound path)

let normalize_form gamma defs f =
  let rec normalize_aux name nf f =
    match f with
    | ETop | EBot -> f
    | EPred (p, _) ->
       if RocqStr.to_string p = name
       then nf
       else f
    | ENeg f -> ENeg (normalize_aux name nf f)
    | EOr (f, g) -> EOr (normalize_aux name nf f, normalize_aux name nf g)
    | EAnd (f, g) -> EAnd (normalize_aux name nf f, normalize_aux name nf g)
    | EImp (f, g) -> EImp (normalize_aux name nf f, normalize_aux name nf g)
    | EEqu (f, g) -> EEqu (normalize_aux name nf f, normalize_aux name nf g)
    | EAll (x, f) -> EAll (x,normalize_aux name nf f)
    | EEx (x, f) -> EEx (x,normalize_aux name nf f) in
  let get_nf name = List.hd ((List.hd (List.filter (fun d -> d.Decl.name = name) defs)).targets) in
  List.fold_left (fun f name -> normalize_aux name (get_nf name) f) f gamma

exception MultipleSubEncountered

let rec mk_substitution = function
  | None | Some [] -> fun x -> Syntax.Free x
  | Some ((x, t) :: xs) ->
     let sigma = mk_substitution (Some xs) in
     fun y -> if x = RocqStr.to_string y then translate_ETerm [] t else sigma y

let interp_form_list gamma defs fs =
  let open Decl in
  let rec interp_roles = function
    | [] -> []
    | x :: xs ->
       assert (List.length x.targets = 1);
       assert (x.inf = None);
       (match x.role with
       | Axiom | NegConj -> List.hd x.targets
       | Conj -> ENeg (List.hd x.targets)
       | _ -> assert false) :: interp_roles xs in
  let fs = interp_roles fs in
  let fs = List.map (normalize_form gamma defs) fs in
  List.map translate_EForm fs

type eRule =
| ERNotNot of coq_EForm
| ERAnd of coq_EForm
| ERNotOr of coq_EForm
| ERNotImplies of coq_EForm
| EROr of coq_EForm
| ERImplies of coq_EForm
| ERNotAnd of coq_EForm
| ERIff of coq_EForm
| ERNotIff of coq_EForm
| ERNotEx of coq_EForm * coq_ETerm
| ERAll of coq_EForm * coq_ETerm
| ERNotAll of coq_EForm * coq_ETerm
| EREx of coq_EForm * coq_ETerm

type eRuleTree =
  | LeafNotTop | LeafBot
  | LeafHyp of (coq_EForm * coq_EForm)
  | Node of eRuleTree * eRule * eRuleTree

let rec mk_etree gamma defs assoc step =
  let open Decl in
  let inf = Option.get step.inf in
  let on_unary r =
    assert (List.length step.targets = 1);
    assert (List.length inf.children = 1);
    let child = List.hd inf.children in
    Node (mk_etree gamma defs assoc (list_assoc child assoc), r (List.hd step.targets), LeafBot) in
  let on_binary r =
    assert (List.length step.targets = 1);
    assert (List.length inf.children = 2);
    let child1 = List.hd inf.children in
    let child2 = List.nth inf.children 1 in
    Node (mk_etree gamma defs assoc (list_assoc child1 assoc),
          r (List.hd step.targets), mk_etree gamma defs assoc (list_assoc child2 assoc)) in
  let on_quant r =
    assert (List.length step.targets = 1);
    assert (List.length inf.children = 1);
    assert (inf.new_term <> None);
    let child = List.hd inf.children in
    let tm = Option.get inf.new_term in
    Node (mk_etree gamma defs assoc (list_assoc child assoc), r (List.hd step.targets) tm, LeafBot) in
  match inf.rule with
  | False -> LeafBot
  | NotTrue -> LeafNotTop
  | Hyp ->
     assert (List.length step.targets = 2);
     LeafHyp (List.hd step.targets, List.nth step.targets 1)
  | NotNot -> on_unary (fun f -> ERNotNot (normalize_form gamma defs f))
  | NotOr -> on_unary (fun f -> ERNotOr (normalize_form gamma defs f))
  | And -> on_unary (fun f -> ERAnd (normalize_form gamma defs f))
  | NotImplies -> on_unary (fun f -> ERNotImplies (normalize_form gamma defs f))
  | Or -> on_binary (fun f -> EROr (normalize_form gamma defs f))
  | Implies -> on_binary (fun f -> ERImplies (normalize_form gamma defs f))
  | NotAnd -> on_binary (fun f -> ERNotAnd (normalize_form gamma defs f))
  | Iff -> on_binary (fun f -> ERIff (normalize_form gamma defs f))
  | NotIff -> on_binary (fun f -> ERNotIff (normalize_form gamma defs f))
  | Exists -> on_quant (fun f tm -> EREx (normalize_form gamma defs f, tm))
  | NotAll -> on_quant (fun f tm -> ERNotAll (normalize_form gamma defs f, tm))
  | Forall -> on_quant (fun f tm -> ERAll (normalize_form gamma defs f, tm))
  | NotEx -> on_quant (fun f tm -> ERNotEx (normalize_form gamma defs f, tm))

exception MalformedProof of string
let rec compile etree =
  let open ProofInstance in
  match etree with
  | LeafBot -> Leaf None
  | LeafNotTop -> Node (Leaf None, AlphaNegNeg (Syntax.Neg (Syntax.Neg Syntax.Bot)), Leaf None)
  | LeafHyp (f, g) -> Leaf (Some (translate_EForm f, translate_EForm g))
  | Node (left, rule, right) ->
     match rule with
     | ERNotNot f -> Node (compile left, AlphaNegNeg (translate_EForm f), Leaf None)
     | ERNotOr  f -> Node (compile left, AlphaNegOr (translate_EForm f), Leaf None)
     | EROr     f -> Node (compile left, BetaOr (translate_EForm f), compile right)
     | ERAll (f, t) ->
        begin
          match t with
          | EFun _ -> raise (MalformedProof "On rule forall: expected a variable, got a constant or a function.")
          | EVar x -> Node (compile left, GammaAll (translate_EForm f, x), Leaf None)
        end
     | ERNotAll (f, t) -> Node (compile left, DeltaNegAll (translate_EForm f, translate_ETerm [] t), Leaf None)

     | ERAnd f ->
        (* [[ And f1 f2 ]] --> Neg (Or (Neg [[ f1 ]]) (Neg [[ f2 ]])) *)
        let f1, f2 =
          match f with
          | EAnd (f1,f2) -> translate_EForm f1, translate_EForm f2
          | _ -> raise (MalformedProof "On rule and: expected target formula to be a conjunction.") in
        let f = translate_EForm f in
        Node (Node (Node (compile left, AlphaNegNeg (Neg (Neg f2)), Leaf None),
                    AlphaNegNeg (Neg (Neg f1)), Leaf None),
              AlphaNegOr f, Leaf None)

     | ERNotImplies f ->
        (* [[ Neg (Imp f1 f2) ]] --> Neg (Or (Neg [[ f1 ]]) [[ f2 ]]) *)
        let f = translate_EForm f in
        let f1,f2 =
          match f with
          | Neg (Or (f1, f2)) -> f1,f2
          | _ -> raise (MalformedProof "On rule notImp: expected target formula to be a negated implication.") in
        Node (Node (compile left, AlphaNegNeg (Neg f1), Leaf None),
              AlphaNegOr f, Leaf None)

     | ERImplies f ->
        (* [[ Imp f1 f2 ]] --> Or (Neg [[ f1 ]]) [[ f2 ]] *)
        Node (compile left, BetaOr (translate_EForm f), Leaf None)

     | ERNotAnd f ->
        (* [[ Neg (And f1 f2) ]] --> Neg (Neg (Or (Neg [[ f1 ]]) (Neg [[ f2 ]]))) *)
        let f = translate_EForm f in
        let f' =
          match f with
          | (Neg (Neg f')) -> f'
          | _ -> raise (MalformedProof "On rule notAnd: expected target formula to be a negated conjunction.") in
        Node (Node (compile left, BetaOr f', compile right), AlphaNegNeg f, Leaf None)

     | ERIff f ->
        (* [[ Iff f1 f2 ]] = Neg (Or (Neg (Or (Neg [[ f1 ]]) [[ f2 ]])) (Neg (Or (Neg [[ f2 ]]) [[ f1 ]]))) *)
        let f1,f2 =
          match f with
          | EEqu (f1, f2) -> f1,f2
          | _ -> raise (MalformedProof "On rule iff: expected target formula to be an equivalence.") in
        let f = translate_EForm f in
        let f1' = translate_EForm f1 in
        let f2' = translate_EForm f2 in
        Node
          ( Node
              ( Node
                  ( Node
                      ( Node
                          ( compile left
                          , BetaOr (Or (Neg f2', f1'))
                          , Leaf (Some (f1', Neg f1')))
                      , BetaOr (Or (Neg f1', f2'))
                      , Node
                          ( Leaf (Some (f2', Neg f2'))
                          , BetaOr (Or (Neg f2', f1'))
                          , compile right))
                  , AlphaNegNeg (Neg (Neg (Or (Neg f2', f1'))))
                  , Leaf None)
              , AlphaNegNeg (Neg (Neg (Or (Neg f1', f2'))))
              , Leaf None)
          , AlphaNegOr f
          , Leaf None)

     | ERNotIff f ->
        (* [[ Not (Iff f1 f2) ]] = Neg (Neg (Or (Neg (Or (Neg [[ f1 ]]) [[ f2 ]])) (Neg (Or (Neg [[ f2 ]]) [[ f1 ]])))) *)
        let f1,f2 =
          match f with
          | ENeg (EEqu (f1, f2)) -> f1,f2
          | _ -> raise (MalformedProof "On rule notIff: expected target formula to be a negated equivalence.") in
        let f = translate_EForm f in
        let f' = match f with Neg (Neg f') -> f' | _ -> assert false in
        let f1' = translate_EForm f1 in
        let f2' = translate_EForm f2 in
        Node
          ( Node
              ( Node
                  ( Node
                      ( compile left
                      , AlphaNegNeg (Neg (Neg f1'))
                      , Leaf None)
                  , AlphaNegOr (Neg (Or (Neg f1', f2')))
                  , Leaf None)
              , BetaOr f'
              , Node
                  ( Node
                      ( compile right
                      , AlphaNegNeg (Neg (Neg f2'))
                      , Leaf None)
                  , AlphaNegOr (Neg (Or (Neg f2', f1')))
                  , Leaf None))
          , AlphaNegNeg f
          , Leaf None)

     | ERNotEx (f, t) ->
        (* [[ Neg (Ex f) ]] = Neg (Neg (All (Neg [[ f ]]))) *)
        let f = translate_EForm f in
        let f' =
          match f with
          | Neg (Neg f') -> f' |
          _ -> raise (MalformedProof "On rule notEx: expected target formula to be a negated existential.") in
        let x =
          match t with
          | EFun _ -> raise (MalformedProof "On rule notEx: expected new term to be a variable.")
          | EVar x -> x in
        Node
          ( Node
              ( compile left
              , GammaAll (f', x)
              , Leaf None)
          , AlphaNegNeg f
          , Leaf None)

     | EREx (f, t) ->
        (* [[ Ex f ]] = Neg (All (Neg [[ f ]])) *)
        let f = translate_EForm f in
        let t = translate_ETerm [] t in
        let g =
          match f with
          | Neg (All (Neg g)) ->
             let atom = AtomInstances.string_atom in
             varOpening (Syntax.opening_form atom atom atom) 0 t g
          | _ -> raise (MalformedProof "On rule ex: expected target formula to be existential.") in
        Node
          ( Node
              ( compile left
              , AlphaNegNeg (Neg (Neg g))
              , Leaf None)
          , DeltaNegAll (f, t)
          , Leaf None)

exception ProofCycleFound of string list
let interp_rules gamma defs tree =
  let open Decl in
  let get_children s = (Option.get s.inf).children in
  let vertices = List.map (fun s -> s.name) tree in
  let edges = List.map (fun s -> (s.name, get_children s)) tree in
  let assoc = List.map (fun s -> (s.name, s)) tree in
  try
    let root = List.hd (toposort vertices edges) in
    let etree = mk_etree gamma defs assoc (list_assoc root assoc) in
    compile etree
  with
  | CycleFound path -> raise (ProofCycleFound path)

let interp_decl_list ls =
  let open Decl in
  let rec interp_aux = function
    | [] -> ([], [], None, None, [])
    | x :: xs ->
       let defs,fs,sub,sk,tree = interp_aux xs in
       match x with
       | Decl.Subst (sigma,sk) ->
          if Option.is_some sub
          then raise MultipleSubEncountered
          else (defs,fs,Some sigma,Some sk,tree)
       | Decl.Plain step ->
          match step.role with
          | Axiom | Conj | NegConj -> defs,(step::fs),sub,sk,tree
          | LocDef -> step::defs,fs,sub,sk,tree
          | ProofStep -> defs,fs,sub,sk,step::tree in
  let defs,fs,sigma,sk,tree = interp_aux ls in
  let sk = Option.value sk ~default:Outer in
  let gamma = sort_normalization defs in
  let fs = interp_form_list gamma defs fs in
  let sigma = mk_substitution sigma in
  let tree = interp_rules gamma defs tree in
  fs,sigma,sk,tree
