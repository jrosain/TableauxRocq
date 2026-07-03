%{

	open Prelude
	open Grammar
	open ExtendedSyntax

	let rec nest_all vs f =
	  match vs with
	  | [] -> f
	  | x :: xs -> EAll (RocqStr.from_string x, nest_all xs f)

	let rec nest_ex vs f =
	  match vs with
	  | [] -> f
	  | v :: vs -> EEx (RocqStr.from_string v, nest_ex vs f)
%}

%token LPAR RPAR COMMA COLON DOT SEMI LBRACK RBRACK LACC RACC BACKQUOTE
%token FOF PLAIN SUBST AXIOM CONJECTURE NEGATED_CONJECTURE DEFINITION TH LEM COR FOT INFERENCE
%token LOR LAND LIMP LIFF LNEG LALL LEX FTRUE FFALSE ARR
%token <int> INT
%token <string> LOWER_WORD SQ_CHAR UPPER_WORD
%token FALSE NOT_TRUE HYP NOT_NOT AND NOT_OR NOT_IMP OR IMP NOT_AND IFF NOT_IFF EX NOT_ALL ALL NOT_EX
%token EOF

%start proof

%type <Decl.t list> proof

%%

proof:
  decl_list EOF { $1 }
;

decl_list:
    decl { [$1] }
  | decl decl_list { $1 :: $2 }
;

decl:
    fof_definition { $1 }
  | fof_proof_step { $1 }
  | fof_subst      { $1 }
;

fof_definition:
  FOF LPAR name COMMA role COMMA fof_formula RPAR DOT { Decl.mk_def $3 $5 $7 }
;

fof_proof_step:
    FOF LPAR name COMMA PLAIN COMMA fof_formula COMMA inference RPAR DOT { Decl.mk $3 Decl.ProofStep $7 $9 }
  | FOF LPAR name COMMA PLAIN COMMA LBRACK RBRACK COMMA inference RPAR DOT { Decl.mk_hyp $3 Decl.ProofStep [] $10 }
  | FOF LPAR name COMMA PLAIN COMMA LBRACK fof_formula_list RBRACK COMMA inference RPAR DOT { Decl.mk_hyp $3 Decl.ProofStep $8 $11 }
;

fof_subst:
  FOF LPAR name COMMA SUBST COMMA LACC subst_list RACC RPAR DOT { Decl.mk_sub $8 }
;

name:
    atomic_word { $1 }
  | INT         { string_of_int $1 }
;

name_list:
    name { [$1] }
  | name COMMA name_list { $1 :: $3 }
;

role:
    AXIOM { Decl.Axiom }
  | TH { Decl.Axiom }
  | LEM { Decl.Axiom }
  | COR { Decl.Axiom }
  | CONJECTURE { Decl.Conj }
  | NEGATED_CONJECTURE { Decl.NegConj }
  | DEFINITION { Decl.LocDef }
;

fof_formula:
    fof_binary_formula { $1 }
  | fof_unary_formula  { $1 }
  | fof_unitary_formula  { $1 }
;

fof_formula_list:
    fof_formula { [$1] }
  | fof_formula COMMA fof_formula_list { $1 :: $3 }
;

inference:
    INFERENCE LPAR rule COMMA LBRACK name_list RBRACK RPAR { Inference.mk $3 $6 None }
  | INFERENCE LPAR rule COMMA LBRACK RBRACK RPAR { Inference.mk $3 [] None }
  | INFERENCE LPAR rule COMMA LBRACK RBRACK COMMA FOT LPAR fof_term RPAR RPAR { Inference.mk $3 [] (Some $10) }
  | INFERENCE LPAR rule COMMA LBRACK name_list RBRACK COMMA FOT LPAR fof_term RPAR RPAR { Inference.mk $3 $6 (Some $11) }
;

subst: UPPER_WORD ARR fof_term { mk_sub $1 $3 }
;

subst_list:
    subst { [$1] }
  | subst SEMI subst_list { $1 :: $3 }
;

rule:
    FALSE { Inference.False }
  | NOT_TRUE { Inference.NotTrue }
  | HYP { Inference.Hyp }
  | NOT_NOT { Inference.NotNot }
  | AND { Inference.And }
  | NOT_OR { Inference.NotOr }
  | NOT_IMP { Inference.NotImplies }
  | OR { Inference.Or }
  | IMP { Inference.Implies }
  | NOT_AND { Inference.NotAnd }
  | IFF { Inference.Iff }
  | NOT_IFF { Inference.NotIff }
  | EX { Inference.Exists }
  | NOT_ALL { Inference.NotAll }
  | ALL { Inference.Forall }
  | NOT_EX { Inference.NotEx }
;

fof_binary_formula:
    fof_unit_formula LIFF fof_unit_formula { EEqu ($1, $3) }
  | fof_binary_rightassoc { $1 }
  | fof_binary_leftassoc { $1 }
;

fof_unary_formula: LNEG fof_unit_formula { ENeg $2 }
;

fof_unitary_formula:
    fof_quantified_formula { $1 }
  | fof_atomic_formula { $1 }
  | LPAR fof_formula RPAR { $2 }
;

fof_binary_leftassoc:
    fof_or_formula { $1 }
  | fof_and_formula { $1 }
;

fof_binary_rightassoc: fof_imp_formula { $1 }
;

fof_unit_formula:
    fof_unitary_formula { $1 }
  | fof_unary_formula { $1 }
;

fof_or_formula:
    fof_unit_formula LOR fof_unit_formula { EOr ($1, $3) }
  | fof_or_formula LOR fof_unit_formula { EOr ($1, $3) }
;

fof_and_formula:
    fof_unit_formula LAND fof_unit_formula { EAnd ($1, $3) }
  | fof_or_formula LAND fof_unit_formula { EAnd ($1, $3) }
;

fof_imp_formula:
    fof_unit_formula LIMP fof_unit_formula { EImp ($1, $3) }
  | fof_unit_formula LIMP fof_imp_formula  { EImp ($1, $3) }
;

fof_quantified_formula:
    LALL LBRACK fof_var_list RBRACK COLON fof_unit_formula { nest_all $3 $6 }
  | LEX  LBRACK fof_var_list RBRACK COLON fof_unit_formula { nest_ex $3 $6  }
;

fof_atomic_formula:
    atomic_word { EPred ((RocqStr.from_string $1), []) }
  | atomic_word LPAR fof_arguments RPAR { EPred ((RocqStr.from_string $1), $3) }
  | FTRUE { ETop }
  | FFALSE { EBot }
;

fof_var_list:
    UPPER_WORD { [$1] }
  | UPPER_WORD COMMA fof_var_list { $1 :: $3 }
;

fof_arguments:
    fof_term { [$1] }
  | fof_term COMMA fof_arguments { $1 :: $3 }
;

fof_term:
    fof_function_term { $1 }
  | UPPER_WORD { EVar (RocqStr.from_string $1) }
;

fof_function_term:
    atomic_word { EFun ((RocqStr.from_string $1), []) }
  | atomic_word LPAR fof_arguments RPAR { EFun ((RocqStr.from_string $1), $3) }
;

atomic_word:
    LOWER_WORD { $1 }
  | SQ_CHAR { $1 }
  | BACKQUOTE UPPER_WORD { $2 }
;
