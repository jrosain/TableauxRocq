{
  open Parser

  let tok = fun _ -> ()
    (* Printf.printf "%s\n%!" *)
}

let nat = ['0'-'9']+
let int = '-'?nat

let lower = ['a'-'z']['a'-'z' 'A'-'Z' '0'-'9' '_']*
let upper = ['A'-'Z']['a'-'z' 'A'-'Z' '0'-'9' '_']*

let sq = '\''[' '-'&' '('-'[' ']'-'~']+'\''

let comment = '%'[^'\n']*

rule token = parse
  | [' ' '\t' '\r'] { token lexbuf }
  | comment { token lexbuf }
  | '\n' { Lexing.new_line lexbuf; token lexbuf }
  | eof { EOF }

  | '('   { tok "LPAR"; LPAR }
  | ')'   { tok "RPAR"; RPAR }
  | ','   { tok "COMMA"; COMMA }
  | ':'   { tok "COLON"; COLON }
  | '.'   { tok "DOT"; DOT }
  | ';'   { tok "SEMI"; SEMI }
  | '['   { tok "LBRACK"; LBRACK }
  | ']'   { tok "RBRACK"; RBRACK }
  | '{'   { tok "LACC"; LACC }
  | '}'   { tok "RACC"; RACC }
  | '`'   { tok "BACKQUOTE"; BACKQUOTE }

  | "fof" { tok "FOF"; FOF }
  | "plain" { tok "PLAIN"; PLAIN }
  | "substitution" { tok "SUBST"; SUBST }
  | "axiom" { tok "AXIOM"; AXIOM }
  | "hypothesis" { tok "AXIOM"; AXIOM }
  | "lemma" { tok "LEM"; LEM }
  | "theorem" { tok "THM"; TH }
  | "corollary" { tok "COR"; COR }
  | "conjecture" { tok "CONJ"; CONJECTURE }
  | "negated_conjecture" { tok "NEG_CONJ"; NEGATED_CONJECTURE }
  | "definition" { tok "DEF"; DEFINITION }
  | "$fot" { tok "FOT"; FOT }
  | "inference" { tok "INFERENCE"; INFERENCE }

  | "|" { tok "LOR"; LOR }
  | "&" { tok "LAND"; LAND }
  | "=>" { tok "LIMP"; LIMP }
  | "<=>" { tok "LIFF"; LIFF }
  | "~" { tok "LNEG"; LNEG }
  | "!" { tok "LALL"; LALL }
  | "?" { tok "LEX"; LEX }

  | "false" { tok "FALSE"; FALSE }
  | "leftFalse" { tok "FALSE"; FALSE }
  | "notTrue" { tok "NOT_TRUE"; NOT_TRUE }
  | "leftNotTrue" { tok "NOT_TRUE"; NOT_TRUE }
  | "hyp" { tok "HYP"; HYP }
  | "leftHyp" { tok "HYP"; HYP }
  | "notNot" { tok "NOT_NOT"; NOT_NOT }
  | "leftNotNot" { tok "NOT_NOT"; NOT_NOT }
  | "notOr" { tok "NOT_OR"; NOT_OR }
  | "leftNotOr" { tok "NOT_OR"; NOT_OR }
  | "and" { tok "AND"; AND }
  | "leftAnd" { tok "AND"; AND }
  | "notImplies" { tok "NOT_IMP"; NOT_IMP }
  | "leftNotImplies" { tok "NOT_IMP"; NOT_IMP }
  | "or" { tok "OR"; OR }
  | "leftOr" { tok "OR"; OR }
  | "implies" { tok "IMP"; IMP }
  | "leftImplies" { tok "IMP"; IMP }
  | "notAnd" { tok "NOT_AND"; NOT_AND }
  | "leftNotAnd" { tok "NOT_AND"; NOT_AND }
  | "iff" { tok "IFF"; IFF }
  | "leftIff" { tok "IFF"; IFF }
  | "notIff" { tok "NOT_IFF"; NOT_IFF }
  | "leftNotIff" { tok "NOT_IFF"; NOT_IFF }
  | "exists" { tok "EX"; EX }
  | "leftExists" { tok "EX"; EX }
  | "notAll" { tok "NOT_ALL"; NOT_ALL }
  | "leftNotAll" { tok "NOT_ALL"; NOT_ALL }
  | "forall" { tok "ALL"; ALL }
  | "leftForall" { tok "ALL"; ALL }
  | "notEx" { tok "NOT_EX"; NOT_EX }
  | "leftNotEx" { tok "NOT_EX"; NOT_EX }

  | "$true" { tok "FTRUE"; FTRUE }
  | "$false" { tok "FFALSE"; FFALSE }

  | "->" { tok "ARR"; ARR }

  | int as n { tok "INT"; INT (int_of_string n) }

  | lower as w { tok "LOWER"; LOWER_WORD w }
  | upper as w { tok "UPPER"; UPPER_WORD w }

  | sq as w { tok "SQ"; SQ_CHAR w }
