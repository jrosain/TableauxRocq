let print_certificate file sko =
  let mk_line s =
    let l = String.length s in
    let st = 60 - (l / 2) in
    let ed = 120 - st - l in
    Printf.sprintf "│%s%s%s│" (String.make st ' ') file (String.make ed ' ') in
  let file = mk_line file in
  Printf.printf {|
╔────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────╗
│                  _____          _   _  __ _           _                __   _____                  __                  │
│                 / ____|        | | (_)/ _(_)         | |              / _| |  __ \                / _|                 │
│                | |     ___ _ __| |_ _| |_ _  ___ __ _| |_ ___    ___ | |_  | |__) | __ ___   ___ | |_                  │
│                | |    / _ \ '__| __| |  _| |/ __/ _` | __/ _ \  / _ \|  _| |  ___/ '__/ _ \ / _ \|  _|                 │
│                | |___|  __/ |  | |_| | | | | (_| (_| | ||  __/ | (_) | |   | |   | | | (_) | (_) | |                   │
│                 \_____\___|_|   \__|_|_| |_|\___\__,_|\__\___|  \___/|_|   |_|   |_|  \___/ \___/|_|                   │
│                                                                                                                        │
│                                                                                                                        │
│          ______)                                                                                                       │
│         (, /  /)                       ,  /) ,                  ,                          /)      /)                  │
│           /  (/    _    _   _  __ _/_    //    _  _  _/_  _       _     _  _   _ _   __  _(/  _  _(/   _/_ ___ '       │
│        ) /   / )__(/_  (___(/_/ (_(___(_/(__(_(__(_(_(___(/_  _(_/_)_  (_(_(_(/ (_(_/ (_(_(__(/_(_(_   (__(_)  '       │
│       (_/                              /)                                                                              │
│                                       (/                                                                               │
│                                                                                                                        │
│                                                                                                                        │
%s
│                                                                                                                        │
│               for being a successful first-order tableau proof certificate in %s Skolemization.                     │
│                                                                                                                        │
│                                                                                                                        │
│                                                                                                                        │
│                                                                                                                        │
│                8                                                   8""""8 8"""88 8   8 8     8"""" ""8""               │
│                8  eeeee eeeee e   e eeee eeeee    eeeee  e    e    8    8 8    8 8   8 8     8       8                 │
│                8e 8   " 8   " 8   8 8    8   8    8   8  8    8    8eeee8 8    8 8e  8 8e    8eeee   8e                │
│                88 8eeee 8eeee 8e  8 8eee 8e  8    8eee8e 8eeee8    88     8    8 88  8 88    88      88                │
│                88    88    88 88  8 88   88  8    88   8   88      88     8    8 88  8 88    88      88                │
│                88 8ee88 8ee88 88ee8 88ee 88ee8    88eee8   88      88     8eeee8 88ee8 88eee 88eee   88                │
│                                                                                                                        │
╚────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────╝|} file sko

let main () =
  let file = ref "" in
  let fancy = ref false in
  let optlist =
    [ ("-fancy", Arg.Set fancy, "Print a fancy certificate instead of a simple message on successful verification. Default: false.")
    ] in
  let msg = "Welcome to POULET, the PrOof-checker for tableaUx in first-order Logic Extracted from Tableauxrocq.\n" in
  let _ = Arg.parse optlist (fun s -> file := s) msg in
  let where_from = open_in !file in
  let lexbuf = Lexing.from_channel where_from in
  begin
    try
      let declarations = Lib.Parser.proof Lib.Lexer.token lexbuf in
      let fs,sigma,sk,ruletree = Lib.Grammar.interp_decl_list declarations in
      let status,err = Lib.Checker.coq_CheckProof (Lib.Grammar.interp_sko sk) fs sigma ruletree in
      if status then
        ((if !fancy then print_certificate !file (Lib.Grammar.sko_str sk)
          else Printf.printf "The file contains a valid tableau proof.");
         exit 0)
      else
        Printf.printf "Proof checking has reported an error:\n\"%s\"\n" (Lib.Prelude.RocqStr.to_string (List.hd err))
    with
    | Lib.Grammar.MultipleSubEncountered ->
       Printf.printf "Error: multiple declarations with the substitution role encountered.\n"
    | Lib.Grammar.NoSuchName name ->
       Printf.printf "Error: found reference to an unknown name \"%s\".\n" name
    | Lib.Grammar.DefCycleFound path ->
       Printf.printf "Error: cycle of dependencies between the definitions (%s).\n" (String.concat " -> " path)
    | Lib.Grammar.ProofCycleFound path ->
       Printf.printf "Error: cyclic proof encountered (%s).\n" (String.concat " -> " path)
    | Lib.Grammar.MalformedProof reason ->
       Printf.printf "Error. %s\n" reason
    | Lib.Parser.Error ->
       Printf.printf "Syntax error on line %d encountered on lexeme \"%s\"\n"
         lexbuf.Lexing.lex_curr_p.pos_lnum
         (Lexing.lexeme lexbuf)
  end;
  exit 1

let _ = main ()
