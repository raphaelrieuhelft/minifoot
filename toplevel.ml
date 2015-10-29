open Misc
open Parsetree
open Defs

let wp lex =
  let (Pprogram (_,iteml)) =
    let ast = Parser.program Lexer.token lex in
      Parsing.clear_parser();
      ast
  in Ast.fundecls_of_itemlist iteml

let verify_wp lex =
  let fmt = !Config.formatter
  and valid = ref true
  in 
  try Error.report (fun () ->
    let fundecls = wp lex in
    let f fundecl =
      Format.fprintf fmt "@.Function %s@." fundecl.fd_name;
      let vcs = Vcgen.vc_gen fundecl fundecls in
      let g vc = valid := (Symbexe.check_vc vc) && !valid in
      List.iter g vcs
    in
    for i=1 to !Config.repetitions do 
      List.iter f fundecls 
    done;
    Format.fprintf fmt "@.%sValid@." (if !valid then "" else "NOT "))
  with Invalid_argument s -> Format.pp_print_string fmt s

let verify_wp_string s =
  let lex = Lexing.from_string s
  in verify_wp lex

let verify_wp_fname fname =
  let ic = if fname = "-" then stdin else open_in fname in
  let lex = Lexing.from_channel ic in
  Lexer.init lex fname;
  init_gensym ();
  verify_wp lex;
  close_in ic
