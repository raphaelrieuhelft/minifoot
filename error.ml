(* lexer *)
exception Illegal_character of char * Location.t
exception Unterminated_comment of Location.t

(* parser *)
exception Not_distinct of string * Location.t
exception Parameters_not_variables of Location.t
exception Parse_error of Location.t


(* ast *)
exception Ast_unsupported of Location.t
exception Ast_no_globals of Misc.ident * Location.t
exception Ast_annot of Location.t
exception Ast_resource of Location.t
exception Ast_ref_vars of Location.t
exception Ast_anot of Location.t
exception Ast_unknown_fun of string * Location.t
exception Ast_wrong_arg_num of string * int * int * Location.t
exception Ast_param_locals of string * string * Location.t
exception Ast_fun_already_defined of string * Location.t
exception Undef_pure_formula of string
exception Ptsto_only

exception Imprecise_formula of Defs.symb_heap


(* reporting *)
let fmt = !Config.formatter

let sprint loc = "\n" ^ (Location.sprint loc)

let report ?(nonfatal_thunk = fun () -> assert false) thunk =
  try thunk () with
      

(* lexer *)
    | Illegal_character(c,loc) ->
	invalid_arg((sprint loc) ^ (Format.sprintf "Syntax error: Illegal character (%s)@." (Char.escaped c)))
    | Unterminated_comment(loc) ->
	invalid_arg ((sprint loc) ^ (Format.sprintf "Syntax error: Unterminated comment@."))

(* parser *)
    | Not_distinct(s,loc) ->
	invalid_arg((sprint loc) ^ (Format.sprintf "Syntax error: %s must be distinct@." s))
    | Parameters_not_variables(loc) ->
	invalid_arg((sprint loc) ^ (Format.sprintf "Syntax error: Reference parameters must be variables@."))
    | Parse_error(loc) ->
	invalid_arg((sprint loc) ^ (Format.sprintf "Parse error@."))
    | Parsetree.Undef_a_exp_of_p_exp(loc) ->
	invalid_arg((sprint loc) ^ (Format.sprintf "Unknown expression@."))
    | Parsetree.Undef_a_prop_of_p_exp(loc) ->
	invalid_arg((sprint loc) ^ (Format.sprintf "Unknown proposition@."))
    | Undef_pure_formula(s) ->
	invalid_arg("Syntax error: " ^ s ^ " not an atomic pure formula\n")
(* ast *)
    | Ast_unsupported(loc) -> 
      invalid_arg((sprint loc) ^ (Format.sprintf "This smallfoot feature is not supported by minifoot@."))
    | Ast_no_globals(id,loc) ->
      invalid_arg((sprint loc) ^ (Format.sprintf "Variable %s undeclared. Minifoot does not support global vars@." (Misc.string_of_ident id)))
    | Ast_annot(loc) -> 
      invalid_arg((sprint loc) ^ (Format.sprintf "Minifoot requires an annotation@."))
    | Ast_unknown_fun (fid,loc) ->
	invalid_arg((sprint loc) ^ (Format.sprintf "Function %s is not defined@." fid))
    | Ast_wrong_arg_num (s,n1,n2,loc) ->
	invalid_arg((sprint loc) ^ (Format.sprintf "Function call has %d %s arguments but %d expected@." n1 s n2))
    | Ast_param_locals (x,fid,loc) ->
	invalid_arg((sprint loc) ^ (Format.sprintf "Variable %s in function %s cannot be both a parameter and a local@." x fid))
    | Ast_resource(loc) ->  
	invalid_arg((sprint loc) ^ (Format.sprintf "Minifoot does not support resources@."))
    | Ast_ref_vars(loc) ->
	invalid_arg((sprint loc) ^ (Format.sprintf "Minifoot does not support reference variables@."))
    | Ast_fun_already_defined(fname,loc) ->
      invalid_arg((sprint loc) ^ (Format.sprintf "Function %s defined twice@." fname))
    | Ptsto_only -> invalid_arg("Minifoot does not support lists, trees or doubly-linked lists.@.")

    | Imprecise_formula(sh) ->
      Format.fprintf !Config.formatter "Imprecise assertion %a@. Minifoot requires precise assertions" Print.pp_sh sh



