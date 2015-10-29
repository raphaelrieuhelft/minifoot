open Parsetree
open Misc
open Defs
open Error
open Symbheap

let ident_of_p_exp e = match e.pexp_desc with
  | Pexp_ident(id) -> create_ident id
  | _ -> raise(Ast_unsupported(e.pexp_loc))

let exp_of_p_exp e = match e.pexp_desc with
  | Pexp_ident(id) -> EXP_ident (create_ident id)
  | Pexp_num(0) -> EXP_null
  | _ -> raise(Ast_unsupported(e.pexp_loc))

let exp_of_a_exp = function
  | Aexp_ident(id) -> EXP_ident(create_ident id)
  | Aexp_num(0)-> EXP_null
  | _ -> invalid_arg("exp_of_a_exp")

let cond_of_p_exp e = match e.pexp_desc with
  | Pexp_infix("==",e1,e2) -> PF_eq((exp_of_p_exp e1),(exp_of_p_exp e2))
  | Pexp_infix("!=",e1,e2) -> PF_neq((exp_of_p_exp e1),(exp_of_p_exp e2))
  | _ -> raise(Ast_unsupported(e.pexp_loc))

let pure_formula_of_prop = function
  | Aprop_equal(e1,e2)->PF_eq(exp_of_a_exp e1,exp_of_a_exp e2)
  | Aprop_not_equal(e1,e2)->PF_neq(exp_of_a_exp e1,exp_of_a_exp e2)
  | p -> 
    let buf = Buffer.create 16 in
    let fmt = Format.formatter_of_buffer buf in
    pp_assert fmt p;
    Format.pp_print_flush fmt ();
    let s = Buffer.contents buf in
    raise (Undef_pure_formula(s))

let spatial_of_spred = function 
  | Aspred_list(_)
  | Aspred_listseg(_) 
  | Aspred_dlseg(_) | Aspred_tree(_) -> raise Ptsto_only
  | Aspred_empty -> []
  | Aspred_pointsto(e1,[_,e2]) -> [SF_pointsto(exp_of_a_exp e1,exp_of_a_exp e2)]
  | Aspred_pointsto(e1,[]) -> [SF_pointsto(exp_of_a_exp e1,EXP_ident(wildcard()))]
  | Aspred_pointsto(_) -> raise Ptsto_only

let rec esh_of_a_prop = function
  | Aprop_infix(_) -> esh_false (*TODO : report a error message *)
  | Aprop_equal(e1,e2)->ESH_base([PF_eq(exp_of_a_exp e1,exp_of_a_exp e2)],[])
  | Aprop_not_equal(e1,e2)->ESH_base([PF_neq(exp_of_a_exp e1,exp_of_a_exp e2)],[])
  | Aprop_false-> esh_false
  | Aprop_ifthenelse(prop1,prop2,prop3)->
    ESH_ifthenelse(pure_formula_of_prop prop1,esh_of_a_prop prop2,esh_of_a_prop prop3)
  | Aprop_star(prop1,prop2)-> esh_star (esh_of_a_prop prop1) (esh_of_a_prop prop2)
  | Aprop_spred(spred) -> ESH_base([],spatial_of_spred spred)


(* check that all variables in the variable set vs are local variables *)
let check_all_locals vs locals loc =
  try
    let x = IdSet.choose (IdSet.diff vs locals)
    in raise (Ast_no_globals(x,loc))
  with Not_found -> ()

let atomic_command_of_stmt_desc = function
  | Pstm_assign(id,e) -> AC_assign(create_ident id,exp_of_p_exp e)
  | Pstm_fldlookup(id,e,_) -> AC_lookup(create_ident id,exp_of_p_exp e)
  | Pstm_fldassign(e1,_,e2) -> AC_update(exp_of_p_exp e1,exp_of_p_exp e2)
  | Pstm_new(id) -> AC_new(create_ident id)
  | Pstm_dispose(e)-> AC_dispose(exp_of_p_exp e)
  | _ -> invalid_arg "atomic_commmand_of_stmt_desc" 

let rec command_of_stmt locals arity stmt = 
  let command_desc = match stmt.pstm_desc with
    | Pstm_assign(_) | Pstm_fldlookup(_) | Pstm_fldassign(_) 
    | Pstm_new(_) | Pstm_dispose(_)-> 
      let c = atomic_command_of_stmt_desc stmt.pstm_desc in
      check_all_locals (vars_of_atomic_command c) locals stmt.pstm_loc;
      CO_atom(c)
    | Pstm_block(stm_list) -> CO_block(List.map (command_of_stmt locals arity) stm_list)
    | Pstm_if(e,stmt1,stmt2) -> 
      let cond = cond_of_p_exp e in
      check_all_locals (vars_of_condition cond) locals stmt.pstm_loc; 
      CO_if(cond,command_of_stmt locals arity stmt1,command_of_stmt locals arity stmt2)
    | Pstm_while(inv,e,body_stmt) ->
      let esh = match inv with
	| None -> raise (Ast_annot(stmt.pstm_loc))
	| Some(a_prop) -> esh_of_a_prop a_prop in 
      let cond = cond_of_p_exp e in
      check_all_locals (IdSet.union (non_ex_vars_of_esh esh) (vars_of_condition cond)) locals stmt.pstm_loc;
      CO_while(cond,esh,command_of_stmt locals arity body_stmt)
    | Pstm_withres(_) -> raise (Ast_resource(stmt.pstm_loc))
    | Pstm_fcall(fname,params)-> 
      co_parallelcalls locals arity stmt.pstm_loc [fname,params]    
    | Pstm_parallel_fcall(fname1,params1,fname2,params2) ->
      co_parallelcalls locals arity stmt.pstm_loc [fname1,params1;fname2,params2]       
  in {command_desc=command_desc;command_loc= stmt.pstm_loc;}
  
and co_parallelcalls locals arity loc l = 
  let f (fname,(ref_params,params)) =
    if ref_params != [] then raise (Ast_ref_vars(loc));
    (* check that the function is declared, and that the number of params is correct *)
    let n1,n2 = 
      try List.length params,arity fname
      with Not_found -> raise (Ast_unknown_fun (fname,loc))
    in
    if n1!=n2 then raise (Ast_wrong_arg_num ("",n1,n2,loc));
    fname,(List.map exp_of_p_exp params)
  in CO_parallelCalls(List.map f l)



let fundecl_of_item arity = function
  | Presource(_,_,_,loc) -> raise (Ast_resource(loc))
  | Pfundecl(fname,(ref_vars,params),precond,locals,stmt_list,postcond,loc1,loc2) ->
    if ref_vars!=[] then raise (Ast_ref_vars(loc1));
    let pre,post = match precond,postcond with
      | None,_ -> raise (Ast_annot(loc1))
      | _,None -> raise (Ast_annot(loc2))
      | Some(pre),Some(post) -> esh_of_a_prop pre, esh_of_a_prop post
    in 
    (* check that all non-existential vars of the pre are parameters *)
    let params = List.map create_ident params in
    let paramset = List.fold_right IdSet.add params IdSet.empty in(*IdSet.of_list params*)
    check_all_locals (non_ex_vars_of_esh pre) paramset loc1;
    (* check that all non-existential vars of the post are parameters or locals*)
    let locals = List.map create_ident locals in
    let localset = List.fold_right IdSet.add locals IdSet.empty in (*IdSet.of_list locals *)
    let declared_vars = IdSet.union paramset localset in
    check_all_locals (non_ex_vars_of_esh post) declared_vars loc2;
    (* check that locals are not parameters *)
    let () = 
      try 
	let x = IdSet.choose (IdSet.inter paramset localset) 
	in raise(Ast_param_locals (string_of_ident x,fname,loc1))
      with Not_found -> ()
    in {
      fd_name = fname;
      fd_params = params;
      fd_precondition = pre;
      fd_locals = locals;
      fd_body = {
	command_desc = CO_block(List.map (command_of_stmt declared_vars arity) stmt_list);
	command_loc = loc1;
      };
      fd_postcondition = post;
      fd_loc1 = loc1;
      fd_loc2 = loc2;
    }

let fundecls_of_itemlist il = 
  (* compute first the arity of each function *)
  (* and check that any two function declarations have different names *)
  let funarities = ref [] in
  let f = function
    | Pfundecl(fname,(_,params),_,_,_,_,loc,_) ->
      if List.mem_assoc fname !funarities 
      then raise (Ast_fun_already_defined(fname,loc))
      else funarities := (fname,List.length params) :: !funarities
    | _ -> ()
  in List.iter f il;
  let arity fname = List.assoc fname !funarities in
  (* process each fundecl item *)
  List.map (fundecl_of_item arity) il


    
