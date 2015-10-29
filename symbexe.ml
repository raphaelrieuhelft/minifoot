open Defs
open Error
open Symbheap
open Entailment
open Print

exception No_frame of ext_symb_heap * ext_symb_heap * string 

let execute_atomic_statement esh info = function
  | ASI_inhale(esh2) -> 
    let ans = match get_frame esh esh2 with
      | Some(esh3) -> esh3
      | None -> raise (No_frame(esh,esh2,info))
    in ans
  | ASI_exhale(esh2) -> esh_star esh esh2
  | ASI_rename(subst) -> esh_rename subst esh

let rec execute_statement esh info = function
  | SI_skip -> 
    [esh]
  | SI_atomic(astmt,stmt) -> 
    execute_statement (execute_atomic_statement esh info astmt) info stmt
  | SI_branch(stmt1,stmt2) ->
    (execute_statement esh info stmt1)@(execute_statement esh info stmt2)

let check_vc vc =
  if !Config.verbose1 then Format.fprintf !Config.formatter "CHECKING %a" pp_vc vc;
  let esh_list = 
    try execute_statement vc.vc_pre vc.vc_info vc.vc_symb_stmt 
    with No_frame(esh1,esh2,info) -> begin
      Format.fprintf fmt "ERROR cannot find frame: %s@.%a@." info 
	pp_frame (esh1,esh2);
      []
    end
  in
  let rec f res = function
    | esh::esh_list ->
      if entails esh vc.vc_post
      then f res esh_list
      else begin 	
	Format.fprintf fmt "ERROR invalid entailment: %s@. %a@." vc.vc_info 
	  Print.pp_entailment (esh,vc.vc_post);
	f false esh_list
      end
    | [] -> 
      if !Config.verbose1 then Format.fprintf !Config.formatter "Done with this VC@."; 
      res
  in (esh_list != []) && f true esh_list
