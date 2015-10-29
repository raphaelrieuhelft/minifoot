open Defs
open Symbheap
open Misc

exception LookupNull
exception UpdateNull

let rec symbseq si1 si2 = match si1 with
  |SI_skip -> si2
  |SI_atomic (asi, si) -> SI_atomic(asi, symbseq si si2)
  |SI_branch si3 si4 -> SI_branch (symbseq si3 si2) (symbseq si4 si2)

let rec chop_atom = function
  |AC_new id -> SI_atomic (ASI_exhale (ESH_base ([],[SF_pointsto(EXP_ident id, EXP_ident (wildcard ()))])), SI_skip)
  |AC_dispose id -> SI_atomic (ASI_inhale (ESH_base ([],[SF_pointsto(EXP_ident id,  EXP_ident (wildcard ()))])), SI_skip)
  |AC_assign(id, e) -> SI_atomic (ASI_exhale (ESH_base ([PF_eq(EXP_ident id, e)], [])), SI_skip)
  |AC_update(e1, e2) ->
		match e1 with
		 |EXP_null -> raise UpdateNull
		 |EXP_ident id -> symbseq (chop_atom AC_dispose id) SI_atomic (ASI_exhale (ESH_base ([],[SF_pointsto(e1, e2)])), SI_skip)
  |AC_lookup(id, e) -> 
		match e with 
		 |EXP_null -> raise LookupNull 
		 |EXP_ident id2 -> failwith "lookup not implemented"(*TODO*)
 
 
 
let rec chop fd = function
  |CO_block l -> List.fold_left (fun c (sis,vcs) -> let (sis1, vcs1) = (chop fd c)  in (symbseq sis1 sis, vcs1@vcs)) (SI_skip,[]) l		(* go right to left ? *)
  |CO_atom (ac) -> (chop_atom ac, [])
  |CO_if (cond, c1, c2) ->
		let si1, vc1 = chop fd c1 in
		let si2, vc2 = chop fd c2 in
		SI_branch (si1, si2), vc1@vc2
  
  
and vc_gen fd fundecls = 
	let si, vcs = chop fd fd.fd_body in
	{vc_pre = fd.fd_precondition; vc_symb_stmt = si; vc_post = fd.fd_postcondition; vc_info = "comes from "^fd.fd_name}


