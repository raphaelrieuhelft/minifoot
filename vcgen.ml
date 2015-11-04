open Defs
open Symbheap
open Misc

exception LookupNull
exception UpdateNull
exception DisposeNull
exception AssignNull

(*jsr record type, to be compiled into symbolic instructions*)
type jsr = {jsr_pre: ext_symb_heap; jsr_mod_var : IdSet.t; jsr_post: ext_symb_heap}

let compile_jsr jsr = SI_skip (*TODO*)

(*helper functions*)
let rec symbseq si1 si2 = match si1 with
  |SI_skip -> si2
  |SI_atomic (asi, si) -> SI_atomic(asi, symbseq si si2)
  |SI_branch (si3, si4) -> SI_branch ((symbseq si3 si2), (symbseq si4 si2))

let rename id id2 = SI_atomic(ASI_rename ( [id, EXP_ident(id2)]), SI_skip)

let rename id = rename id (gensym id)

let negate_pf = function 
	|PF_eq(e1,e2) -> PF_neq(e1,e2)
	|PF_neq(e1,e2) -> PF_eq(e1,e2)

(*computes the set of variables modified by a command*)
let rec mod_vars fundecls acc = function
  |CO_atom(AC_new id) -> IdSet.add id acc
  |CO_atom(AC_dispose _) -> acc
  |CO_atom(AC_assign(id,_)) -> IdSet.add id acc
  |CO_atom(AC_lookup(id, e)) -> IdSet.add id acc
  |CO_atom(AC_update(_,_)) -> acc
  |CO_block([]) -> acc
  |CO_block(h::t) -> mod_vars fundecls (mod_vars fundecls acc h.command_desc) (CO_block(t))
  |CO_if(_,c1,c2) -> mod_vars fundecls (mod_vars fundecls acc c1.command_desc) c2.command_desc
  |CO_while (_,_,c) -> mod_vars fundecls acc c.command_desc
  |CO_parallelCalls([]) -> acc
  |CO_parallelCalls((f,l)::t) -> 
			let fd = List.find (fun fd -> fd.fd_name = f) fundecls in
			let modf = IdSet.diff (mod_vars fundecls IdSet.empty fd.fd_body.command_desc) (List.fold_right IdSet.add fd.fd_params IdSet.empty)
			in
			let params = List.fold_left (fun s p -> match p with EXP_null -> s | EXP_ident id -> IdSet.add id s) IdSet.empty l in 
			mod_vars fundecls (IdSet.union acc (IdSet.union modf params)) (CO_parallelCalls(t))

(*compiles an atomic command into a symbolic instruction*)		
let rec chop_atom = function
  |AC_new id -> symbseq (rename id) (SI_atomic (ASI_exhale (ESH_base ([],[SF_pointsto(EXP_ident id, EXP_ident (wildcard ()))])), SI_skip))
  |AC_dispose (EXP_null) -> raise DisposeNull
  |AC_dispose (EXP_ident id) -> SI_atomic (ASI_inhale (ESH_base ([],[SF_pointsto(EXP_ident id,  EXP_ident (wildcard ()))])), SI_skip)
  |AC_assign(id, EXP_null) -> raise AssignNull
  |AC_assign(id, e) -> symbseq (rename id) (SI_atomic (ASI_exhale (ESH_base ([PF_eq(EXP_ident id, e)], [])), SI_skip))
  |AC_update(e1, e2) -> begin
		match e1 with
		 |EXP_null -> raise UpdateNull
		 |EXP_ident id -> symbseq (chop_atom (AC_dispose e1)) (SI_atomic(ASI_exhale (ESH_base ([],[SF_pointsto(e1, e2)])), SI_skip))
		 end
  |AC_lookup(id, e) -> 
		match e with 
		 |EXP_null -> raise LookupNull 
		 |EXP_ident id2 -> 
			let id1 = gensym id2 in 
			SI_atomic (ASI_inhale (ESH_base ([],[SF_pointsto(EXP_ident id,  EXP_ident id1)])), 
				SI_atomic (ASI_exhale(ESH_base([PF_eq(EXP_ident id1, EXP_ident id2)], [SF_pointsto(EXP_ident id, EXP_ident id1)])), SI_skip)
				)


let rec chop fundecls = function
  |CO_block l -> List.fold_left (fun (sis,vcs) c -> let (sis1, vcs1) = (chop fundecls c)  in (symbseq sis1 sis, vcs1@vcs)) (SI_skip,[]) (List.map (fun c -> c.command_desc) l)		(* go right to left ? *)
  |CO_atom (ac) -> (chop_atom ac, [])
  |CO_if (cond, c1, c2) ->
		let si1, vc1 = chop fundecls c1.command_desc in
		let si2, vc2 = chop fundecls c2.command_desc in
		SI_branch (si1, si2), vc1@vc2
  |CO_while (cond, inv, c) ->
		let post = esh_star inv (ESH_base([negate_pf cond], [])) in
		let jsr = {jsr_pre = inv; jsr_mod_var = mod_vars fundecls IdSet.empty c.command_desc; jsr_post = post} in
		(compile_jsr jsr, vc_gen_cmd c.command_desc inv post "comes from a while loop" fundecls)

and vc_gen_cmd cmd pre post info fundecls =	
	let si, vcs = chop fundecls cmd in
	{vc_pre = pre; vc_symb_stmt = si; vc_post = post; vc_info = info}::vcs
	
and vc_gen fd fundecls = vc_gen_cmd fd.fd_body.command_desc fd.fd_precondition fd.fd_postcondition ("comes from "^fd.fd_name) fundecls 

