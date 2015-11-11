open Defs
open Symbheap
open Misc
open Entailment

exception LookupNull
exception UpdateNull
exception DisposeNull
exception AssignNull
exception CallNull

(*jsr record type, to be compiled into symbolic instructions*)
type jsr = {jsr_pre: ext_symb_heap; jsr_mod_vars : IdSet.t; jsr_post: ext_symb_heap}

let rec pure_of_esh = function
	|ESH_base(pf,_) -> ESH_base(pf, [])
	|ESH_ifthenelse(pf,esh1, esh2) -> ESH_ifthenelse(pf, pure_of_esh esh1, pure_of_esh esh2)

(*compiles a jsr, adapted from the inference rule in http://arxiv.org/pdf/1204.4804.pdf page 6*)
let compile_jsr jsr = 
	let subst = List.map (fun id -> (id, EXP_ident(gensym id))) (IdSet.elements jsr.jsr_mod_vars) in
	SI_atomic( ASI_inhale(jsr.jsr_pre), 
		SI_atomic (ASI_rename(subst),
			SI_atomic( ASI_exhale(jsr.jsr_post),
				SI_skip)))

(*helper functions*)
let rec symbseq si1 si2 = match si1 with
  |SI_skip -> si2
  |SI_atomic (asi, si) -> SI_atomic(asi, symbseq si si2)
  |SI_branch (si3, si4) -> SI_branch ((symbseq si3 si2), (symbseq si4 si2))
  
let rename id id2 = SI_atomic(ASI_rename ( [id, EXP_ident(id2)]), SI_skip)

let rename id = rename id (gensym id)

let esh_pointsto e1 e2 = ESH_base([], [SF_pointsto(e1,e2)])
let esh_eq e1 e2 = ESH_base([PF_eq(e1,e2)], [])

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
			(*parameters are passed by value : they are not modified*)
			in
			let params = List.fold_left (fun s p -> match p with EXP_null -> s | EXP_ident id -> IdSet.add id s) IdSet.empty l in 
			mod_vars fundecls (IdSet.union acc (IdSet.union modf params)) (CO_parallelCalls(t))
			(* should be empty every time if all variables are local ?*)

(*compiles an atomic command into a jsr, then into a symbolic instruction via compile_jsr*)				
let rec chop_atom = function
	|AC_new id -> compile_jsr {jsr_pre = esh_emp; jsr_mod_vars = IdSet.singleton id; jsr_post = esh_pointsto (EXP_ident id) (EXP_ident (wildcard ()))}
	|AC_dispose (EXP_null) -> raise DisposeNull
	|AC_dispose (EXP_ident id) -> compile_jsr {jsr_pre = esh_pointsto (EXP_ident id) (EXP_ident (wildcard ())); jsr_mod_vars = IdSet.empty; jsr_post = esh_emp}
	|AC_assign(id, EXP_null) -> raise AssignNull
	|AC_assign(id, EXP_ident id2) when id = id2 -> SI_skip (*not the same as next case: x not modified*)
	|AC_assign(id, EXP_ident id2) -> compile_jsr {jsr_pre = esh_eq (EXP_ident id) (EXP_ident (wildcard ())); jsr_mod_vars = IdSet.singleton id; jsr_post = esh_eq (EXP_ident id) (EXP_ident id2)}
	|AC_update(e1, e2) -> begin
		match e1 with
		 |EXP_null -> raise UpdateNull
		 |EXP_ident id -> compile_jsr {jsr_pre = esh_pointsto (EXP_ident id) (EXP_ident (wildcard ())); jsr_mod_vars = IdSet.empty; jsr_post = esh_pointsto (EXP_ident id) e2}
		end
	|AC_lookup(id, e) -> begin
		match e with
		 |EXP_null -> raise LookupNull
		 |EXP_ident id2 ->
			let next = EXP_ident (wildcard ()) in
			compile_jsr {jsr_pre = esh_pointsto e next; jsr_mod_vars = IdSet.singleton id; jsr_post = ESH_base([PF_eq(EXP_ident id, next)], [SF_pointsto(e, next)])}
		end

let jsrs_of_call fd fundecls callargs =
	let to_rename = IdSet.union (List.fold_right IdSet.add fd.fd_params IdSet.empty) (IdSet.union (vars_of_esh fd.fd_precondition) (vars_of_esh fd.fd_postcondition)) in
	let subst_ids = List.map (fun id -> (id, gensym id)) (IdSet.elements to_rename) in
	let subst = List.map (fun (a,b) -> (a, EXP_ident b)) subst_ids in
	let post1 = ESH_base((List.map2 (fun ca p -> PF_eq(ca, EXP_ident (List.assoc p subst_ids))) callargs fd.fd_params), []) in	(*call by value : copy each parameter*)
	let modf = mod_vars fundecls IdSet.empty (fd.fd_body).command_desc in
	let modf = IdSet.fold (fun x s -> IdSet.add (try List.assoc x subst_ids with Not_found -> x) s) modf IdSet.empty in (* the modified variables are the copies that are passed to the function *)
	let pre2 = esh_rename subst fd.fd_precondition in
	let post2 = esh_rename subst fd.fd_postcondition in
	{jsr_pre = esh_emp; jsr_mod_vars = IdSet.empty; jsr_post = post1}, {jsr_pre = pre2; jsr_mod_vars = modf; jsr_post = post2}
	

let rec chop fundecls = function
  |CO_block l -> List.fold_left (fun (sis,vcs) c -> let (sis1, vcs1) = (chop fundecls c)  in (symbseq sis sis1, vcs1)) (SI_skip,[]) (List.map (fun c -> c.command_desc) l)		
  |CO_atom (ac) -> (chop_atom ac, [])
  |CO_if (cond, c1, c2) ->
		let si1, vc1 = chop fundecls c1.command_desc in
		let si2, vc2 = chop fundecls c2.command_desc in
		SI_branch ((SI_atomic(ASI_exhale(cond) ,si1)),(SI_atomic (ASI_exhale(pure_neg cond),si2))), vc1@vc2
  |CO_while (cond, inv, c) ->
		let post = esh_star inv (ESH_base([pure_neg cond], [])) in
		let jsr = {jsr_pre = inv; jsr_mod_vars = mod_vars fundecls IdSet.empty c.command_desc; jsr_post = post} in
		(compile_jsr jsr, vc_gen_cmd c.command_desc (esh_star inv (ESH_base([cond], []))) inv "comes from a while loop" fundecls)
  |CO_parallelCalls(l) ->
		let jsrs_list = List.map 
		(fun (fname, args) -> let fd = List.find (fun fd -> fd.fd_name = fname) fundecls in jsrs_of_call fd fundecls args) l in
		let (post1, pre2, post2, modv) = List.fold_left (fun (post1, pre2, post2, modv) (jsr1, jsr2) ->
			((esh_star post1 jsr1.jsr_post), (esh_star pre2 jsr2.jsr_pre), (esh_star post2 jsr2.jsr_post),  (IdSet.union modv jsr2.jsr_mod_vars))) (esh_emp, esh_emp, esh_emp, IdSet.empty) jsrs_list in 
			(*union is disjoint by construction*)
		let jsr1 = {jsr_pre = esh_emp; jsr_mod_vars = IdSet.empty; jsr_post = post1} in
		let jsr2 = {jsr_pre = pre2; jsr_mod_vars = modv; jsr_post = post2} in
		(symbseq (compile_jsr jsr1) (compile_jsr jsr2), [])


and vc_gen_cmd cmd pre post info fundecls =	
	let si, vcs = chop fundecls cmd in
	{vc_pre = pre; vc_symb_stmt = si; vc_post = post; vc_info = info}::vcs
	
let vc_gen fd fundecls = vc_gen_cmd fd.fd_body.command_desc fd.fd_precondition fd.fd_postcondition ("comes from "^fd.fd_name) fundecls 

