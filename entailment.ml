open Defs
open Print
open Symbheap
open Misc
open Error

type esh = ext_symb_heap
type frame = esh option

let print = Format.fprintf !Config.formatter

exception ImpliesFalse
exception ImpreciseFormula
exception NoFrameExists

let exp_is_existential = function
  | EXP_null -> false
  | EXP_ident id -> is_existential id

let esh_of_pure c = ESH_base([c], [])

module ESet = Set.Make (struct type t = exp let compare = compare end)   
module ESSet = Set.Make (struct type t = ESet.t let compare = compare end)
module EMap = Map.Make (struct type t = exp let compare = compare end) 

(* like List.find, returns an element of the set satisfying predicate
   if there is one, else raises Not_found,
   unlike _Set.find which returns an element equal to the argument *)
let eset_find predicate eset = ESet.choose (ESet.filter predicate eset)
let esset_find predicate esset = ESSet.choose (ESSet.filter predicate esset)

let unify e1 e2 esset =
  let eset_containing e =
    try esset_find (ESet.mem e) esset 
    with Not_found -> ESet.singleton e 
  in
  let eset1 = eset_containing e1 in
  let eset2 = eset_containing e2 in
  let esset = ESSet.remove eset1 esset in
  let esset = ESSet.remove eset2 esset in
  ESSet.add (ESet.union eset1 eset2) esset
  
let choose_repr eset =
  if ESet.mem EXP_null eset then EXP_null else
  try eset_find (fun e -> not (exp_is_existential e)) eset
  with Not_found -> ESet.choose eset
  
let compute_repr_map pure_formulas =
  let esset = List.fold_left
    (fun esset -> function
	  | PF_eq (e1,e2) -> unify e1 e2 esset
	  | PF_neq _ -> esset)
	ESSet.empty pure_formulas
  in
  List.fold_left
    (fun repr_map eset ->
	  let repr = choose_repr eset in
	  List.fold_left (fun repr_map e -> EMap.add e repr repr_map) repr_map (ESet.elements eset))
	EMap.empty (ESSet.elements esset)

let neqs_from_pure repr_map pure_formulas =
  List.fold_left (fun neqs -> function
    | PF_eq _ -> neqs
	| PF_neq (e1,e2) ->
	  let repr1 = EMap.find e1 repr_map in
	  let repr2 = EMap.find e2 repr_map in
	  if repr1 = repr2 then raise ImpliesFalse
	  else (repr1,repr2)::neqs
	) [] pure_formulas

let rec list_remove_once x = function
  | [] -> []
  | hd::tl when hd = x -> tl
  | hd::tl -> hd::(list_remove_once x tl)

let process_spatial_formulas repr_map spatial_formulas =
  let pointsto_couples = List.map (function 
    | SF_false -> raise NoFrameExists
	| SF_pointsto (e1,e2) -> (e1,e2)
	) spatial_formulas in
  let add_if_absent e repr_map =
    if EMap.mem e repr_map then repr_map
	else EMap.add e e repr_map
  in
  let repr_map = List.fold_left (fun repr_map (e1,e2) ->
      add_if_absent e1 (add_if_absent e2 repr_map)
	) repr_map pointsto_couples in
  let pointsto_couples = List.map (fun (e1,e2) -> 
    (EMap.find e1 repr_map, EMap.find e2 repr_map)) pointsto_couples in
  let first_exp_is_precise precise_exps (e1,_) =
	(not (exp_is_existential e1)) || ESet.mem e1 precise_exps in
  let rec loop pointsto_couples precise_exps pointsto_map =
    if pointsto_couples = [] then
	  pointsto_map
	else
	  let (e1,e2) =
	    try List.find (first_exp_is_precise precise_exps) pointsto_couples
		with Not_found -> raise ImpreciseFormula
	  in
	  let next_pointsto_couples = list_remove_once (e1,e2) pointsto_couples in
	  if (e1 = EXP_null) || (EMap.mem e1 pointsto_map) then raise ImpliesFalse
	  else
	    let next_pointsto_map = EMap.add e1 e2 pointsto_map in
		let next_precise_exps = ESet.add e2 precise_exps in
		loop next_pointsto_couples next_precise_exps next_pointsto_map
  in
  let pointsto_map = loop pointsto_couples ESet.empty EMap.empty in
  repr_map, pointsto_map


let neqs_from_spatial pointsto_map =
  let pointings = List.map fst (EMap.bindings pointsto_map) in
  let rec compute_neqs exps acc_neqs =
    if exps = [] then acc_neqs else
	  let e = List.hd exps in
	  let rest_exps = List.tl exps in
	  let new_neqs = (EXP_null,e)::(List.map (fun e2 -> (e,e2)) rest_exps) in
	  compute_neqs rest_exps (new_neqs@acc_neqs)
  in
  compute_neqs pointings []


  
let update_repr_map repr_map right_pure_formulas =
  let process_eq (repr_map, esset) e1 e2 =
	if EMap.mem e1 repr_map then
	  let repr1 = EMap.find e1 repr_map in
	  if EMap.mem e2 repr_map then
	    let repr2 = EMap.find e2 repr_map in
	    if repr1 = repr2 then (repr_map, esset)
		else raise NoFrameExists
	  else if exp_is_existential e2 then
		(EMap.add e2 repr1 repr_map, esset)
	  else raise NoFrameExists
	else if exp_is_existential e1 then
	  if EMap.mem e2 repr_map then
	    let repr2 = EMap.find e2 repr_map in
	    (EMap.add e1 repr2 repr_map, esset)
	  else if exp_is_existential e2 then
		(repr_map, unify e1 e2 esset)
	  else raise NoFrameExists
	else raise NoFrameExists
  in
  let (repr_map, esset) = List.fold_left
    (fun (repr_map, esset) -> function
	  | PF_eq (e1,e2) -> process_eq (repr_map, esset) e1 e2
	  | PF_neq _ -> (repr_map, esset))
	(repr_map, ESSet.empty) right_pure_formulas
  in
  (repr_map, esset)


let compute_frame_map repr_map exst_cls pointsto_map right_spatial_formulas =
  let spatials = List.map (function 
    | SF_false -> raise NoFrameExists
	| SF_pointsto (e1,e2) -> (e1,e2)
	) right_spatial_formulas in
  let rec loop repr_map exst_cls pointsto_map spatials =
    if spatials = [] then (repr_map, exst_cls, pointsto_map) else
    let (e1,e2) = 
	  try List.find (fun (e1,_) -> EMap.mem e1 repr_map) spatials
	  with Not_found -> raise NoFrameExists
	in
	let spatials' = list_remove_once (e1,e2) spatials in
	let repr1 = EMap.find e1 repr_map in
	if EMap.mem repr1 pointsto_map then
	  let target = EMap.find repr1 pointsto_map in
	  let pointsto_map' = EMap.remove repr1 pointsto_map in
	  if EMap.mem e2 repr_map then
	    let repr2 = EMap.find e2 repr_map in
		if repr2 = target then
		  loop repr_map exst_cls pointsto_map' spatials'
		else raise NoFrameExists
	  else
	    try
		  let e2_cl = esset_find (fun cl -> ESet.mem e2 cl) exst_cls in
		  let repr_map' = ESet.fold 
		    (fun e repr_map -> EMap.add e target repr_map) e2_cl repr_map in
		  let exst_cls' = ESSet.remove e2_cl exst_cls in
		  loop repr_map' exst_cls' pointsto_map' spatials'
		with Not_found ->
		  let repr_map' = EMap.add e2 target repr_map in
		  loop repr_map' exst_cls pointsto_map' spatials'
	else raise NoFrameExists
  in
  loop repr_map exst_cls pointsto_map spatials

let verify_right_neqs repr_map exst_cls left_neqs right_pure_formulas =
  (*print "verify_right_neqs with@.";
  print "repr_map = ";
  EMap.iter (fun e1 e2 -> Format.fprintf !Config.formatter " %a|->%a;" pp_exp e1 pp_exp e2) repr_map;
  print "@.exst_cls =";
  ESSet.iter (fun cl -> Format.fprintf !Config.formatter "  {"; ESet.iter (Format.fprintf !Config.formatter " %a" pp_exp) cl; Format.fprintf !Config.formatter " }") exst_cls; 
  print "@.";*)
  let repr_map = ESSet.fold (fun cl repr_map ->
      let repr = ESet.choose cl in
	  ESet.fold (fun e repr_map -> EMap.add e repr repr_map) cl repr_map
	) exst_cls repr_map in
  List.iter (function
    | PF_eq _ -> ()
	| PF_neq (e1,e2) ->
	  let repr1 = try EMap.find e1 repr_map with Not_found -> e1 in
	  let repr2 = try EMap.find e2 repr_map with Not_found -> e2 in
	  if repr1 = repr2 then raise NoFrameExists
    ) right_pure_formulas




let frame_of_asf_list sfs = Some (ESH_base ([],sfs))

let get_frame_base (pfs,sfs) (pfs2,sfs2) =
  try
  
    let repr_map = compute_repr_map pfs in
	(*let pointsto_map = compute_pointsto_map repr_map sfs in
	let () = verify_precise pointsto_map in*)
	let repr_map, pointsto_map = process_spatial_formulas repr_map sfs in
	let neqs = (neqs_from_pure repr_map pfs)@(neqs_from_spatial pointsto_map) in
	
	let repr_map, exst_cls = update_repr_map repr_map pfs2 in
	let repr_map, exst_cls, frame_map = 
	  compute_frame_map repr_map exst_cls pointsto_map sfs2 in
	let () = verify_right_neqs repr_map exst_cls neqs pfs2 in
	(* TODO: verify that second formula is precise alone *)
	
	frame_of_asf_list (List.map (fun (e1,e2) -> SF_pointsto (e1,e2)) (EMap.bindings frame_map))
	
  with 
    | ImpliesFalse -> frame_of_asf_list [SF_false]
	| NoFrameExists -> None

	(*
    let repr_map = compute_repr_map pfs in
	print "repr_map done@.";
	(*let pointsto_map = compute_pointsto_map repr_map sfs in
	let () = verify_precise pointsto_map in*)
	let repr_map, pointsto_map = process_spatial_formulas repr_map sfs in
	print "process_spatial_formulas done@.";
	let neqs = (neqs_from_pure repr_map pfs)@(neqs_from_spatial pointsto_map) in
	print "neqs_from done@.";
	
	let repr_map, exst_cls = update_repr_map repr_map pfs2 in
	print "update_repr_map done@.";
	let repr_map, exst_cls, frame_map = 
	  compute_frame_map repr_map exst_cls pointsto_map sfs2 in
	print "compute_frame_map done@.";
	let () = verify_right_neqs repr_map exst_cls neqs pfs2 in
	print "verify_right_neqs done@.";
	(* verify that second formula is precise alone? *)
	*)
	
let print_exn esh1 esh2 = Format.fprintf !Config.formatter "Error finding frame for %a@." pp_frame (esh1, esh2)

let rec get_frame esh esh2 = match esh, esh2 with
  | ESH_base sh, ESH_base sh2 -> 
  (try 
	get_frame_base sh sh2
  with e -> print_exn esh esh2; raise e
  )
  | ESH_ifthenelse(c, esht, eshf), _ -> 
	let ft = get_frame (esh_star (esh_of_pure c) esht) esh2 in
	let ff = get_frame (esh_star (esh_of_pure (pure_neg c)) eshf) esh2 in
	(match ft, ff with
		Some ft, Some ff -> Some(ESH_ifthenelse(c, ft, ff))
		|_-> None)
  | ESH_base _, ESH_ifthenelse(c, esh2t, esh2f) ->
	let ft = get_frame (esh_star esh (esh_of_pure c)) esh2t in
	let ff = get_frame (esh_star esh (esh_of_pure (pure_neg c))) esh2f in
	(match ft, ff with
		Some ft, Some ff -> Some(ESH_ifthenelse(c, ft, ff))	
		|_-> None)



let is_emp_sh (pi,sigma) = sigma=[]

let rec is_emp_esh = function
  | ESH_base(sh) -> is_emp_sh sh
  | ESH_ifthenelse(_,esh1,esh2) -> (is_emp_esh esh1) && (is_emp_esh esh2)

let pp_frame f = function
  | None -> Format.fprintf f "None"
  | Some(esh) -> pp_esh f esh

let entails esh esh2 = 
  if !Config.verbose1 
  then Format.fprintf !Config.formatter "Checking Entailment:@.%a@." pp_entailment (esh,esh2); 
  let frame = get_frame esh esh2 in
  let res = match frame with
    | Some(esh)-> (esh = esh_false) || (is_emp_esh esh)
    | _ -> false 
  in
  if !Config.verbose1 
  then
    if res then Format.fprintf !Config.formatter "Entailment holds@." 
    else Format.fprintf !Config.formatter "Entailment does not hold@.Infered frame: %a@." pp_frame frame;
  res
