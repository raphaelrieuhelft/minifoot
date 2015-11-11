open Defs
open Print
open Symbheap
open Misc
open Error

type esh = ext_symb_heap
type frame = esh option


exception ImpliesFalse
exception NoFrameExists
exception ImpreciseFormula

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

let add_if_absent e repr_map =
  if EMap.mem e repr_map then repr_map
  else EMap.add e e repr_map

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
try
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
with Not_found -> assert false

let neqs_from_pure repr_map pure_formulas =
try
  let repr_map, neqs = List.fold_left (fun (repr_map, neqs) -> function
    | PF_eq _ -> repr_map, neqs
	| PF_neq (e1,e2) ->
	  let repr_map = add_if_absent e1 (add_if_absent e2 repr_map) in
	  let repr1 = EMap.find e1 repr_map in
	  let repr2 = EMap.find e2 repr_map in
	  if repr1 = repr2 then raise ImpliesFalse
	  else repr_map, (repr1,repr2)::neqs
	) (repr_map, []) pure_formulas
  in repr_map, neqs
with Not_found -> assert false

let rec list_remove_once x = function
  | [] -> []
  | hd::tl when hd = x -> tl
  | hd::tl -> hd::(list_remove_once x tl)

let process_spatial_formulas repr_map spatial_formulas =
try
  let pointsto_couples = List.map (function 
    | SF_false -> raise ImpliesFalse
	| SF_pointsto (e1,e2) -> (e1,e2)
	) spatial_formulas in
  let repr_map = List.fold_left (fun repr_map (e1,e2) ->
      add_if_absent e1 (add_if_absent e2 repr_map)
	) repr_map pointsto_couples in
  let repr_map = add_if_absent EXP_null repr_map in
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
with Not_found -> assert false

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


let process_symb_heap ((pure_formulas, spatial_formulas) as sh) =
  try
    let repr_map = compute_repr_map pure_formulas in
	let repr_map, pointsto_map = process_spatial_formulas repr_map spatial_formulas in
	let repr_map, neqs = neqs_from_pure repr_map pure_formulas in
	let neqs = neqs@(neqs_from_spatial pointsto_map) in
	repr_map, pointsto_map, neqs
  with 
    | ImpreciseFormula -> raise (Imprecise_formula sh)
    | e when e <> ImpliesFalse -> (Format.fprintf !Config.formatter "Error in process_symb_heap on %a@." pp_sh sh; raise e)

	
	
	
	
(* Computes trans_map which associates, to every right representative,
Some of a left representative if they have to be equal, None if there is no such left representative. There cannot be two such left representatives because that would force them to be equal, which cannot be deduced from the left symbolic heap *)
let compute_trans_map left_repr_map right_repr_map =
  let translate e rrepr trans_map = (* to fold on right_repr_map *)
    if EMap.mem e left_repr_map then
	  let lrepr = EMap.find e left_repr_map in
	  if EMap.mem rrepr trans_map then
	    match EMap.find rrepr trans_map with
		  | None -> EMap.add rrepr (Some lrepr) trans_map
		  | Some tr ->
		    if tr = lrepr then trans_map
			else raise NoFrameExists (* equality of distinct left representatives cannot be proven *)
	  else
	    EMap.add rrepr (Some lrepr) trans_map
	else if exp_is_existential e then
	  if EMap.mem rrepr trans_map then trans_map
	  else EMap.add rrepr None trans_map
	else raise NoFrameExists (* non existential ident appearing in the right symbolic heap but not in the left one (cannot be EXP_null because left_repr_map always contains it) *)
  in
  let trans_map = EMap.fold translate right_repr_map EMap.empty in
  trans_map

let inhale_right_pointsto_map trans_map left_pointsto_map right_pointsto_map =
try
  let inhalable trans_map rrepr _ = match EMap.find rrepr trans_map with
    Some _ -> true | None -> false in
  let inhale rrepr1 rrepr2 (trans_map, left_pointsto_map, right_pointsto_map) =
    let lrepr1 = match EMap.find rrepr1 trans_map with 
	  Some lrepr1 -> lrepr1 | None -> assert false in
	if EMap.mem lrepr1 left_pointsto_map then
	  let ltarget = EMap.find lrepr1 left_pointsto_map in
	  let next_left_pointsto_map = EMap.remove lrepr1 left_pointsto_map in
	  let next_right_pointsto_map = EMap.remove rrepr1 right_pointsto_map in
	  match EMap.find rrepr2 trans_map with
	    | None ->
		  (EMap.add rrepr2 (Some ltarget) trans_map, next_left_pointsto_map, next_right_pointsto_map)
		| Some lrepr2 ->
		  if lrepr2 = ltarget then
		    (trans_map, next_left_pointsto_map, next_right_pointsto_map)
		  else raise NoFrameExists
	else raise NoFrameExists (* cannot prove rrepr1|-> *)
  in
  let rec loop (trans_map, left_pointsto_map, right_pointsto_map) =
    if EMap.is_empty right_pointsto_map then
	  trans_map, left_pointsto_map
	else
	  let inhalables = EMap.filter (inhalable trans_map) right_pointsto_map in
	  let (rrepr1,rrepr2) = try EMap.choose inhalables 
	    with Not_found -> raise NoFrameExists in
	  loop (inhale rrepr1 rrepr2 (trans_map, left_pointsto_map, right_pointsto_map))
  in
  let trans_map, frame_map = loop (trans_map, left_pointsto_map, right_pointsto_map) in
  trans_map, frame_map
with Not_found -> assert false

let verify_right_neqs trans_map left_neqs right_neqs =
try
  let rec mem_pair (x,y) = function
    | [] -> false
	| (a,b)::_ when (a=x&&b=y) || (a=y&&b=x) -> true
	| _::tl -> mem_pair (x,y) tl
  in
  let verify (rrepr1,rrepr2) =
    match EMap.find rrepr1 trans_map, EMap.find rrepr2 trans_map with
	  | Some lrepr1, Some lrepr2 ->
	    if not (mem_pair (lrepr1,lrepr2) left_neqs) then raise NoFrameExists
	  | tr1, tr2 -> if tr1 = tr2 then raise NoFrameExists
  in
  List.iter verify right_neqs
with Not_found -> assert false



let get_frame_base sh sh2 =
  try
	let repr_map, pointsto_map, neqs = process_symb_heap sh in
	let repr_map2, pointsto_map2, neqs2 = 
	  try process_symb_heap sh2 
	  with ImpliesFalse -> raise NoFrameExists
	in
	let trans_map = compute_trans_map repr_map repr_map2 in
	let trans_map, frame_map = inhale_right_pointsto_map trans_map pointsto_map pointsto_map2 in
	let () = verify_right_neqs trans_map neqs neqs2 in
	let frame_spatials = List.map (fun (e1,e2) -> SF_pointsto (e1,e2)) (EMap.bindings frame_map) in
	(* the frame consists of the computed spatial formulas, but also all pure formulas of sh *)
	Some (ESH_base ((fst sh), frame_spatials))
  with 
    | ImpliesFalse -> 
	  (* This can only be about sh (or it would have been caught above). The frame to return is then false, but we still process sh2 to check that it is precise. *)
	  (try let _ = process_symb_heap sh2 in Some esh_false
	  with ImpliesFalse -> Some esh_false)
	| NoFrameExists -> None
	| Not_found -> 
	  (Format.fprintf !Config.formatter "Not_found in get_frame_base@."; 
	  assert false)


	


let build_if c ft ff =
	match ft, ff with
		| (Some esht, Some eshf) when esht=eshf -> ft
		| Some esht, Some eshf when esht = esh_false -> 
		  Some (esh_star eshf (esh_of_pure (pure_neg c)))
		| Some esht, Some eshf when eshf = esh_false -> 
		  Some (esh_star esht (esh_of_pure c))
		| Some esht, Some eshf -> Some(ESH_ifthenelse(c, esht, eshf))
		| _ -> None

		
		
let rec get_frame esh esh2 = 
try match esh, esh2 with
  | ESH_base sh, ESH_base sh2 -> get_frame_base sh sh2
  | ESH_ifthenelse(c, esht, eshf), _ ->
	let ft = get_frame (esh_star (esh_of_pure c) esht) esh2 in
	let ff = get_frame (esh_star (esh_of_pure (pure_neg c)) eshf) esh2 in
	build_if c ft ff
  | ESH_base _, ESH_ifthenelse(c, esh2t, esh2f) ->
	let ft = get_frame (esh_star esh (esh_of_pure c)) esh2t in
	let ff = get_frame (esh_star esh (esh_of_pure (pure_neg c))) esh2f in
	build_if c ft ff
with 
  | Imprecise_formula sh ->
	Format.fprintf !Config.formatter "Imprecise formula %a.@.The corresponding call to get_frame returns that no frame exists so that execution is not aborted; therefore following messages may be inaccurate.@." pp_sh sh; 
	None
  | e -> Format.fprintf !Config.formatter "Error finding frame for %a@." pp_frame (esh, esh2); raise e


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
