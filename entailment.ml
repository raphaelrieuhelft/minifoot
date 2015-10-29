open Defs
open Print
open Symbheap
open Misc
open Error

type esh = ext_symb_heap
type frame = esh option


let get_frame esh esh2 = 
  (* A COMPLETER *)
  None

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
