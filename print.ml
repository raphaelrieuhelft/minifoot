open Format
open Misc
open Defs

let pp_string f s = fprintf f "%s" s

let rec pp_listsep pp s1 s2 f = function
  | [] -> fprintf f "%s" s2
  | [x] -> fprintf f "%a" pp x
  | x::l -> fprintf f "%a%s %a" pp x s1 (pp_listsep pp s1 s2) l

let rec pp_seq pp f = function
  | [] -> ()
  | [x] -> fprintf f "%a" pp x
  | x::l -> fprintf f "%a,%a" pp x (pp_seq pp) l

let rec pp_exp f = function
  | EXP_null -> pp_string f "NULL"
  | EXP_ident(id) -> pp_ident f id

let pp_atomic_pure_formula f = function
  | PF_eq (e1,e2) -> fprintf f "%a==%a" pp_exp e1 pp_exp e2
  | PF_neq (e1,e2) -> fprintf f "%a!=%a" pp_exp e1 pp_exp e2

let pp_atomic_spatial_formula f = function
  | SF_false -> pp_string f "false"
  | SF_pointsto(e1,e2) -> fprintf f "%a|->%a" pp_exp e1 pp_exp e2

let pp_pure_formula = pp_listsep pp_atomic_pure_formula " *" ""
let pp_spatial_formula = pp_listsep pp_atomic_spatial_formula " *" "emp"

let pp_sh f (pi,sigma) = match (pi,sigma) with
  | ([],[]) -> fprintf f "emp"
  | (_::_,[]) -> pp_pure_formula f pi
  | ([],_::_) -> pp_spatial_formula f sigma
  | _ -> fprintf f "%a * %a" pp_pure_formula pi pp_spatial_formula sigma

let rec pp_esh f = function
  | ESH_base(sh) -> pp_sh f sh
  | ESH_ifthenelse(cond,esh1,esh2) -> 
      fprintf f "if %a@ then %a@ else %a"

	pp_atomic_pure_formula cond pp_esh esh1 pp_esh esh2

let pp_subst f subst = 
  let pp f (x,e) = fprintf f "%a->%a" pp_ident x pp_exp e in
  fprintf f "{@[<hv>%a@]}" (pp_listsep pp "," "") subst

let pp_atomic_symbexec_statement f = function
  | ASI_inhale(esh) -> fprintf f "inhale(%a);" pp_esh esh
  | ASI_exhale(esh) -> fprintf f "exhale(%a);" pp_esh esh
  | ASI_rename(subst) -> fprintf f "rename(%a);" pp_subst subst

let rec pp_symbexec_statement f = function
  | SI_skip -> fprintf f "skip"
  | SI_atomic(c,SI_skip) -> pp_atomic_symbexec_statement f c
  | SI_atomic(c,cseq) -> fprintf f "%a@.%a" pp_atomic_symbexec_statement c pp_symbexec_statement cseq
  | SI_branch(c1,c2) -> fprintf f "branch@[<hv>{@[<hov 2>%a@]@ }@ {@ @[<hov 2>%a@]}@]" pp_symbexec_statement c1 pp_symbexec_statement c2

let pp_entailment f (esh1,esh2) =
  fprintf f "@[<hv>@[<hov 2>%a@]@ |-@ @[<hov 2>%a@]@]" pp_esh esh1 pp_esh esh2

let pp_frame f (esh1,esh2) =
  fprintf f "@[<hv>@[<hov 2>%a@]@ |-@ ?? *@ @[<hov 2>%a@]@]" pp_esh esh1 pp_esh esh2

let pp_pure_entailment f (pi1,pi2) =
  fprintf f "@[<hv>@[<hov 2>%a@]@ |-@ @[<hov 2>%a@]@]"
    pp_pure_formula pi1 pp_pure_formula pi2

let pp_spatial_entailment f (sigma1,sigma2) =
  fprintf f "@[<hv>@[<hov 2>%a@]@ |-@ @[<hov 2>%a@]@]"
    pp_spatial_formula sigma1 pp_spatial_formula sigma2

let pp_vc f vc =
  fprintf f "VERIFICATION CONDITION %s@.[%a]@.%a@.[%a]@."
    vc.vc_info pp_esh vc.vc_pre pp_symbexec_statement vc.vc_symb_stmt pp_esh vc.vc_post
 
let rec pp_atomic_command f = function
  | AC_new(id) -> fprintf f "%a = new();" pp_ident id
  | AC_dispose(e) -> fprintf f "dispose(%a);" pp_exp e
  | AC_assign(id,e) -> fprintf f "%a = %a;" pp_ident id pp_exp e
  | AC_lookup(id,e) -> fprintf f "%a = %a->tl;" pp_ident id pp_exp e
  | AC_update(e1,e2) -> fprintf f "%a->tl = %a;" pp_exp e1 pp_exp e2
