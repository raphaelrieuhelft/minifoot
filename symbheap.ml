open Misc
open Defs
open Error


(** {1} False and empty *)
let sh_false = [],[SF_false]
let esh_false = ESH_base(sh_false)
let sh_emp = [],[]
let esh_emp = ESH_base(sh_emp)

(** {1} Set of vars of something *)
let vars_of_exp = function
  | EXP_ident(i) -> IdSet.singleton i
  | EXP_null -> IdSet.empty

let vars_of_atomic_pure = function
  | PF_eq(e1,e2) | PF_neq(e1,e2) -> IdSet.union (vars_of_exp e1) (vars_of_exp e2)

let vars_of_atomic_spatial = function
  | SF_pointsto(e1,e2) ->
      IdSet.union (vars_of_exp e1) (vars_of_exp e2)
  | SF_false -> IdSet.empty
  
let vars_of_pure pi = 
  List.fold_left IdSet.union IdSet.empty (List.map vars_of_atomic_pure pi)

let vars_of_spatial sigma = 
  List.fold_left IdSet.union IdSet.empty (List.map vars_of_atomic_spatial sigma)

let vars_of_sh (pi,sigma) = 
  IdSet.union (vars_of_pure pi) (vars_of_spatial sigma)

let rec vars_of_esh = function
  | ESH_base(sh) -> vars_of_sh sh
  | ESH_ifthenelse(cond,esh1,esh2) -> 
    IdSet.union (vars_of_atomic_pure cond) 
      (IdSet.union (vars_of_esh esh1) (vars_of_esh esh2))

let non_ex_vars_of_esh esh = IdSet.filter (fun id->not (is_existential id)) (vars_of_esh esh)

let vars_of_atomic_command = function
  | AC_new(x) -> IdSet.singleton x
  | AC_dispose(e) -> vars_of_exp e
  | AC_lookup(x,e) | AC_assign(x,e) -> IdSet.union (IdSet.singleton x) (vars_of_exp e)
  | AC_update(e1,e2) -> IdSet.union (vars_of_exp e1) (vars_of_exp e2)

let vars_of_condition = function
  | PF_eq(e1,e2) | PF_neq(e1,e2) -> IdSet.union (vars_of_exp e1) (vars_of_exp e2)

(** {1} Substitutions *)

let exp_rename subst = function
  | EXP_null -> EXP_null
  | EXP_ident(id) as e-> try List.assoc id subst with Not_found -> e

let atom_pure_rename subst = function
  | PF_eq(e1,e2) -> PF_eq(exp_rename subst e1,exp_rename subst e2)
  | PF_neq(e1,e2) -> PF_neq(exp_rename subst e1,exp_rename subst e2)

let cond_rename = atom_pure_rename

let atom_spatial_rename subst = function
  | SF_false -> SF_false
  | SF_pointsto(e1,e2) -> SF_pointsto(exp_rename subst e1,exp_rename subst e2)

let pure_rename subst sigma = List.map (atom_pure_rename subst) sigma

let spatial_rename subst sigma = List.map (atom_spatial_rename subst) sigma

let sh_rename subst (pi,sigma) = (pure_rename subst pi,spatial_rename subst sigma)

let rec esh_rename subst = function
  | ESH_base(sh) -> ESH_base(sh_rename subst sh)
  | ESH_ifthenelse(cond,esh1,esh2) ->
    ESH_ifthenelse(cond_rename subst cond,esh_rename subst esh1,esh_rename subst esh2)

(** {1} Misc *)

let rec non_ex_vars_of_esh esh = 
  IdSet.filter (fun x-> not (is_existential x)) (vars_of_esh esh)

let sh_star (pi1,sigma1) (pi2,sigma2) = (pi1@pi2,sigma1@sigma2)

let rec esh_star esh1 esh2 = match (esh1,esh2) with
  | ESH_base(sh1),ESH_base(sh2) -> ESH_base(sh_star sh1 sh2)
  | ESH_ifthenelse(cond,esh1,esh2),esh3 ->
    ESH_ifthenelse(cond,esh_star esh1 esh3,esh_star esh2 esh3)
  | esh1,ESH_ifthenelse(cond,esh2,esh3) ->
    ESH_ifthenelse(cond,esh_star esh1 esh2,esh_star esh1 esh3)

let esh_star_list l = List.fold_left esh_star esh_emp l

let pure_neg = function
  | PF_eq(e,f) -> PF_neq(e,f)
  | PF_neq(e,f)-> PF_eq(e,f)


