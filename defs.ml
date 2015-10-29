(** {1} Formulas *)

(** identifiers *)
type ident = Misc.ident

(** expression *)
type exp =
  | EXP_null
  | EXP_ident of ident

(** pure formulas *)
type atomic_pure_formula = 
  | PF_eq of exp * exp
  | PF_neq of exp * exp

(** spatial formulas *)
type atomic_spatial_formula =
  | SF_false
  | SF_pointsto of exp * exp

(** symbolic heaps *)
type symb_heap = atomic_pure_formula list * atomic_spatial_formula list

(** extended symbolic heaps *)
type ext_symb_heap =
  | ESH_base of symb_heap
  | ESH_ifthenelse of atomic_pure_formula * ext_symb_heap * ext_symb_heap

(** substitutions *)
type substitution = (ident * exp) list  (* [x1->E1,..,xn->En] in parallel *)


(** {1} Programs *)

(** function identifiers *)
type func_name = string

(** atomic commands *)
type atomic_command = 
  | AC_new of ident                  (* x = new() *)
  | AC_dispose of exp                (* dispose(E) *)
  | AC_assign of ident * exp         (* x = E *)
  | AC_lookup of ident * exp         (* x = E->tl; *)
  | AC_update of exp * exp           (* E->tl =  E' *)

(** boolean conditions *)
type condition =  atomic_pure_formula

(** commands *)
type command = {
  command_desc : command_desc;
  command_loc : Location.t;
}

and command_desc = 
  | CO_atom of atomic_command
  | CO_block of command list
  | CO_if of condition * command * command
  | CO_while of condition * ext_symb_heap * command
  | CO_parallelCalls of (func_name * exp list) list

(** function declaration *)
type function_declaration = {
  fd_name : string;
  fd_params : ident list;
  fd_precondition : ext_symb_heap;
  fd_locals : ident list;
  fd_body : command;
  fd_postcondition : ext_symb_heap;
  fd_loc1 : Location.t;
  fd_loc2 : Location.t;
}


(** {1} Symbolic Instructions and VC *)

type atom_symb_inst = 
  | ASI_inhale of ext_symb_heap       (** inhale(A)(A*B)=B  *) 
  | ASI_exhale of ext_symb_heap       (** exhale(A)(B)=A*B  *) 
  | ASI_rename of substitution        (** rename(s)(A)=A[s] *)

type symb_inst = 
  | SI_skip
  | SI_atomic of atom_symb_inst * symb_inst
  | SI_branch of symb_inst * symb_inst

type verification_condition = {
  vc_pre : ext_symb_heap;
  vc_symb_stmt : symb_inst;
  vc_post: ext_symb_heap;
  vc_info : string; (** some message to be shown when reporing an error with this VC *)
}

