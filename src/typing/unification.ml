(********************)
(* TYPE DEFINITIONS *)
(********************)

(* Typing constraint *)
type ty_cnstr = (Type.ty * Type.ty)
(* Dirt constraint *)
type dirt_cnstr = (Type.dirt * Type.dirt)

(* A constraint set *)
type t = {
  types : ty_cnstr list;
  dirts : dirt_cnstr list
}

(******************)
(* HELPER METHODS *)
(******************)

(* Add a type constraint to a constraint set *)
let add_type ty cnstr = {
  types = ty :: cnstr.types;
  dirts = cnstr.dirts
}

(* Add a drt constraint to a constraint set *)
let add_dirt drt cnstr = {
  types = cnstr.types;
  dirts = drt :: cnstr.dirts
}

let combine_types types cnstr = List.fold_right add_type types cnstr

let combine_dirts types cnstr = List.fold_right add_dirt types cnstr

let subst_ty_cnstr sbst (ty1, ty2) = (Type.subst_ty sbst ty1, Type.subst_ty sbst ty2)

let subst_dirt_cnstr sbst (drt1, drt2) = (Type.subst_dirt sbst drt1, Type.subst_dirt sbst drt2)

(*************************)
(* CONSTRAINT OPERATIONS *)
(*************************)

(* The empty constraint set *)
let empty = {
  types = [];
  dirts = []
}

(* Add a type constraint to a constraint set *)
let add_ty_constraint ty1 ty2 cnstr = add_type (ty1, ty2) cnstr

let add_dirt_constraint drt1 drt2 cnstr = add_dirt (drt1, drt2) cnstr

let add_dirty_constraint (ty1, drt1) (ty2, drt2) cnstr = add_ty_constraint ty1 ty2 (add_dirt_constraint drt1 drt2 cnstr)


(* Combine two constraint sets to a single set *)
let union c1 c2 =
  let c' = combine_dirts c1.dirts c2 in
  let c'' = combine_types c1.types c' in
  c''

(* Combine mutliple constraint sets to a single set *)
let union_list c_list =
  List.fold_right union c_list empty

(* Unify the constraints to find a solution *)
let unify cnstr = cnstr

(* Perform a substitution *)
let subst sbst constraints =
  {types=List.map (subst_ty_cnstr sbst) constraints.types; dirts=List.map (subst_dirt_cnstr sbst) constraints.dirts }

let list_union = function
  | [] -> empty
  | [constraints] -> constraints
  | constraints :: constraints_lst -> List.fold_right union constraints_lst constraints

(***********************)
(* PRINTING OPERATIONS *)
(***********************)

(* Print constraints *)
let print constraints ppf =
  Print.sequence "," (fun (x, y) ppf -> Format.fprintf ppf "(%t = %t)" (Type.print_ty x) (Type.print_ty y)) constraints.types ppf;
  Format.pp_print_string ppf " ; ";
  Print.sequence "," (fun (x, y) ppf -> Format.fprintf ppf "(%t = %t)" (Type.print_dirt x) (Type.print_dirt y)) constraints.dirts ppf
