(* Typing constraint *)
type ty_cnstr = (Type.ty * Type.ty)
(* Dirt constraint *)
type dirt_cnstr = int

(* A constraint set *)
type t = {
  types : ty_cnstr list;
  dirt : dirt_cnstr list
}

(* The empty constraint set *)
let empty = {
  types = [];
  dirt = []
}

(* Add a type constraint to a constraint set *)
let add_type ty cnstr = {
  types = ty :: cnstr.types;
  dirt = cnstr.dirt
}

(* Add a type constraint to a constraint set *)
let add_ty_constraint ty1 ty2 cnstr = add_type (ty1, ty2) cnstr

(* Add a drt constraint to a constraint set *)
let add_dirt drt cnstr = {
  types = cnstr.types;
  dirt = drt :: cnstr.dirt
}

let combine_types types cnstr = List.fold_right add_type types cnstr

let combine_dirts types cnstr = List.fold_right add_dirt types cnstr

(* Combine two constraint sets to a single set *)
let union c1 c2 =
  let c' = combine_dirts c1.dirt c2 in
  let c'' = combine_types c1.types c2 in
  c''

(* Combine mutliple constraint sets to a single set *)
let union_list c_list =
  List.fold_right union c_list empty

(* Unify the constraints to find a solution *)
let unify cnstr = cnstr

(* Print constraints *)
let print constraints ppf =
  Print.sequence "," (fun (x, y) ppf -> Format.fprintf ppf "%t = %t" (Type.print_ty x) (Type.print_ty y)) constraints.types ppf
