(********************)
(* TYPE DEFINITIONS *)
(********************)

(* Typing constraint *)
type ty_cnstr = (Type.ty * Type.ty * Location.t)
(* Dirt constraint *)
type dirt_cnstr = (Type.dirt * Type.dirt * Location.t)

(* A constraint set *)
type t = {
  types : ty_cnstr list;
  dirts : dirt_cnstr list
}

(* represents a context and contains all free variables that occur *)
type context = (Untyped.variable, Type.ty) Common.assoc

(**********************)
(* SIMPLY CONSTRAINTS *)
(**********************)

let print_types str constraints =
  Print.sequence "," (fun (x, y, _) ppf -> Format.fprintf ppf "(%t = %t)" (Type.print_ty x) (Type.print_ty y)) constraints Format.std_formatter;
  Format.pp_print_string Format.std_formatter str


(* Add a dirt to a constraint set *)
let add_dirt_only drt cnstr = {
  types = cnstr.types;
  dirts = drt :: cnstr.dirts
}

(* Add a type to a constraint set *)
let add_ty_only ty cnstr = {
  types = ty :: cnstr.types;
  dirts = cnstr.dirts
}

let rec contains x = function
  | [] -> false
  | x' :: lst -> if (x = x') then true else contains x lst

let rec remove_duplicates occ cnstr =
  begin match occ with
    | [] -> []
    | item :: tail when contains item cnstr -> remove_duplicates tail cnstr
    | item :: tail -> item :: (remove_duplicates tail cnstr)
  end

(* Check if two dirts are the same (with no operations) *)
let dirt_var_equal drt1 drt2 =
  begin match drt1.Type.ops, drt2.Type.ops with
    | [], [] -> drt1.Type.rest = drt2.Type.rest
    | _ -> false
  end

(* Check if a dirt only contains a var and no operations *)
let is_drt_var drt =
  begin match drt.Type.ops with
    | [] -> true
    | _ -> false
  end

let fix_type ty =
  begin match ty with
    | Type.Apply ("unit", ([], _)) -> Type.Tuple []
    | Type.Apply ("bool", ([], _)) -> Type.Prim Type.BoolTy
    | Type.Apply ("int", ([], _)) -> Type.Prim Type.IntTy
    | Type.Apply ("string", ([], _)) -> Type.Prim Type.StringTy
    | Type.Apply ("float", ([], _)) -> Type.Prim Type.FloatTy
    | _ -> ty
  end

(* FIX THIS: Type.Apply ("unit", ([], _)) *)
let prim_equal t1 t2 =
  let t1 = fix_type t1 in
  let t2 = fix_type t2 in
  begin match t1, t2 with
    | Type.Prim Type.BoolTy, Type.Prim Type.BoolTy -> true
    | Type.Prim Type.IntTy, Type.Prim Type.IntTy -> true
    | Type.Prim Type.FloatTy, Type.Prim Type.FloatTy -> true
    | Type.Prim Type.StringTy, Type.Prim Type.StringTy -> true
    | Type.Tuple [], Type.Tuple [] -> true
    (* | Type.UnitTy, Type.UniTy -> true *)
    | Type.Prim Type.UniTy, Type.Prim Type.UniTy -> true
    | _ -> false
  end

(* Find matching dirts *)
let rec find_other_dirt drt cnstr =
  begin match cnstr with
    | [] -> None, []
    | (drt1, drt2, loc) :: cnstr when dirt_var_equal drt drt1 && not (is_drt_var drt2) ->
      Some drt2, cnstr
    | (drt2, drt1, loc) :: cnstr when dirt_var_equal drt drt1 && not (is_drt_var drt2)->
      Some drt2, cnstr
    | (drt1, drt2, loc) :: cnstr ->
      let opt, cnstr = find_other_dirt drt cnstr in
      opt, (drt1, drt2, loc) :: cnstr
  end

(*
  Unify two dirts of the form:
    d1 = {ops... ; d2}
    d1 = {ops... ; d3}
  into:
    d2 = {ops... ; d4}
    d3 = {ops... ; d4}
    d1 = {ops... ; d4}
*)
let unify_single_dirt loc drt2 drt3 =
  let out = Type.fresh_dirt () in
  let out = Type.add_ops drt2.Type.ops out in
  let out = Type.add_ops drt3.Type.ops out in
  let out2_l = Type.make_dirt [] drt2.Type.rest in
  let out3_l = Type.make_dirt [] drt3.Type.rest in
  let out2_r = Type.make_dirt drt3.Type.ops out.Type.rest in
  let out3_r = Type.make_dirt drt2.Type.ops out.Type.rest in
  out, (out2_l, out2_r, loc), (out3_l, out3_r, loc)

(* Add a dirt to a constraint set and perform some unification *)
let rec simplify_dirt (drt1, drt2, loc) cnstr =
  begin match drt1, drt2 with
    | (drt1, drt2) when dirt_var_equal drt1 drt2 ->
      cnstr
    | (drt1, drt2) when is_drt_var drt1 && is_drt_var drt2 ->
      add_dirt_only (drt1, drt2, loc) cnstr
    | (drt1, drt2) when is_drt_var drt1 ->
      let drt3_option, dirts = find_other_dirt drt1 cnstr.dirts in
      let cnstr = {cnstr with dirts=dirts} in
      begin match drt3_option with
        | None -> add_dirt_only (drt1, drt2, loc) cnstr
        | Some drt3 ->
          let new1, new2, new3 = unify_single_dirt loc drt2 drt3 in
          let cnstr = add_dirt_only (drt1, new1, loc) cnstr in
          let cnstr = simplify_dirt new2 cnstr in
          let cnstr = simplify_dirt new3 cnstr in
          (* let cnstr = expand_dirts drt1 drt2 loc cnstr in *)
          cnstr
      end
    | (drt2, drt1) when is_drt_var drt1 ->
      let drt3_option, dirts = find_other_dirt drt1 cnstr.dirts in
      let cnstr = {cnstr with dirts=dirts} in
      begin match drt3_option with
        | None -> add_dirt_only (drt1, drt2, loc) cnstr
        | Some drt3 ->
          let new1, new2, new3 = unify_single_dirt loc drt2 drt3 in
          let cnstr = add_dirt_only (drt1, new1, loc) cnstr in
          let cnstr = simplify_dirt new2 cnstr in
          let cnstr = simplify_dirt new3 cnstr in
          (* let cnstr = expand_dirts drt1 drt2 loc cnstr in *)
          cnstr
      end
    | (drt1, drt2) ->
      let new1, new2, new3 = unify_single_dirt loc drt1 drt2 in
      let cnstr = simplify_dirt new2 cnstr in
      let cnstr = simplify_dirt new3 cnstr in
      cnstr
  end

(* Add a drt constraint to a constraint set *)
and add_dirt drt cnstr = simplify_dirt drt cnstr

let rec find_occurences ty cnstr =
  begin match cnstr with
    | [] -> []
    | (ty1, ty2, loc) :: cnstr when ty = ty1 ->
      (ty1, ty2, loc) :: (find_occurences ty cnstr)
    | (ty1, ty2, loc) :: cnstr when ty = ty2 ->
      (ty1, ty2, loc) :: (find_occurences ty cnstr)
    | _ :: cnstr -> find_occurences ty cnstr
  end

let rec replace_type ty_replace ty_new occ =
  begin match occ with
    | [] -> []
    | (ty1, ty2, loc) :: occ when ty_replace = ty1 ->
      (ty_new, ty2, loc) :: (replace_type ty_replace ty_new occ)
    | (ty1, ty2, loc) :: occ when ty_replace = ty2 ->
      (ty1, ty_new, loc) :: (replace_type ty_replace ty_new occ)
    | _ :: occ -> replace_type ty_replace ty_new occ
  end

let rec replace_type_reverse ty_replace ty_new occ =
  begin match occ with
    | [] -> []
    | (ty1, ty2, loc) :: occ when ty_replace = ty1 ->
      (ty_new, ty2, loc) :: (replace_type_reverse ty_replace ty_new occ)
    | (ty1, ty2, loc) :: occ when ty_replace = ty2 ->
      (ty1, ty_new, loc) :: (replace_type_reverse ty_replace ty_new occ)
    | _ :: occ -> replace_type_reverse ty_replace ty_new occ
  end

let remove_duplicate_list l =
  let rec tail_uniq a l =
    match l with
      | [] -> a
      | hd::tl -> tail_uniq (hd::a) (List.filter (fun x -> x  != hd) tl) in
  tail_uniq [] l

(* Add a dirt to a constraint set and perform some unification *)
let rec simplify_type (ty1, ty2, loc) cnstr =
  let rec add_new_types occ cnstr =
    begin match occ with
      | [] -> cnstr
      | item :: tail -> add_new_types tail (add_type item cnstr)
    end
  in
  begin match ty1, ty2 with
    | (ty1, ty2) when ty1 = ty2 ->
      cnstr
    | (Type.TyVar t1, Type.TyVar t2) ->
      let occ1 = find_occurences ty1 cnstr.types in
      let occ2 = find_occurences ty2 cnstr.types in
      let occ1 = replace_type ty1 ty2 occ1 in
      let occ2 = replace_type ty2 ty1 occ2 in
      let occ = remove_duplicate_list (occ1 @ occ2) in
      let occ = remove_duplicates occ cnstr.types in
      let cnstr = add_ty_only (ty1, ty2, loc) cnstr in
      (* let cnstr = add_new_types occ cnstr in *)
      cnstr
    | (Type.TyVar t1, t2) ->
      let occ = find_occurences ty1 cnstr.types in
      let occ = replace_type_reverse ty1 ty2 occ in
      let occ = remove_duplicates occ cnstr.types in
      let cnstr = add_ty_only (ty1, ty2, loc) cnstr in
      let cnstr = add_new_types occ cnstr in
      cnstr
    | (t1, Type.TyVar t2) ->
      let occ = find_occurences ty2 cnstr.types in
      (* print_types " type_end "[ty1, ty2, loc];
      print_types " occ_end " occ;
      print_types " cnstr_end " cnstr.types; *)
      let occ = replace_type_reverse ty2 ty1 occ in
      let occ = remove_duplicates occ cnstr.types in
      let cnstr = add_ty_only (ty1, ty2, loc) cnstr in
      let cnstr = add_new_types occ cnstr in
      cnstr
    | (t1, t2) when prim_equal t1 t2 ->
      cnstr
    | (Type.Arrow (ty1_in, dirty1_out), Type.Arrow (ty2_in, dirty2_out)) ->
      let (ty1_out, drt1) = dirty1_out in
      let (ty2_out, drt2) = dirty2_out in
      let cnstr = simplify_dirt (drt1, drt2, loc) cnstr in
      let cnstr = add_type (ty1_in, ty2_in, loc) cnstr in
      let cnstr = add_type (ty1_out, ty2_out, loc) cnstr in
      cnstr
    | (Type.Handler (dirty1_in, dirty1_out), Type.Handler (dirty2_in, dirty2_out)) ->
      let (ty1_in, drt1_in) = dirty1_in in
      let (ty2_in, drt2_in) = dirty2_in in
      let (ty1_out, drt1_out) = dirty1_out in
      let (ty2_out, drt2_out) = dirty2_out in
      let cnstr = simplify_dirt (drt1_in, drt2_in, loc) cnstr in
      let cnstr = simplify_dirt (drt1_out, drt2_out, loc) cnstr in
      let cnstr = add_type (ty1_in, ty2_in, loc) cnstr in
      let cnstr = add_type (ty1_out, ty2_out, loc) cnstr in
      cnstr
    | _ -> Error.typing ~loc "This expression has type %t but it should have type %t." (Type.print_ty ty1) (Type.print_ty ty2)
  end

(******************)
(* HELPER METHODS *)
(******************)

(* Add a type constraint to a constraint set *)
and add_type (ty1, ty2, loc) cnstr =
  let t1 = fix_type ty1 in
  let t2 = fix_type ty2 in
  let ty = (t1, t2, loc) in
  if (contains ty cnstr.types) then cnstr else (simplify_type ty cnstr)


let combine_types types cnstr = List.fold_right add_type types cnstr

let combine_dirts types cnstr = List.fold_right add_dirt types cnstr

let subst_ty_cnstr sbst (ty1, ty2, loc) = (Type.subst_ty sbst ty1, Type.subst_ty sbst ty2, loc)

let subst_dirt_cnstr sbst (drt1, drt2, loc) = (Type.subst_dirt sbst drt1, Type.subst_dirt sbst drt2, loc)

(*************************)
(* CONSTRAINT OPERATIONS *)
(*************************)

(* The empty constraint set *)
let empty = {
  types = [];
  dirts = []
}

(* Add a type constraint to a constraint set *)
let add_ty_constraint ~loc ty1 ty2 cnstr = add_type (ty1, ty2, loc) cnstr

let add_dirt_constraint ~loc drt1 drt2 cnstr = add_dirt (drt1, drt2, loc) cnstr

let add_dirty_constraint ~loc (ty1, drt1) (ty2, drt2) cnstr = add_ty_constraint ~loc ty1 ty2 (add_dirt_constraint ~loc drt1 drt2 cnstr)


(* Combine two constraint sets to a single set *)
let union c1 c2 =
  let c' = combine_dirts c1.dirts c2 in
  let c'' = combine_types c1.types c' in
  c''

(* Combine mutliple constraint sets to a single set *)
let union_list c_list =
  List.fold_right union c_list empty

(* Perform a substitution *)
let subst sbst constraints =
  {types=List.map (subst_ty_cnstr sbst) constraints.types; dirts=List.map (subst_dirt_cnstr sbst) constraints.dirts }

let list_union = function
  | [] -> empty
  | [constraints] -> constraints
  | constraints :: constraints_lst -> List.fold_right union constraints_lst constraints

(************************)
(* CONSTRAINT SOLUTIONS *)
(************************)

let rec search_constraints_type ty full cnstr exclude =
  begin match cnstr with
    | [] -> ty
    | (ty1, ty2, _) :: cnstr when (ty1 = ty) && (not (contains ty exclude)) ->
      begin match ty2 with
        | Type.Prim _ -> ty2
        | Type.TyVar a -> search_constraints_type ty2 full cnstr (ty :: exclude)
        | _ -> search_constraints_type ty full cnstr exclude
      end
    | (ty2, ty1, _) :: cnstr when (ty1 = ty) && (not (contains ty exclude)) ->
      begin match ty2 with
        | Type.Prim _ -> ty2
        | Type.TyVar a -> search_constraints_type ty2 full cnstr (ty :: exclude)
        | _ -> search_constraints_type ty full cnstr exclude
      end
    | (ty2, ty1, _) :: cnstr -> search_constraints_type ty full cnstr exclude
  end

let rec search_constraints_dirt drt cnstr =
  begin match cnstr with
    | [] -> None
    | (drt1, drt2, loc) :: cnstr when dirt_var_equal drt drt1 && not (is_drt_var drt2) ->
      Some (Type.add_ops drt2.Type.ops drt)
      (* let next = search_constraints_dirt drt2 cnstr in
      begin match next with
        | None -> search_constraints_dirt drt cnstr
        | Some drt -> Some (Type.add_ops drt2.Type.ops drt)
      end *)
    | (drt2, drt1, loc) :: cnstr when dirt_var_equal drt drt1 && not (is_drt_var drt2) ->
      Some (Type.add_ops drt2.Type.ops drt)
      (* let next = search_constraints_dirt drt2 cnstr in
      begin match next with
        | None -> search_constraints_dirt drt cnstr
        | Some drt -> Some (Type.add_ops drt2.Type.ops drt)
      end *)
    | (drt1, drt2, loc) :: cnstr ->
      search_constraints_dirt drt cnstr
  end


(* Unify the constraints to find a solution *)
let unify ctx cnstr =
  (* let dirt_extra, types = unify_types [] [] cnstr.types in *)
  (* let dirts = unify_dirts [] (cnstr.dirts) in *)
  {
    types = cnstr.types;
    dirts = cnstr.dirts
  }

(* find a principal solution for types *)
let rec find_ty_solution ty cnstr =
  let ty = fix_type ty in
  begin match ty with
    | Type.Prim _ -> ty
    | Type.Tuple lst -> Type.Tuple (List.map (fun x -> find_ty_solution x cnstr) lst)
    | Type.Arrow (ty, dirty) -> Type.Arrow (find_ty_solution ty cnstr, find_dirty_solution dirty cnstr)
    | Type.Handler (dirty1, dirty2) -> Type.Handler (find_dirty_solution dirty1 cnstr, find_dirty_solution dirty2 cnstr)
    | Type.TyVar a -> search_constraints_type ty cnstr.types cnstr.types []
    | Type.Apply (name, (ty_list, dirt_list)) ->
      let ty_list = List.map (fun x -> find_ty_solution x cnstr) ty_list in
      let dirt_list = List.map (fun x -> find_dirt_solution x cnstr) dirt_list in
      Type.Apply (name, (ty_list, dirt_list))
  end


(* find a principal solution for a dirt *)
and find_dirt_solution drt cnstr =
  begin match search_constraints_dirt drt cnstr.dirts with
    | None -> drt
    | Some drt -> drt
  end

(* find a principal solution for a dirty type *)
and find_dirty_solution (ty, drt) cnstr = (find_ty_solution ty cnstr, find_dirt_solution drt cnstr)

(***********************)
(* PRINTING OPERATIONS *)
(***********************)

(* Print constraints *)
let print constraints ppf =
  Print.sequence "," (fun (x, y, _) ppf -> Format.fprintf ppf "(%t = %t)" (Type.print_ty x) (Type.print_ty y)) constraints.types ppf;
  Format.pp_print_string ppf " ; ";
  Print.sequence "," (fun (x, y, _) ppf -> Format.fprintf ppf "(%t = %t)" (Type.print_dirt x) (Type.print_dirt y)) constraints.dirts ppf
