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
type context = (Untyped.variable, Type.ty) OldUtils.assoc

(******************)
(* HELPER METHODS *)
(******************)

(* Add a type constraint to a constraint set *)
let add_type ty cnstr = {
  types = ty :: cnstr.types;
  dirts = cnstr.dirts
}

let add_dirt drt cnstr = {
  types = cnstr.types;
  dirts = drt :: cnstr.dirts
}

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

(* let rec check_ctx ty ctx =
  begin match ctx with
    | [] -> true
    | (x, y) :: lst -> if y = ty then false else check_ctx ty lst
  end *)

(* within [ty] substitute [ty_old] with [ty_new] *)
(* let rec perform_subst_ty ty_old ty_new ty =
  begin match ty with
    | t when t = ty_old -> ty_new
    | Type.Arrow (ty_in, (ty_out, d)) ->
      let ty_in = perform_subst_ty ty_old ty_new ty_in in
      let ty_out = perform_subst_ty ty_old ty_new ty_out in
      Type.Arrow (ty_in, (ty_out, d))
    | Type.Handler ((ty_in, d1), (ty_out, d2)) ->
      let ty_in = perform_subst_ty ty_old ty_new ty_in in
      let ty_out = perform_subst_ty ty_old ty_new ty_out in
      Type.Handler ((ty_in, d1), (ty_out, d2))
    | Type.Tuple lst ->
      let lst = List.map (perform_subst_ty ty_old ty_new) lst in
      Type.Tuple lst
    | Type.Apply (ty_name, (lst, drts)) ->
      let lst = List.map (perform_subst_ty ty_old ty_new) lst in
      Type.Apply (ty_name, (lst, drts))
    (* not matching or primitive *)
    | _ -> ty
  end *)

(* unify types *)
(* let rec unify_types ctx ty cnstr =
  begin match cnstr.types with
    | [] -> (ctx, ty, cnstr)
    | (ty1, ty2, loc) :: tail ->
      let cnstr_new = {cnstr with types=tail} in
      begin match ty1, ty2 with
        | (ty1, ty2) when ty1 = ty2 -> unify_types ctx ty cnstr_new

        | (Type.Tuple tys1, Type.Tuple tys2) when List.length tys1 = List.length tys2 ->
          let cnstr = List.fold_right2 (add_ty_constraint ~loc) tys1 tys2 cnstr_new in
          unify_types ctx ty cnstr

        (* | (Type.Apply (ty_name1, args1), Type.Apply (ty_name2, args2)) when ty_name1 = ty_name2 ->
          begin match Tctx.lookup_params ty_name1 with
            | None -> Error.typing ~loc "Undefined type %s" ty_name1
            | Some params -> add_args_constraint ~loc params args1 args2 constraints
          end *)
      (*
      (* The following two cases cannot be merged into one, as the whole matching
         fails if both types are Apply, but only the second one is transparent. *)
      | (Type.Apply (ty_name, args), ty) when Tctx.transparent ~loc ty_name ->
        begin match Tctx.ty_apply ~loc ty_name args with
          | Tctx.Inline ty' -> add_ty_constraint ~loc ty' ty constraints
          | Tctx.Sum _ | Tctx.Record _ -> assert false (* None of these are transparent *)
        end

      | (ty, Type.Apply (ty_name, args)) when Tctx.transparent ~loc ty_name ->
        begin match Tctx.ty_apply ~loc ty_name args with
          | Tctx.Inline ty' -> add_ty_constraint ~loc ty ty' constraints
          | Tctx.Sum _ | Tctx.Record _ -> assert false (* None of these are transparent *)
        end *)

        (* substitute ty1 with ty2 (if ty1 is not a FTV) *)
        | (Type.TyVar t1, t2) when check_ctx ty1 ctx ->
          let ty = perform_subst_ty ty1 ty2 ty in
          let cnstr_types = List.map (
            fun (t1, t2, loc) ->
              let t1 = perform_subst_ty ty1 ty2 t1 in
              let t2 = perform_subst_ty ty1 ty2 t2 in
              (t1, t2, loc)
          ) cnstr_new.types in
          let cnstr = {cnstr_new with types=cnstr_types} in
          unify_types ctx ty cnstr

        (* substitute ty2 with ty1 (if ty2 is not a FTV) *)
        | (t1, Type.TyVar t2) when check_ctx ty2 ctx ->
          let ty = perform_subst_ty ty2 ty1 ty in
          let cnstr_types = List.map (
            fun (t1, t2, loc) ->
              let t1 = perform_subst_ty ty2 ty1 t1 in
              let t2 = perform_subst_ty ty2 ty1 t2 in
              (t1, t2, loc)
          ) cnstr_new.types in
          let cnstr = {cnstr_new with types=cnstr_types} in
          unify_types ctx ty cnstr

        (* A -> B ! a = C -> D ! b translates into: A=C, B=D, a=b *)
        | (Type.Arrow (ty1_in, dirty1_out), Type.Arrow (ty2_in, dirty2_out)) ->
          let cnstr = add_ty_constraint ~loc ty1_in ty2_in cnstr_new in
          let cnstr = add_dirty_constraint ~loc dirty1_out dirty2_out cnstr in
          unify_types ctx ty cnstr

        (* A ! a => B ! b = C ! c => D ! d translates into: A=C, B=D, a=c, b=d *)
        | (Type.Handler (dirty1_in, dirty1_out), Type.Handler (dirty2_in, dirty2_out)) ->
          let cnstr = add_dirty_constraint ~loc dirty1_in dirty2_in cnstr_new in
          let cnstr = add_dirty_constraint ~loc dirty1_out dirty2_out cnstr in
          unify_types ctx ty cnstr

        (* keep constraints when ty1 is an element of the context *)
        | (Type.TyVar t1, t2) when not (check_ctx ty1 ctx) ->
          let (ctx, ty, cnstr) = unify_types ctx ty cnstr_new in
          let cnstr = add_ty_constraint ~loc ty1 ty2 cnstr in
          (ctx, ty, cnstr)

        (* keep constraints when ty2 is an element of the context *)
        | (t1, Type.TyVar t2) when not (check_ctx ty2 ctx) ->
          let (ctx, ty, cnstr) = unify_types ctx ty cnstr_new in
          let cnstr = add_ty_constraint ~loc ty1 ty2 cnstr in
          (ctx, ty, cnstr)

        (* Primitives *)
        | (Type.Prim Type.BoolTy, Type.Prim Type.BoolTy) -> unify_types ctx ty cnstr_new
        | (Type.Prim Type.IntTy, Type.Prim Type.IntTy) -> unify_types ctx ty cnstr_new
        | (Type.Prim Type.FloatTy, Type.Prim Type.FloatTy) -> unify_types ctx ty cnstr_new
        | (Type.Prim Type.StringTy, Type.Prim Type.StringTy) -> unify_types ctx ty cnstr_new
        | (Type.Tuple [], Type.Tuple []) -> unify_types ctx ty cnstr_new
        | (Type.Prim Type.UniTy, Type.Prim Type.UniTy) -> unify_types ctx ty cnstr_new

        (* Constraints could not be unified *)
        | _ -> Error.typing ~loc "This expression has type %t but it should have type %t." (Type.print_ty ty1) (Type.print_ty ty2)
      end
  end *)

(* Check if a dirt only contains a var and no operations *)
(* let is_drt_var drt =
  begin match drt.Type.ops with
    | [] -> true
    | _ -> false
  end *)

(* let rec contains x = function
  | [] -> false
  | x' :: lst -> if (x = x') then true else contains x lst *)

(* let rec dirt_difference main minus =
    begin match main with
    | [] -> []
    | d :: lst when (contains d minus) -> dirt_difference lst minus
    | d :: lst -> d :: dirt_difference lst minus
    end *)

(* let contains_ops main other =
  let rec check main other =
    begin match other with
      | [] -> []
      | d :: lst when (contains d main) -> check main lst
      | d :: lst -> d :: check main lst
    end in
  List.length (check main other) = 0 *)

(* let check_drt drt_old drt_new drt =
  begin match drt with
    | drt when (drt = drt_old) && (is_drt_var drt_old) -> drt_new
    | drt when (drt.Type.rest = drt_old.Type.rest) && (is_drt_var drt_old) ->
      Type.add_ops drt.Type.ops drt_new
    | drt when (drt.Type.rest = drt_old.Type.rest) && (contains_ops drt.Type.ops drt_old.Type.ops) ->
      Type.add_ops (dirt_difference drt.Type.ops drt_old.Type.ops) drt_new
    | _ -> drt
  end *)

(* within [ty] substitute [ty_old] with [ty_new] *)
(* let rec perform_subst_drty drt_old drt_new ty =
  begin match ty with
    | Type.Arrow (ty_in, (ty_out, d)) ->
      let ty_in = perform_subst_drty drt_old drt_new ty_in in
      let ty_out = perform_subst_drty drt_old drt_new ty_out in
      let d = check_drt drt_old drt_new d in
      Type.Arrow (ty_in, (ty_out, d))
    | Type.Handler ((ty_in, d1), (ty_out, d2)) ->
      let ty_in = perform_subst_drty drt_old drt_new ty_in in
      let ty_out = perform_subst_drty drt_old drt_new ty_out in
      let d1 = check_drt drt_old drt_new d1 in
      let d2 = check_drt drt_old drt_new d2 in
      Type.Handler ((ty_in, d1), (ty_out, d2))
    | Type.Tuple lst ->
      let lst = List.map (perform_subst_drty drt_old drt_new) lst in
      Type.Tuple lst
    | Type.Apply (ty_name, (lst, drts)) ->
      let lst = List.map (perform_subst_drty drt_old drt_new) lst in
      let drts = List.map (check_drt drt_old drt_new) drts in
      Type.Apply (ty_name, (lst, drts))
    (* not matching or primitive *)
    | _ -> ty
  end *)

(*
  Unify two dirts of the form:
    d1 = {ops... ; d2}
    d1 = {ops... ; d3}
  into:
    d2 = {ops... ; d4}
    d3 = {ops... ; d4}
    d1 = {ops... ; d4}
*)
(* let unify_single_dirt loc drt2 drt3 =
  let out = Type.fresh_dirt () in
  let out = Type.add_ops drt2.Type.ops out in
  let out = Type.add_ops drt3.Type.ops out in
  let out2_l = Type.make_dirt [] drt2.Type.rest in
  let out3_l = Type.make_dirt [] drt3.Type.rest in
  let out2_r = Type.make_dirt (dirt_difference drt3.Type.ops drt2.Type.ops) out.Type.rest in
  let out3_r = Type.make_dirt (dirt_difference drt2.Type.ops drt3.Type.ops) out.Type.rest in
  out, (out2_l, out2_r, loc), (out3_l, out3_r, loc) *)

(* unify types *)
(* let rec unify_dirts ctx (ty, drt) cnstr =
  begin match cnstr.dirts with
    | [] -> (ctx, (ty, drt), cnstr)
    | (drt1, drt2, loc) :: tail ->
      let cnstr_new = {cnstr with dirts=tail} in
      begin match drt1, drt2 with
        | (drt1, drt2) when drt1 = drt2 -> unify_dirts ctx (ty, drt) cnstr_new
        | (drt1, drt2) when is_drt_var drt1 ->
          let ty = perform_subst_drty drt1 drt2 ty in
          let drt = check_drt drt1 drt2 drt in
          let cnstr_dirts = List.map (
            fun (d1, d2, loc) ->
              let d1 = check_drt drt1 drt2 d1 in
              let d2 = check_drt drt1 drt2 d2 in
              (d1, d2, loc)
          ) cnstr_new.dirts in
          let cnstr = {cnstr_new with dirts=cnstr_dirts} in
          unify_dirts ctx (ty, drt) cnstr
        | (drt2, drt1) when is_drt_var drt1 ->
          let ty = perform_subst_drty drt1 drt2 ty in
          let drt = check_drt drt1 drt2 drt in
          let cnstr_dirts = List.map (
            fun (d1, d2, loc) ->
              let d1 = check_drt drt1 drt2 d1 in
              let d2 = check_drt drt1 drt2 d2 in
              (d1, d2, loc)
          ) cnstr_new.dirts in
          let cnstr = {cnstr_new with dirts=cnstr_dirts} in
          unify_dirts ctx (ty, drt) cnstr
        | (drt1, drt2) ->
          let new1, new2, new3 = unify_single_dirt loc drt1 drt2 in
          let cnstr = add_dirt new2 cnstr_new in
          let cnstr = add_dirt new3 cnstr in
          unify_dirts ctx (ty, drt) cnstr
      end
  end *)

(*
Strategy:
  biunify 
  subi -> match
  atomic -> match + create subst (see subst)
  constructed -> simple match

  substitute -> (keeps track of polarity)
*)

(* Unify the constraints to find a solution *)
let unify_ty ctx ty cnstr = 
  (* let ctx, ty, cnstr = unify_types ctx ty cnstr in *)
  (ctx, ty, cnstr)

(* Unify the constraints to find a solution *)
let unify_dirty ctx (ty, drt) cnstr =
  (* let ctx, ty, cnstr = unify_ty ctx ty cnstr in *)
  (* let ctx, (ty, drt), cnstr = unify_dirts ctx (ty, drt) cnstr in *)
  (ctx, (ty, drt), cnstr)

(***********************)
(* PRINTING OPERATIONS *)
(***********************)

(* Print constraints *)
let print constraints ppf =
  Print.sequence "," (fun (x, y, _) ppf -> Format.fprintf ppf "(%t %s %t)" (Type.print_ty x) (Symbols.less ()) (Type.print_ty y)) constraints.types ppf;
  Format.pp_print_string ppf " ; ";
  Print.sequence "," (fun (x, y, _) ppf -> Format.fprintf ppf "(%t %s %t)" (Type.print_dirt x) (Symbols.less ()) (Type.print_dirt y)) constraints.dirts ppf
