(* We need two sorts of parameters, for types and dirt.
   In order not to confuse them, we define separate types for them.
*)

type ty =
  | Apply of OldUtils.tyname * args
  | Prim of prim_ty
  | Tuple of ty list
  | Arrow of ty * dirty
  | Handler of dirty * dirty
  | TyVar of Params.ty_param
  | Bottom
  | Top
  | RecType of Params.ty_param * ty
  | Union of ty * ty
  | Intersection of ty * ty

(* Primitive types *)
and prim_ty =
  | BoolTy
  | IntTy
  | FloatTy
  | StringTy
  | UniTy

and dirty = ty * dirt

(* The dirt defined as a row *)
and dirt = 
  | Op of OldUtils.effect
  | DirtVar of Params.dirt_param
  | DirtBottom
  | DirtUnion of dirt * dirt
  | DirtIntersection of dirt * dirt
(* {
  ops: OldUtils.effect list;
  rest: Params.dirt_param
} *)

and args = ty list * dirt list

let int_ty = Prim IntTy
let string_ty = Prim StringTy
let bool_ty = Prim BoolTy
let float_ty = Prim FloatTy
let unit_ty = Tuple []
let empty_ty = Apply ("empty", ([], []))

let prim_to_string prim =
  begin match prim with
    | BoolTy -> "bool"
    | IntTy -> "int"
    | FloatTy -> "float"
    | StringTy -> "string"
    | UniTy -> "universal"
  end

(** [fresh_ty ()] gives a type [Param p] where [p] is a new type parameter on
    each call. *)
let fresh_ty () = TyVar (Params.fresh_ty_param ())
let simple_dirt d = DirtVar d (* { ops = []; rest = d } *)
let fresh_dirt () = simple_dirt (Params.fresh_dirt_param ())
let fresh_dirty () = (fresh_ty (), fresh_dirt ())

let add_ops ops d = DirtUnion (ops, d) (* { ops = OldUtils.uniq (ops @ d.ops); rest = d.rest } *)
let fresh_dirt_ops ops = add_ops ops (fresh_dirt ())

let make_dirt ops rest = DirtUnion (ops, rest) (*{ ops = ops; rest = rest }*)

let add_ops_list ops d = List.fold_left (fun d1 d2 -> DirtUnion (d1, Op d2)) d ops

let rec get_var_internal drt = (* d.rest *)
  begin match drt with
    | Op _ -> None
    | DirtVar d -> Some drt
    | DirtBottom -> None
    | DirtUnion (d1, d2) -> 
      begin match (get_var_internal d1) with
        | None -> get_var_internal d2
        | Some d -> Some d
      end
    | DirtIntersection (d1, d2) -> 
      begin match (get_var_internal d1) with
        | None -> get_var_internal d2
        | Some d -> Some d
      end
  end

let get_var drt = 
  match (get_var_internal drt) with 
    | Some (DirtVar d) -> d

(* These types are used when type checking is turned off. Their names
   are syntactically incorrect so that the programmer cannot accidentally
   define it. *)
let universal_ty = Prim UniTy (* Basic "_" *)
let universal_dirty = (Prim UniTy, fresh_dirt ()) (* (Basic "_", fresh_dirt ()) *)


type replacement = {
  ty_param_repl : Params.ty_param -> ty;
  dirt_param_repl : Params.dirt_param -> dirt;
}

let rec replace_dirt rpls drt =
  begin match drt with
    | Op _ -> drt
    | DirtVar d -> (rpls.dirt_param_repl d)
    | DirtBottom -> DirtBottom
    | DirtUnion (d1, d2) -> DirtUnion ((replace_dirt rpls d1), (replace_dirt rpls d2))
    | DirtIntersection (d1, d2) -> DirtIntersection ((replace_dirt rpls d1), (replace_dirt rpls d2))
  end
  (* let { ops = new_ops; rest = new_rest } = rpls.dirt_param_repl drt.rest in *)
  (* { ops = new_ops @ drt.ops; rest = new_rest } *)

(** [replace_ty rpls ty] replaces type parameters in [ty] according to [rpls]. *)
let rec replace_ty rpls = function
  | Apply (ty_name, args) -> Apply (ty_name, replace_args rpls args)
  | TyVar p -> rpls.ty_param_repl p
  | Prim _ as ty -> ty
  | Tuple tys -> Tuple (OldUtils.map (replace_ty rpls) tys)
  | Arrow (ty1, (ty2, drt)) ->
    let ty1 = replace_ty rpls ty1 in
    let drt = replace_dirt rpls drt in
    let ty2 = replace_ty rpls ty2 in
    Arrow (ty1, (ty2, drt))
  | Handler (drty1, drty2) ->
    let drty1 = replace_dirty rpls drty1 in
    let drty2 = replace_dirty rpls drty2 in
    Handler (drty1, drty2)

and replace_dirty rpls (ty, drt) =
  let ty = replace_ty rpls ty in
  let drt = replace_dirt rpls drt in
  (ty, drt)

and replace_args rpls (tys, drts) =
  let tys = OldUtils.map (replace_ty rpls) tys in
  let drts = OldUtils.map (replace_dirt rpls) drts in
  (tys, drts)

let rec subst_dirt sbst drt = (* {ops; rest} = *)
  begin match drt with
    | Op _ -> drt
    | DirtVar d -> DirtVar (sbst.Params.dirt_param d)
    | DirtBottom -> DirtBottom
    | DirtUnion (d1, d2) -> DirtUnion ((subst_dirt sbst d1), (subst_dirt sbst d2))
    | DirtIntersection (d1, d2) -> DirtIntersection ((subst_dirt sbst d1), (subst_dirt sbst d2))
  end
  (* { ops = ops; rest = sbst.Params.dirt_param rest } *)

(** [subst_ty sbst ty] replaces type parameters in [ty] according to [sbst]. *)
let rec subst_ty sbst = function
  | Apply (ty_name, args) -> Apply (ty_name, subst_args sbst args)
  | TyVar p -> TyVar (sbst.Params.ty_param p)
  | Prim _ as ty -> ty
  | Tuple tys -> Tuple (OldUtils.map (subst_ty sbst) tys)
  | Arrow (ty1, (ty2, drt)) ->
    let ty1 = subst_ty sbst ty1 in
    let drt = subst_dirt sbst drt in
    let ty2 = subst_ty sbst ty2 in
    Arrow (ty1, (ty2, drt))
  | Handler (drty1, drty2) ->
    let drty1 = subst_dirty sbst drty1 in
    let drty2 = subst_dirty sbst drty2 in
    Handler (drty1, drty2)
  | Bottom -> Bottom
  | Top -> Top
  | Union (ty1, ty2) ->
    let ty1 = subst_ty sbst ty1 in
    let ty2 = subst_ty sbst ty2 in
    Union (ty1, ty2)
  | Intersection (ty1, ty2) ->
    let ty1 = subst_ty sbst ty1 in
    let ty2 = subst_ty sbst ty2 in
    Intersection (ty1, ty2)

and subst_dirty sbst (ty, drt) =
  let ty = subst_ty sbst ty in
  let drt = subst_dirt sbst drt in
  (ty, drt)

and subst_args sbst (tys, drts) =
  let tys = OldUtils.map (subst_ty sbst) tys in
  let drts = OldUtils.map (subst_dirt sbst) drts in
  (tys, drts)

let refresh ty =
  let sbst = Params.refreshing_subst () in
  subst_ty sbst ty

let (@@@) = Params.append

let for_parameters get_params is_pos ps lst =
  List.fold_right2 (fun (_, (cov, contra)) el params ->
      let params = if cov then get_params is_pos el @@@ params else params in
      if contra then get_params (not is_pos) el @@@ params else params) ps lst Params.empty

let rec print_dirt drt ppf =
  begin match drt with
    | Op op -> 
      let print_operation op ppf =
        Print.print ppf "%s" op
      in
      print_operation op ppf
    | DirtVar d -> Print.print ppf "%t" (Params.print_dirt_param d)
    | DirtBottom -> Print.print ppf "%s" (Symbols.bottom ())
    | DirtUnion (d1, d2) -> (print_dirt d1 ppf); (Print.print ppf " %s " (Symbols.union ())); (print_dirt d2 ppf)
    | DirtIntersection (d1, d2) -> (print_dirt d1 ppf); (Print.print ppf " %s " (Symbols.intersection ())); (print_dirt d2 ppf)
  end
  (* match drt.ops with
  | [] ->
    Print.print ppf "%t" (Params.print_dirt_param drt.rest)
  | _ ->
    let print_operation op ppf =
      Print.print ppf "%s" op
    in
    Print.print ppf "{%t|%t}"
      (Print.sequence ", " print_operation drt.ops)
      (Params.print_dirt_param drt.rest) *)
        
      
let rec print_ty ?max_level ty ppf =
  let print ?at_level = Print.print ?max_level ?at_level ppf in
  match ty with
  | Apply (ty_name, ([], _)) ->
    print ".%s" ty_name
  | Apply (ty_name, ([ty], _)) ->
    print ~at_level:1 "%t .%s" (print_ty ~max_level:1 ty) ty_name
  | Apply (ty_name, (tys, _)) ->
    print ~at_level:1 "(%t) %s" (Print.sequence ", " print_ty tys) ty_name
  | TyVar p -> Params.print_ty_param p ppf
  | Prim b -> print "%s" (prim_to_string b)
  | Tuple [] -> print "unit"
  | Tuple tys ->
    print ~at_level:2 "@[<hov>%t@]"
      (Print.sequence (Symbols.times ()) (print_ty ~max_level:1) tys)
  | Arrow (t1, (t2, drt)) ->
    print ~at_level:5 "@[%t -(%t)%s@ %t@]"
      (print_ty ~max_level:4 t1)
      (print_dirt drt)
      (Symbols.short_arrow ())
      (print_ty ~max_level:5 t2)
  | Handler ((t1, drt1), (t2, drt2)) ->
    print ~at_level:6 "%t ! (%t) %s@ %t ! (%t)"
      (print_ty ~max_level:4 t1)
      (print_dirt drt1)
      (Symbols.handler_arrow ())
      (print_ty ~max_level:4 t2)
      (print_dirt drt2)
  | Bottom -> print "%s" (Symbols.bottom ())
  | Top -> print "%s" (Symbols.top ())
  | Union (t1, t2) ->
    print ~at_level:5 "@[%t %s@ %t@]"
      (print_ty ~max_level:4 t1)
      (Symbols.union ())
      (print_ty ~max_level:5 t2)
  | Intersection (t1, t2) ->
    print ~at_level:5 "@[%t %s@ %t@]"
      (print_ty ~max_level:4 t1)
      (Symbols.intersection ())
      (print_ty ~max_level:5 t2)
