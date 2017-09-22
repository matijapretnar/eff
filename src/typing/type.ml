(* We need three sorts of parameters, for types, dirt, and regions.
   In order not to confuse them, we define separate types for them.
*)

type ty =
  | Apply of Common.tyname * args
  | Prim of prim_ty (* Basic of string *)
  | Tuple of ty list
  | Arrow of ty * dirty
  | Handler of dirty * dirty
  (* Type variable *)
  | TyVar of Params.ty_param
  (* Polytype *)
  | PolyType of Params.ty_param * ty list

(* Primitive types *)
and prim_ty =
  | BoolTy
  | IntTy
  | FloatTy
  | StringTy
  | UnitTy
  | UniTy

and dirty = ty * dirt

(* The dirt defined as a row *)
and dirt = {
  ops: Common.effect list;
  rest: Params.dirt_param
}

and args = ty list * dirt list

let int_ty = Prim IntTy
let string_ty = Prim StringTy
let bool_ty = Prim BoolTy
let float_ty = Prim FloatTy
let unit_ty = Prim UnitTy
let empty_ty = Apply ("empty", ([], []))

let prim_to_string prim =
  begin match prim with
    | BoolTy -> "bool"
    | IntTy -> "int"
    | FloatTy -> "float"
    | StringTy -> "string"
    | UnitTy -> "unit"
    | UniTy -> "universal"
  end

(** [fresh_ty ()] gives a type [Param p] where [p] is a new type parameter on
    each call. *)
let fresh_ty () = TyVar (Params.fresh_ty_param ())
let simple_dirt d = { ops = []; rest = d }
let fresh_dirt () = simple_dirt (Params.fresh_dirt_param ())
let fresh_dirty () = (fresh_ty (), fresh_dirt ())

(* These types are used when type checking is turned off. Their names
   are syntactically incorrect so that the programmer cannot accidentally
   define it. *)
let universal_ty = Prim UniTy (* Basic "_" *)
let universal_dirty = (Prim UniTy, fresh_dirt ()) (* (Basic "_", fresh_dirt ()) *)


type replacement = {
  ty_param_repl : Params.ty_param -> ty;
  dirt_param_repl : Params.dirt_param -> dirt;
}

(** [replace_ty rpls ty] replaces type parameters in [ty] according to [rpls]. *)
let rec replace_ty rpls = function
  | Apply (ty_name, args) -> Apply (ty_name, replace_args rpls args)
  | TyVar p -> rpls.ty_param_repl p
  | Prim _ as ty -> ty
  | Tuple tys -> Tuple (Common.map (replace_ty rpls) tys)
  | Arrow (ty1, (ty2, drt)) ->
    let ty1 = replace_ty rpls ty1 in
    let drt = replace_dirt rpls drt in
    let ty2 = replace_ty rpls ty2 in
    Arrow (ty1, (ty2, drt))
  | Handler (drty1, drty2) ->
    let drty1 = replace_dirty rpls drty1 in
    let drty2 = replace_dirty rpls drty2 in
    Handler (drty1, drty2)

and replace_dirt rpls drt =
  let { ops = new_ops; rest = new_rest } = rpls.dirt_param_repl drt.rest in
  { ops = new_ops @ drt.ops; rest = new_rest }

and replace_dirty rpls (ty, drt) =
  let ty = replace_ty rpls ty in
  let drt = replace_dirt rpls drt in
  (ty, drt)

and replace_args rpls (tys, drts) =
  let tys = Common.map (replace_ty rpls) tys in
  let drts = Common.map (replace_dirt rpls) drts in
  (tys, drts)

(** [subst_ty sbst ty] replaces type parameters in [ty] according to [sbst]. *)
let rec subst_ty sbst = function
  | Apply (ty_name, args) -> Apply (ty_name, subst_args sbst args)
  | TyVar p -> TyVar (sbst.Params.ty_param p)
  | Prim _ as ty -> ty
  | Tuple tys -> Tuple (Common.map (subst_ty sbst) tys)
  | Arrow (ty1, (ty2, drt)) ->
    let ty1 = subst_ty sbst ty1 in
    let drt = subst_dirt sbst drt in
    let ty2 = subst_ty sbst ty2 in
    Arrow (ty1, (ty2, drt))
  | Handler (drty1, drty2) ->
    let drty1 = subst_dirty sbst drty1 in
    let drty2 = subst_dirty sbst drty2 in
    Handler (drty1, drty2)

and subst_dirt sbst {ops; rest} =
  { ops = ops; rest = sbst.Params.dirt_param rest }

and subst_dirty sbst (ty, drt) =
  let ty = subst_ty sbst ty in
  let drt = subst_dirt sbst drt in
  (ty, drt)

and subst_args sbst (tys, drts) =
  let tys = Common.map (subst_ty sbst) tys in
  let drts = Common.map (subst_dirt sbst) drts in
  (tys, drts)

let refresh ty =
  let sbst = Params.refreshing_subst () in
  subst_ty sbst ty

let (@@@) = Params.append

let for_parameters get_params is_pos ps lst =
  List.fold_right2 (fun (_, (cov, contra)) el params ->
      let params = if cov then get_params is_pos el @@@ params else params in
      if contra then get_params (not is_pos) el @@@ params else params) ps lst Params.empty

let print_dirt drt ppf =
  match drt.ops with
  | [] ->
    Print.print ppf "%t" (Params.print_dirt_param drt.rest)
  | _ ->
    let print_operation op ppf =
      Print.print ppf "%s" op
    in
    Print.print ppf "{%t|%t}"
      (Print.sequence ", " print_operation drt.ops)
      (Params.print_dirt_param drt.rest)

let rec print_ty ?max_level ty ppf =
  let print ?at_level = Print.print ?max_level ?at_level ppf in
  match ty with
  | Apply (ty_name, ([], _)) ->
    print "%s" ty_name
  | Apply (ty_name, ([ty], _)) ->
    print ~at_level:1 "%t %s" (print_ty ~max_level:1 ty) ty_name
  | Apply (ty_name, (tys, _)) ->
    print ~at_level:1 "(%t) %s" (Print.sequence ", " print_ty tys) ty_name
  | TyVar p -> Params.print_ty_param p ppf
  | Prim b -> print "%s" (prim_to_string b)
  | Tuple [] -> print "unit"
  | Tuple tys ->
    print ~at_level:2 "@[<hov>%t@]"
      (Print.sequence (Symbols.times ()) (print_ty ~max_level:1) tys)
  | Arrow (t1, (t2, drt)) ->
    print ~at_level:5 "@[%t -%t%s@ %t@]"
      (print_ty ~max_level:4 t1)
      (print_dirt drt)
      (Symbols.short_arrow ())
      (print_ty ~max_level:5 t2)
  | Handler ((t1, drt1), (t2, drt2)) ->
    print ~at_level:6 "%t ! %t %s@ %t ! %t"
      (print_ty ~max_level:4 t1)
      (print_dirt drt1)
      (Symbols.handler_arrow ())
      (print_ty ~max_level:4 t2)
      (print_dirt drt2)
