(* We need three sorts of parameters, for types, dirt, and regions.
   In order not to confuse them, we define separate types for them.
*)

type ty =
  | Apply of OldUtils.tyname * args
  | Param of Params.ty_param
  | Basic of string
  | Tuple of ty list
  | Arrow of ty * dirty
  | Handler of dirty * dirty

and dirty = ty * dirt

and dirt = {
  ops: (OldUtils.effect, Params.region_param) OldUtils.assoc;
  rest: Params.dirt_param
}

and args = ty list * dirt list * Params.region_param list


let int_ty = Basic "int"
let string_ty = Basic "string"
let bool_ty = Basic "bool"
let float_ty = Basic "float"
let unit_ty = Tuple []
let empty_ty = Apply ("empty", ([], [], []))

(** [fresh_ty ()] gives a type [Param p] where [p] is a new type parameter on
    each call. *)
let fresh_ty () = Param (Params.fresh_ty_param ())
let simple_dirt d = { ops = []; rest = d }
let fresh_dirt () = simple_dirt (Params.fresh_dirt_param ())
let fresh_dirty () = (fresh_ty (), fresh_dirt ())

(* These types are used when type checking is turned off. Their names
   are syntactically incorrect so that the programmer cannot accidentally
   define it. *)
let universal_ty = Basic "_"
let universal_dirty = (Basic "_", fresh_dirt ())


type replacement = {
  ty_param_repl : Params.ty_param -> ty;
  dirt_param_repl : Params.dirt_param -> dirt;
  region_param_repl : Params.region_param -> Params.region_param;
}

(** [replace_ty rpls ty] replaces type parameters in [ty] according to [rpls]. *)
let rec replace_ty rpls = function
  | Apply (ty_name, args) -> Apply (ty_name, replace_args rpls args)
  | Param p -> rpls.ty_param_repl p
  | Basic _ as ty -> ty
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

and replace_dirt rpls drt =
  let ops = OldUtils.assoc_map rpls.region_param_repl drt.ops in
  let { ops = new_ops; rest = new_rest } = rpls.dirt_param_repl drt.rest in
  { ops = new_ops @ ops; rest = new_rest }

and replace_dirty rpls (ty, drt) =
  let ty = replace_ty rpls ty in
  let drt = replace_dirt rpls drt in
  (ty, drt)

and replace_args rpls (tys, drts, rs) =
  let tys = OldUtils.map (replace_ty rpls) tys in
  let drts = OldUtils.map (replace_dirt rpls) drts in
  let rs = OldUtils.map rpls.region_param_repl rs in
  (tys, drts, rs)

(** [subst_ty sbst ty] replaces type parameters in [ty] according to [sbst]. *)
let rec subst_ty sbst = function
  | Apply (ty_name, args) -> Apply (ty_name, subst_args sbst args)
  | Param p -> Param (sbst.Params.ty_param p)
  | Basic _ as ty -> ty
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

and subst_dirt sbst {ops; rest} =
  { ops = OldUtils.assoc_map sbst.Params.region_param ops; rest = sbst.Params.dirt_param rest }

and subst_dirty sbst (ty, drt) =
  let ty = subst_ty sbst ty in
  let drt = subst_dirt sbst drt in
  (ty, drt)

and subst_args sbst (tys, drts, rs) =
  let tys = OldUtils.map (subst_ty sbst) tys in
  let drts = OldUtils.map (subst_dirt sbst) drts in
  let rs = OldUtils.map sbst.Params.region_param rs in
  (tys, drts, rs)

let refresh ty =
  let sbst = Params.refreshing_subst () in
  subst_ty sbst ty

let (@@@) = Params.append

let for_parameters get_params is_pos ps lst =
  List.fold_right2 (fun (_, (cov, contra)) el params ->
      let params = if cov then get_params is_pos el @@@ params else params in
      if contra then get_params (not is_pos) el @@@ params else params) ps lst Params.empty

let pos_neg_params get_variances ty =
  let rec pos_ty is_pos = function
    | Apply (ty_name, args) -> pos_args is_pos ty_name args
    | Param p -> if is_pos then Params.add_ty_param p Params.empty else Params.empty
    | Basic _ -> Params.empty
    | Tuple tys -> Params.flatten_map (pos_ty is_pos) tys
    | Arrow (ty1, drty2) -> pos_ty (not is_pos) ty1 @@@ pos_dirty is_pos drty2
    | Handler ((ty1, drt1), drty2) -> pos_ty (not is_pos) ty1 @@@ pos_dirt (not is_pos) drt1 @@@ pos_dirty is_pos drty2
  and pos_dirty is_pos (ty, drt) =
    pos_ty is_pos ty @@@ pos_dirt is_pos drt
  and pos_dirt is_pos drt =
    pos_dirt_param is_pos drt.rest @@@ Params.flatten_map (fun (op, dt) -> if op = "*poly*" then pos_region_param true dt @@@ pos_region_param false dt else pos_region_param is_pos dt) drt.ops
  and pos_dirt_param is_pos d =
    if is_pos then Params.add_dirt_param d Params.empty else Params.empty
  and pos_region_param is_pos r =
    if is_pos then Params.add_region_param r Params.empty else Params.empty
  and pos_args is_pos ty_name (tys, drts, rgns) =
    let (ps, ds, rs) = get_variances ty_name in
    for_parameters pos_ty is_pos ps tys @@@
    for_parameters pos_dirt is_pos ds drts @@@
    for_parameters pos_region_param is_pos rs rgns
  in
  Params.uniq (pos_ty true ty), Params.uniq (pos_ty false ty)

let print_dirt drt ppf =
  match drt.ops with
  | [] ->
    Print.print ppf "%t" (Params.print_dirt_param drt.rest)
  | _ ->
    let print_operation (op, r) ppf =
      Print.print ppf "%s:%t" op (Params.print_region_param r)
    in
    Print.print ppf "{%t|%t}"
      (Print.sequence ", " print_operation drt.ops)
      (Params.print_dirt_param drt.rest)

let rec print_ty ?max_level ty ppf =
  let print ?at_level = Print.print ?max_level ?at_level ppf in
  match ty with
  | Apply (ty_name, ([], _, _)) ->
    print "%s" ty_name
  | Apply (ty_name, ([ty], _, _)) ->
    print ~at_level:1 "%t %s" (print_ty ~max_level:1 ty) ty_name
  | Apply (ty_name, (tys, _, _)) ->
    print ~at_level:1 "(%t) %s" (Print.sequence ", " print_ty tys) ty_name
  | Param p -> Params.print_ty_param p ppf
  | Basic b -> print "%s" b
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
