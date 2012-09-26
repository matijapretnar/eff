(* We need three sorts of parameters, for types, dirt, and regions.
   In order not to confuse them, we define separate types for them.
 *)

type ty_param = Ty_Param of int
type dirt_param = Dirt_Param of int
type region_param = Region_Param of int
type instance_param = Instance_Param of int

let fresh_ty_param = Common.fresh (fun n -> Ty_Param n)
let fresh_dirt_param = Common.fresh (fun n -> Dirt_Param n)
let fresh_region_param = Common.fresh (fun n -> Region_Param n)
let fresh_instance_param = Common.fresh (fun n -> Instance_Param n)

type ty =
  | Apply of Common.tyname * args
  | Effect of Common.tyname * args * region_param
  | TyParam of ty_param
  | Basic of string
  | Tuple of ty list
  | Arrow of ty * dirty
  | Handler of ty * ty

and dirty = instance_param list * ty * dirt_param

and args = (ty, dirt_param, region_param) Trio.t


(* This type is used when type checking is turned off. Its name
   is syntactically incorrect so that the programmer cannot accidentally
   define it. *)
let universal_ty = Basic "_"
let universal_dirty = ([], ([], Basic "_", fresh_dirt_param ()), [])

let int_ty = Basic "int"
let string_ty = Basic "string"
let bool_ty = Basic "bool"
let float_ty = Basic "float"
let unit_ty = Tuple []
let empty_ty = Apply ("empty", Trio.empty)

(** [fresh_ty ()] gives a type [TyParam p] where [p] is a new type parameter on
    each call. *)
let fresh_ty () = TyParam (fresh_ty_param ())
(* XXX Should a fresh dirty type have no fresh instances? *)
let fresh_dirty () = ([], fresh_ty (), fresh_dirt_param ())


type substitution = {
  ty_param : ty_param -> ty;
  dirt_param : dirt_param -> dirt_param;
  region_param : region_param -> region_param;
  instance_param : instance_param -> instance_param option;
}

(** [subst_ty sbst ty] replaces type parameters in [ty] according to [sbst]. *)
let rec subst_ty sbst = function
  | Apply (ty_name, args) -> Apply (ty_name, subst_args sbst args)
  | Effect (ty_name, args, r) -> Effect (ty_name, subst_args sbst args, sbst.region_param r)
  | TyParam p -> sbst.ty_param p
  | Basic _ as ty -> ty
  | Tuple tys -> Tuple (List.map (subst_ty sbst) tys)
  | Arrow (ty1, ty2) -> Arrow (subst_ty sbst ty1, subst_dirty sbst ty2)
  | Handler (ty1, ty2) -> Handler (subst_ty sbst ty1, subst_ty sbst ty2)

and subst_dirty sbst (frsh, ty, d) =
  let subst_instance i frsh =
    match sbst.instance_param i with
    | Some j -> j :: frsh
    | None -> frsh
  in
  (List.fold_right subst_instance frsh [], subst_ty sbst ty, sbst.dirt_param d)

and subst_args sbst (tys, ds, rs) =
  (List.map (subst_ty sbst) tys, List.map sbst.dirt_param ds, List.map sbst.region_param rs)

(** [identity_subst] is a substitution that makes no changes. *)
let identity_subst = {
  ty_param = (fun p -> TyParam p);
  dirt_param = Common.id;
  region_param = Common.id;
  instance_param = (fun i -> Some i);
}

(** [compose_subst sbst1 sbst2] returns a substitution that first performs
    [sbst2] and then [sbst1]. *)
let compose_subst sbst1 sbst2 =
  {
    ty_param = Common.compose (subst_ty sbst1) sbst2.ty_param;
    dirt_param = Common.compose sbst1.dirt_param sbst2.dirt_param;
    region_param = Common.compose sbst1.region_param sbst2.region_param;
    instance_param = (fun i -> match sbst2.instance_param i with None -> None | Some j -> sbst1.instance_param j);
  }

let refresher fresh =
  let substitution = ref [] in
  fun p ->
    match Common.lookup p !substitution with
    | None ->
        let p' = fresh () in
        substitution := Common.update p p' !substitution;
        p'
    | Some p' -> p'

let create_subst (fresh_ty_param, fresh_dirt_param, fresh_region_param) =
  let refresh = refresher fresh_ty_param in
  {
    identity_subst with
    ty_param = (fun p -> TyParam (refresh p));
    dirt_param = refresher fresh_dirt_param;
    region_param = refresher fresh_region_param;
  }

let disable_beautify = ref false

let beautifying_subst () =
  if !disable_beautify then
    identity_subst
  else
    let beautify_ty_param = Common.fresh (fun n -> Ty_Param n)
    and beautify_dirt_param = Common.fresh (fun n -> Dirt_Param n)
    and beautify_region_param = Common.fresh (fun n -> Region_Param n)
    in
    create_subst (beautify_ty_param, beautify_dirt_param, beautify_region_param)

let refreshing_subst () =
  create_subst (fresh_ty_param, fresh_dirt_param, fresh_region_param)

let refresh ty =
  let sbst = refreshing_subst () in
  subst_ty sbst ty

let instance_refreshing_subst is =
  identity_subst
(*   {
    identity_subst with
    instance_param = let refresh = fun i -> Some (fresh_instance_param ()))) is;
  }
 *)
let beautify2 ty1 ty2 =
  let sbst = beautifying_subst () in
  (subst_ty sbst ty1, subst_ty sbst ty2)
