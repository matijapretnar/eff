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
  | Effect (ty_name, args, r) ->
      let args = subst_args sbst args in
      let r = sbst.region_param r in
      Effect (ty_name, args, r)
  | TyParam p -> sbst.ty_param p
  | Basic _ as ty -> ty
  | Tuple tys -> Tuple (Common.map (subst_ty sbst) tys)
  | Arrow (ty1, drty2) ->
      let ty1 = subst_ty sbst ty1 in
      let drty2 = subst_dirty sbst drty2 in
      Arrow (ty1, drty2)
  | Handler (ty1, ty2) ->
      let ty1 = subst_ty sbst ty1 in
      let ty2 = subst_ty sbst ty2 in
      Handler (ty1, ty2)

and subst_dirty sbst (frsh, ty, d) =
  let subst_instance i frsh =
    match sbst.instance_param i with
    | Some j -> j :: frsh
    | None -> frsh
  in
  let frsh = List.fold_right subst_instance frsh [] in
  let ty = subst_ty sbst ty in
  let d = sbst.dirt_param d in
  (frsh, ty, d)

and subst_args sbst (tys, ds, rs) =
  let tys = Common.map (subst_ty sbst) tys in
  let ds = Common.map sbst.dirt_param ds in
  let rs = Common.map sbst.region_param rs in
  (tys, ds, rs)

(** [identity_subst] is a substitution that makes no changes. *)
let identity_subst =
  {
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

let disable_beautify = ref false

let beautifying_subst () =
  if !disable_beautify then
    identity_subst
  else
    {
      ty_param = refresher (Common.fresh (fun n -> TyParam (Ty_Param n)));
      dirt_param = refresher (Common.fresh (fun n -> Dirt_Param n));
      region_param = refresher (Common.fresh (fun n -> Region_Param n));
      instance_param = refresher (Common.fresh (fun n -> Some (Instance_Param n)));
    }

let refreshing_subst () =
  {
    identity_subst with
    ty_param = (let refresh = refresher fresh_ty_param in fun p -> TyParam (refresh p));
    dirt_param = refresher fresh_dirt_param;
    region_param = refresher fresh_region_param;
  }

let instance_refreshing_subst () =
  {
    identity_subst with
    instance_param = (let refresh = refresher fresh_instance_param in fun i -> Some (refresh i))
  }

let refresh ty =
  let sbst = refreshing_subst () in
  subst_ty sbst ty

let beautify2 ty1 ty2 =
  let sbst = beautifying_subst () in
  let ty1 = subst_ty sbst ty1 in
  let ty2 = subst_ty sbst ty2 in
  (ty1, ty2)
