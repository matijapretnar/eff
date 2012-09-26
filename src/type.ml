(* We need three sorts of parameters, for types, dirt, and regions.
   In order not to confuse them, we define separate types for them.
 *)
let refresher fresh =
  let substitution = ref [] in
  fun p ->
    match Common.lookup p !substitution with
    | None ->
        let p' = fresh () in
        substitution := Common.update p p' !substitution;
        p'
    | Some p' -> p'


type ty_param = Ty_Param of int
type dirt_param = Dirt_Param of int
type region_param = Region_Param of int
type instance_param = Instance_Param of int

let fresh_ty_param = (let f = Common.fresh "type parameter" in fun () -> Ty_Param (f ()))
let fresh_dirt_param = (let f = Common.fresh "dirt parameter" in fun () -> Dirt_Param (f ()))
let fresh_region_param = (let f = Common.fresh "region parameter" in fun () -> Region_Param (f ()))
let fresh_instance_param = (let f = Common.fresh "instance parameter" in fun () -> Instance_Param (f ()))

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

type substitution = {
  subst_ty : (ty_param * ty) list ;
  subst_dirt : (dirt_param * dirt_param) list ;
  subst_region : (region_param * region_param) list;
  subst_instance : (instance_param * instance_param option) list
}


let subst_instance_param sbst i =
  match Common.lookup i sbst.subst_instance with
  | Some (Some i') -> Some i'
  | Some None -> None
  | None -> Some i

let subst_option_instance_param sbst = function
  | None -> None
  | Some i -> subst_instance_param sbst i

let subst_region_param sbst r =
  match Common.lookup r sbst.subst_region with
  | Some r' -> r'
  | None -> r

let subst_dirt_param sbst d =
  match Common.lookup d sbst.subst_dirt with
  | Some d' -> d'
  | None -> d

let subst_fresh sbst frsh =
  List.fold_right (fun i acc -> match subst_instance_param sbst i with
    | Some j -> j :: acc | None -> acc) frsh []

let rec subst_args subst (tys, drts, rgns) =
  (List.map (subst_ty subst) tys, List.map (subst_dirt_param subst) drts, List.map (subst_region_param subst) rgns)

(** [subst_ty sbst ty] replaces type parameters in [ty] according to [sbst]. *)
and subst_ty sbst ty =
  let rec subst = function
  | Apply (ty_name, args) -> Apply (ty_name, subst_args sbst args)
  | Effect (ty_name, args, rgn) ->
      Effect (ty_name, subst_args sbst args, subst_region_param sbst rgn)
  | TyParam p as ty ->
    (match Common.lookup p sbst.subst_ty with
      | Some ty -> ty
      | None -> ty)
  | Basic _ as ty -> ty
  | Tuple tys -> Tuple (List.map subst tys)
  | Arrow (ty1, ty2) -> Arrow (subst ty1, subst_dirty sbst ty2)
  | Handler (ty1, ty2) -> Handler (subst ty1, subst ty2)
  in
  subst ty

and subst_dirty sbst (frsh, ty, drt) =
  (subst_fresh sbst frsh, subst_ty sbst ty, subst_dirt_param sbst drt)

(** [identity_subst] is a substitution that makes no changes. *)
let identity_subst = { subst_ty = []; subst_dirt = []; subst_region = []; subst_instance = [] }

(** [compose_subst sbst1 sbst2] returns a substitution that first performs
    [sbst2] and then [sbst1]. *)
let compose_subst
    ({subst_ty = a1 ; subst_dirt = b1 ; subst_region = c1; subst_instance = d1} as sbst1)
     {subst_ty = a2 ; subst_dirt = b2 ; subst_region = c2; subst_instance = d2} =
  { subst_ty = a1 @ Common.assoc_map (subst_ty sbst1) a2 ;
    subst_dirt = b1 @ Common.assoc_map (subst_dirt_param sbst1) b2 ;
    subst_region = c1 @ Common.assoc_map (subst_region_param sbst1) c2 ;
    subst_instance = d1 @ Common.assoc_map (subst_option_instance_param sbst1) d2 ;
  }

(** [free_params ty cnstrs] returns three lists of type parameters that occur in [ty].
    Each parameter is listed only once and in order in which it occurs when
    [ty] is displayed. *)
let free_params ty =
  let (@@@) = Trio.append in
  let rec free_ty = function
    | Apply (_, args) -> free_args args
    | Effect (_, args, r) -> ([], [], [r]) @@@ free_args args
    | TyParam p -> ([p], [], [])
    | Basic _ -> Trio.empty
    | Tuple tys -> Trio.flatten_map free_ty tys
    | Arrow (ty1, dirty2) -> free_ty ty1 @@@ free_dirty dirty2
    | Handler (ty1, ty2) -> free_ty ty1 @@@ free_ty ty2
  and free_dirty (_, ty, d) =
    ([], [d], []) @@@ free_ty ty
  and free_args (tys, drts, rgns) =
    ([], drts, rgns) @@@ Trio.flatten_map free_ty tys
  in
  Trio.uniq (free_ty ty)

(** [occurs_in_ty p ty] checks if the type parameter [p] occurs in type [ty]. *)
let occurs_in_ty p ty = let (xs, _, _) = free_params ty in List.mem p xs

(** [fresh_ty ()] gives a type [TyParam p] where [p] is a new type parameter on
    each call. *)
let fresh_ty () = TyParam (fresh_ty_param ())


(* XXX Should a fresh dirty type have no fresh instances? *)
let fresh_dirty () = ([], fresh_ty (), fresh_dirt_param ())

let refreshing_subst (ps, qs, rs) =
  let ps' = List.map (fun p -> (p, fresh_ty_param ())) ps in
  let qs' = List.map (fun q -> (q, fresh_dirt_param ())) qs in
  let rs' = List.map (fun r -> (r, fresh_region_param ())) rs in
  let sbst = 
    { subst_ty = Common.assoc_map (fun p' -> TyParam p') ps' ;
      subst_dirt = Common.assoc_map (fun q' -> q') qs' ;
      subst_region = Common.assoc_map (fun r' -> r') rs';
      subst_instance = [];
     }
  in
    Trio.snds (ps', qs', rs'), sbst

let instance_refreshing_subst is =
    { identity_subst with subst_instance = List.map (fun i -> (i, Some (fresh_instance_param ()))) is;
     }

(** [refresh (ps,qs,rs) ty] replaces the polymorphic parameters [ps,qs,rs] in [ty] with fresh
    parameters. It returns the  *)
(** [refresh (ps,qs,rs) ty] replaces the polymorphic parameters [ps,qs,rs] in [ty] with fresh
    parameters. It returns the  *)
let global_param_refreshers () =
  (refresher fresh_ty_param, refresher fresh_dirt_param, refresher fresh_region_param)

let refresh_ty (refresh_ty_param, refresh_dirt_param, refresh_region_param) ty =
  let rec refresh_ty = function
  | Apply (ty_name, args) -> Apply (ty_name, refresh_args args)
  | Effect (ty_name, args, r) -> Effect (ty_name, refresh_args args, refresh_region_param r)
  | TyParam p -> TyParam (refresh_ty_param p)
  | Basic _ as ty -> ty
  | Tuple tys -> Tuple (List.map refresh_ty tys)
  | Arrow (ty1, ty2) -> Arrow (refresh_ty ty1, refresh_dirty ty2)
  | Handler (ty1, ty2) -> Handler (refresh_ty ty1, refresh_ty ty2)
  and refresh_args (tys, ds, rs) =
    (List.map refresh_ty tys, List.map refresh_dirt_param ds, List.map refresh_region_param rs)
  and refresh_dirty (frsh, ty, d) = (frsh, refresh_ty ty, refresh_dirt_param d)
  in
  refresh_ty ty

let rec variablize ty =
  let refreshers = global_param_refreshers () in
  refresh_ty refreshers ty

let disable_beautify = ref false

(** [beautify ty] returns a sequential replacement of all type parameters in
    [ty] that can be used for its pretty printing. *)
let beautify ?beautifier ((ps, ds, rs), ty, cnstrs) =
  if !disable_beautify then
     ((ps, ds, rs), ty, cnstrs)
  else
     ((ps, ds, rs), ty, cnstrs)
 (*    let next_ty_param = Common.fresh "beautify_ty"
    and next_dirt_param =  Common.fresh "beautify_dirt"
    and next_region_param = Common.fresh "beautify_region"
    in
    let (xs, ys, zs) = free_params (Trio.empty, ty, cnstrs) in
    let xs_map = List.map (fun p -> (p, Ty_Param (next_ty_param ()))) xs
    and ys_map = List.map (fun q -> (q, Dirt_Param (next_dirt_param ()))) ys
    and zs_map = List.map (fun r -> (r, Region_Param (next_region_param ()))) zs in
    let subst ps ps_map = List.map (fun p ->
      match Common.lookup p ps_map with
      | None -> p
      | Some p' -> p') ps in
    let sbst = 
      { subst_ty = Common.assoc_map (fun p' -> TyParam p') xs_map ;
        subst_dirt = Common.assoc_map (fun q' -> q') ys_map ;
        subst_region = Common.assoc_map (fun r' -> r') zs_map ;
        subst_instance = [] }
    in
    (subst ps xs_map, subst ds ys_map, subst rs zs_map), subst_ty sbst ty, subst_constraints sbst cnstrs *)

let beautify_dirty (params, ty, cnstrs) drt =
  match beautify (params, Arrow (Tuple [], ([], ty, drt)), cnstrs) with
  | (ps, Arrow (Tuple [], ([], ty, drt)), cnstrs) -> (ps, ty, cnstrs), drt
  | _ -> assert false


let beautify2 ty1 ty2 =
  match beautify (Trio.empty, Tuple [ty1; ty2], []) with
  | (ps, Tuple [ty1; ty2], cnstrs) -> (ps, ty1), (ps, ty2)
  | _ -> assert false

