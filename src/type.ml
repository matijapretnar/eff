(* We need three sorts of parameters, for types, dirt, and regions.
   In order not to confuse them, we define separate types for them.
 *)

type ty_param = Ty_Param of int
type dirt_param = Dirt_Param of int
type region_param = Region_Param of int
type instance_param = Instance_Param of int

type params = ty_param list * dirt_param list * region_param list

let fresh_ty_param = (let f = Common.fresh "type parameter" in fun () -> Ty_Param (f ()))
let fresh_dirt_param = (let f = Common.fresh "dirt parameter" in fun () -> Dirt_Param (f ()))
let fresh_region_param = (let f = Common.fresh "region parameter" in fun () -> Region_Param (f ()))
let fresh_instance_param = (let f = Common.fresh "instance parameter" in fun () -> Instance_Param (f ()))

type ty =
  | Apply of Common.tyname * ty list
  | TyParam of ty_param
  | Basic of string
  | Tuple of ty list
  | Arrow of ty * dirty
  | Handler of handler_ty

and dirty = ty * dirt

and handler_ty = {
  value: ty; (* the type of the _argument_ of value *)
  finally: ty; (* the return type of finally *)
}

and dirt =
  | DirtParam of dirt_param
  | DirtAtom of region * Common.opsym
  | DirtEmpty
(* probably no need for this
  | DirtUnion of dirt list
*)

and region =
  | RegionParam of region_param
  | RegionInstance of instance_param
(* probably no need for this:
  | RegionUnion of region list
  | RegionTop
*)

let empty_dirt = DirtEmpty

(* This type is used when type checking is turned off. Its name
   is syntactically incorrect so that the programmer cannot accidentally
   define it. *)
let universal_ty = Basic "_"
let universal_dirty = (Basic "_", DirtEmpty)

let int_ty = Basic "int"
let string_ty = Basic "string"
let bool_ty = Basic "bool"
let float_ty = Basic "float"
let unit_ty = Tuple []
let empty_ty = Apply ("empty", [])

type substitution = {
  subst_ty : (ty_param * ty) list ;
  subst_dirt : (dirt_param * dirt) list ;
  subst_region : (region_param * region) list
}

let subst_region sbst = function
  | RegionParam r ->
    (match Common.lookup r sbst.subst_region with
      | Some rgn -> rgn
      | None -> RegionParam r)    
  | (RegionInstance _) as rgn -> rgn

let subst_dirt sbst = function
  | DirtEmpty -> DirtEmpty
  | DirtParam d ->
    (match Common.lookup d sbst.subst_dirt with
      | Some drt -> drt
      | None -> DirtParam d)
  | DirtAtom (r, op) -> DirtAtom (subst_region sbst r, op)

(** [subst_ty sbst ty] replaces type parameters in [ty] according to [sbst]. *)
let rec subst_ty sbst ty =
  let rec subst = function
  | Apply (ty_name, tys) -> Apply (ty_name, List.map subst tys)
  | TyParam p as ty ->
    (match Common.lookup p sbst.subst_ty with
      | Some ty -> ty
      | None -> ty)
  | Basic _ as ty -> ty
  | Tuple tys -> Tuple (List.map subst tys)
  | Arrow (ty1, ty2) -> Arrow (subst ty1, subst_dirty sbst ty2)
  | Handler {value = ty1; finally = ty2} ->
      Handler {value = subst ty1; finally = subst ty2}
  in
  subst ty

and subst_dirty sbst (ty, drt) =
  (subst_ty sbst ty, subst_dirt sbst drt)

(** [identity_subst] is a substitution that makes no changes. *)
let identity_subst = { subst_ty = []; subst_dirt = []; subst_region = [] }

(** [compose_subst sbst1 sbst2] returns a substitution that first performs
    [sbst2] and then [sbst1]. *)
let compose_subst
    ({subst_ty = a1 ; subst_dirt = b1 ; subst_region = c1} as sbst1)
     {subst_ty = a2 ; subst_dirt = b2 ; subst_region = c2} =
  { subst_ty = a1 @ Common.assoc_map (subst_ty sbst1) a2 ;
    subst_dirt = b1 @ Common.assoc_map (subst_dirt sbst1) b2 ;
    subst_region = c1 @ Common.assoc_map (subst_region sbst1) c2 }

(** [free_params ty] returns three lists of type parameters that occur in [ty].
    Each parameter is listed only once and in order in which it occurs when
    [ty] is displayed. *)
let free_params ty =
  let (@@@) (xs, ys, zs) (us, vs, ws) = (xs @ us, ys @ vs, zs @ ws) in
  let flatten_map f lst = List.fold_left (@@@) ([], [], []) (List.map f lst) in
  let rec free_ty = function
    | Apply (_, tys) -> flatten_map free_ty tys
    | TyParam p -> ([p], [], [])
    | Basic _ -> ([], [], [])
    | Tuple tys -> flatten_map free_ty tys
    | Arrow (ty1, dirty2) -> free_ty ty1 @@@ free_dirty dirty2
    | Handler {value = ty1; finally = ty2} -> free_ty ty1 @@@ free_ty ty2
  and free_dirty (ty, drt) =
    let (xs, ys, zs) = free_ty ty in
    let (vs, ws) = free_dirt drt in
      (xs, ys @ vs, zs @ ws)
  and free_dirt = function
    | DirtEmpty -> ([], [])
    | DirtParam p -> ([p], [])
    | DirtAtom (rgn, _) -> ([], free_region rgn)
  and free_region = function
    | RegionParam r -> [r]
    | RegionInstance _ -> []
  in
  let (xs, ys, zs) = free_ty ty in    
    (Common.uniq xs, Common.uniq ys, Common.uniq zs)

(** [occurs_in_ty p ty] checks if the type parameter [p] occurs in type [ty]. *)
let occurs_in_ty p ty = List.mem p (let (xs, _, _) = free_params ty in xs)

(** [fresh_ty ()] gives a type [TyParam p] where [p] is a new type parameter on
    each call. *)
let fresh_ty () = TyParam (fresh_ty_param ())

let fresh_dirt () = DirtParam (fresh_dirt_param ())

let fresh_region () = RegionParam (fresh_region_param ())

let fresh_dirty () = (fresh_ty (), fresh_dirt ())

let refreshing_subst (ps, qs, rs) =
  let ps' = List.map (fun p -> (p, fresh_ty_param ())) ps in
  let qs' = List.map (fun q -> (q, fresh_dirt_param ())) qs in
  let rs' = List.map (fun r -> (r, fresh_region_param ())) rs in
  let sbst = 
    { subst_ty = Common.assoc_map (fun p' -> TyParam p') ps' ;
      subst_dirt = Common.assoc_map (fun q' -> DirtParam q') qs' ;
      subst_region = Common.assoc_map (fun r' -> RegionParam r') rs' }
  in
    (List.map snd ps', List.map snd qs', List.map snd rs'), sbst

(** [refresh (ps,qs,rs) ty] replaces the polymorphic parameters [ps,qs,rs] in [ty] with fresh
    parameters. It returns the  *)
let refresh params ty =
  let params', sbst = refreshing_subst params in
    params', subst_ty sbst ty

(** [beautify ty] returns a sequential replacement of all type parameters in
    [ty] that can be used for its pretty printing. *)
let beautify ((ps, ds, rs), ty) =
  let next_ty_param = Common.fresh "beautify_ty" in
  let next_dirt_param = Common.fresh "beautify_dirt" in
  let next_region_param = Common.fresh "beautify_region" in
  let (xs, ys, zs) = free_params ty in
  let xs_map = List.map (fun p -> (p, Ty_Param (next_ty_param ()))) xs
  and ys_map = List.map (fun q -> (q, Dirt_Param (next_dirt_param ()))) ys
  and zs_map = List.map (fun r -> (r, Region_Param (next_region_param ()))) zs in
  let subst ps ps_map = List.map (fun p ->
    match Common.lookup p ps_map with
    | None -> p
    | Some p' -> p') ps in
  let sbst = 
    { subst_ty = Common.assoc_map (fun p' -> TyParam p') xs_map ;
      subst_dirt = Common.assoc_map (fun q' -> DirtParam q') ys_map ;
      subst_region = Common.assoc_map (fun r' -> RegionParam r') zs_map }
  in
  (subst ps xs_map, subst ds ys_map, subst rs zs_map), subst_ty sbst ty

let beautify2 ty1 ty2 =
  match beautify (([], [], []), Tuple [ty1; ty2]) with
  | (ps, Tuple [ty1; ty2]) -> (ps, ty1), (ps, ty2)
  | _ -> assert false

