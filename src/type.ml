(* We need three sorts of parameters, for types, dirt, and regions.
   In order not to confuse them, we define separate types for them.
 *)

type ty_param = Ty_Param of int
type dirt_param = Dirt_Param of int
type region_param = Region_Param of int
type instance_param = Instance_Param of int

let fresh_ty_param = (let f = Common.fresh "type parameter" in fun () -> Ty_Param (f ()))
let fresh_dirt_param = (let f = Common.fresh "dirt parameter" in fun () -> Dirt_Param (f ()))
let fresh_region_param = (let f = Common.fresh "region parameter" in fun () -> Region_Param (f ()))
let fresh_instance_param = (let f = Common.fresh "instance parameter" in fun () -> Instance_Param (f ()))

type params = ty_param list * dirt_param list * region_param list

type args = ty list * dirt list * region list

and ty =
  | Apply of Common.tyname * args
  | Effect of Common.tyname * args * region
  | TyParam of ty_param
  | Basic of string
  | Tuple of ty list
  | Arrow of ty * dirty
  | Handler of handler_ty

and dirty = instance_param list * ty * dirt

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
  | RegionTop
(* probably no need for this:
  | RegionUnion of region list
*)


let empty_dirt = DirtEmpty

type constraints =
  | TypeConstraint of ty * ty * Common.position
  | DirtConstraint of dirt * dirt * Common.position
  | RegionConstraint of region * region * Common.position



(* This type is used when type checking is turned off. Its name
   is syntactically incorrect so that the programmer cannot accidentally
   define it. *)
let universal_ty = Basic "_"
let universal_dirty = ([], Basic "_", DirtEmpty)

let int_ty = Basic "int"
let string_ty = Basic "string"
let bool_ty = Basic "bool"
let float_ty = Basic "float"
let unit_ty = Tuple []
let empty_ty = Apply ("empty", ([], [], []))

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
  | (RegionInstance _ | RegionTop) as rgn -> rgn

let subst_dirt sbst = function
  | DirtEmpty -> DirtEmpty
  | DirtParam d ->
    (match Common.lookup d sbst.subst_dirt with
      | Some drt -> drt
      | None -> DirtParam d)
  | DirtAtom (r, op) -> DirtAtom (subst_region sbst r, op)

let rec subst_args subst (tys, drts, rgns) =
  (List.map (subst_ty subst) tys,
   List.map (subst_dirt subst) drts,
   List.map (subst_region subst) rgns)

(** [subst_ty sbst ty] replaces type parameters in [ty] according to [sbst]. *)
and subst_ty sbst ty =
  let rec subst = function
  | Apply (ty_name, args) -> Apply (ty_name, subst_args sbst args)
  | Effect (ty_name, args, rgn) ->
      Effect (ty_name, subst_args sbst args, subst_region sbst rgn)
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

and subst_dirty sbst (frsh, ty, drt) =
  (frsh, subst_ty sbst ty, subst_dirt sbst drt)


let subst_constraints sbst cstrs = List.map (function
  | TypeConstraint (ty1, ty2, pos) -> TypeConstraint (subst_ty sbst ty1, subst_ty sbst ty2, pos)
  | DirtConstraint (drt1, drt2, pos) -> DirtConstraint (subst_dirt sbst drt1, subst_dirt sbst drt2, pos)
  | RegionConstraint (rgn1, rgn2, pos) -> RegionConstraint (subst_region sbst rgn1, subst_region sbst rgn2, pos)
  ) cstrs

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

(** [free_params ty cstrs] returns three lists of type parameters that occur in [ty].
    Each parameter is listed only once and in order in which it occurs when
    [ty] is displayed. *)
let free_params ty cstrs =
  let (@@@) (xs, ys, zs) (us, vs, ws) = (xs @ us, ys @ vs, zs @ ws) in
  let flatten_map f lst = List.fold_left (@@@) ([], [], []) (List.map f lst) in
  let rec free_ty = function
    | Apply (_, args) -> free_args args
    | Effect (_, args, rgn) -> free_args args @@@ free_region rgn
    | TyParam p -> ([p], [], [])
    | Basic _ -> ([], [], [])
    | Tuple tys -> flatten_map free_ty tys
    | Arrow (ty1, dirty2) -> free_ty ty1 @@@ free_dirty dirty2
    | Handler {value = ty1; finally = ty2} -> free_ty ty1 @@@ free_ty ty2
  and free_dirty (_, ty, drt) =
    free_ty ty @@@ free_dirt drt
  and free_dirt = function
    | DirtEmpty -> ([], [], [])
    | DirtParam p -> ([], [p], [])
    | DirtAtom (rgn, _) -> free_region rgn
  and free_region = function
    | RegionParam r -> ([], [], [r])
    | RegionInstance _ | RegionTop -> ([], [], [])
  and free_args (tys, drts, rgns) =
    flatten_map free_ty tys @@@ flatten_map free_dirt drts @@@ flatten_map free_region rgns
  and free_constraint = function
    | TypeConstraint (ty1, ty2, pos) -> free_ty ty1 @@@ free_ty ty2
    | DirtConstraint (drt1, drt2, pos) -> free_dirt drt1 @@@ free_dirt drt2
    | RegionConstraint (rgn1, rgn2, pos) -> free_region rgn1 @@@ free_region rgn2
  in
  let (xs, ys, zs) = free_ty ty @@@ flatten_map free_constraint cstrs in    
    (Common.uniq xs, Common.uniq ys, Common.uniq zs)

let instance_refreshing_subst isbst = List.map (fun i -> i, Some (fresh_instance_param ())) isbst

let subst_inst_region isbst = function
  | (RegionParam _ | RegionTop) as rgn -> rgn
  | RegionInstance i as rgn -> 
      begin match Common.lookup i isbst with
      | Some (Some j) -> RegionInstance j
      | Some None -> RegionTop
      | None -> rgn
      end

let subst_inst_dirt isbst = function
  | (DirtEmpty | DirtParam _) as drt -> drt
  | DirtAtom (r, op) -> DirtAtom (subst_inst_region isbst r, op)

let rec subst_inst_args isbst (tys, drts, rgns) =
  (List.map (subst_inst_ty isbst) tys,
   List.map (subst_inst_dirt isbst) drts,
   List.map (subst_inst_region isbst) rgns)

(** [subst_inst_ty isbst ty] replaces type parameters in [ty] according to [isbst]. *)
and subst_inst_ty isbst ty =
  let rec subst_inst = function
  | Apply (ty_name, args) -> Apply (ty_name, subst_inst_args isbst args)
  | Effect (ty_name, args, rgn) ->
      Effect (ty_name, subst_inst_args isbst args, subst_inst_region isbst rgn)
  | TyParam p as ty -> ty
  | Basic _ as ty -> ty
  | Tuple tys -> Tuple (List.map subst_inst tys)
  | Arrow (ty1, ty2) -> Arrow (subst_inst ty1, subst_inst_dirty isbst ty2)
  | Handler {value = ty1; finally = ty2} ->
      Handler {value = subst_inst ty1; finally = subst_inst ty2}
  in
  subst_inst ty

and subst_inst_dirty isbst (frsh, ty, drt) =
  let frsh = List.fold_right (fun i frsh ->
    match Common.lookup i isbst with
    | Some (Some j) -> j :: frsh
    | _ -> frsh) frsh [] in
  (frsh, subst_inst_ty isbst ty, subst_inst_dirt isbst drt)

let subst_inst_constraints isbst cstrs = List.map (function
  | TypeConstraint (ty1, ty2, pos) -> TypeConstraint (subst_inst_ty isbst ty1, subst_inst_ty isbst ty2, pos)
  | DirtConstraint (drt1, drt2, pos) -> DirtConstraint (subst_inst_dirt isbst drt1, subst_inst_dirt isbst drt2, pos)
  | RegionConstraint (rgn1, rgn2, pos) -> RegionConstraint (subst_inst_region isbst rgn1, subst_inst_region isbst rgn2, pos)
  ) cstrs

(** [occurs_in_ty p ty] checks if the type parameter [p] occurs in type [ty]. *)
let occurs_in_ty p ty = List.mem p (let (xs, _, _) = free_params ty [] in xs)

(** [fresh_ty ()] gives a type [TyParam p] where [p] is a new type parameter on
    each call. *)
let fresh_ty () = TyParam (fresh_ty_param ())

let fresh_dirt () = DirtParam (fresh_dirt_param ())

let fresh_region () = RegionParam (fresh_region_param ())

let fresh_instance () = RegionInstance (fresh_instance_param ())

(* XXX Should a fresh dirty type have no fresh instances? *)
let fresh_dirty () = ([], fresh_ty (), fresh_dirt ())

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
let refresh params ty cstrs =
  let params', sbst = refreshing_subst params in
    params', subst_ty sbst ty, subst_constraints sbst cstrs

let disable_beautify = ref false

(** [beautify ty] returns a sequential replacement of all type parameters in
    [ty] that can be used for its pretty printing. *)
let beautify ((ps, ds, rs), ty, cstrs) =
  if !disable_beautify then
    ((ps, ds, rs), ty, cstrs)
  else
    let next_ty_param = Common.fresh "beautify_ty" in
    let next_dirt_param = Common.fresh "beautify_dirt" in
    let next_region_param = Common.fresh "beautify_region" in
    let (xs, ys, zs) = free_params ty cstrs in
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
    (subst ps xs_map, subst ds ys_map, subst rs zs_map), subst_ty sbst ty, subst_constraints sbst cstrs


let beautify_dirty (params, ty, cstrs) drt =
  match beautify (params, Arrow (Tuple [], ([], ty, drt)), cstrs) with
  | (ps, Arrow (Tuple [], ([], ty, drt)), cstrs) -> (ps, ty, cstrs), drt
  | _ -> assert false


let beautify2 ty1 ty2 cstrs =
  match beautify (([], [], []), Tuple [ty1; ty2], cstrs) with
  | (ps, Tuple [ty1; ty2], cstrs) -> (ps, ty1, cstrs), (ps, ty2, cstrs)
  | _ -> assert false

