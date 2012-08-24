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

and region =
  | RegionParam of region_param
  | RegionAtom of instance

and instance =
  | InstanceParam of instance_param
  | InstanceTop

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
  subst_region : (region_param * region) list;
  subst_instance : (instance_param * instance) list
}

let subst_instance sbst = function
  | InstanceParam i as inst ->
      begin match Common.lookup i sbst.subst_instance with
      | Some inst' -> inst'
      | None -> inst
      end
  | InstanceTop -> InstanceTop  

let subst_region sbst = function
  | RegionParam r ->
    (match Common.lookup r sbst.subst_region with
      | Some rgn -> rgn
      | None -> RegionParam r)    
  | RegionAtom inst -> RegionAtom (subst_instance sbst inst)

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


let subst_constraints sbst cnstrs = List.map (function
  | TypeConstraint (ty1, ty2, pos) -> TypeConstraint (subst_ty sbst ty1, subst_ty sbst ty2, pos)
  | DirtConstraint (drt1, drt2, pos) -> DirtConstraint (subst_dirt sbst drt1, subst_dirt sbst drt2, pos)
  | RegionConstraint (rgn1, rgn2, pos) -> RegionConstraint (subst_region sbst rgn1, subst_region sbst rgn2, pos)
  ) cnstrs

(** [identity_subst] is a substitution that makes no changes. *)
let identity_subst = { subst_ty = []; subst_dirt = []; subst_region = []; subst_instance = [] }

(** [compose_subst sbst1 sbst2] returns a substitution that first performs
    [sbst2] and then [sbst1]. *)
let compose_subst
    ({subst_ty = a1 ; subst_dirt = b1 ; subst_region = c1; subst_instance = d1} as sbst1)
     {subst_ty = a2 ; subst_dirt = b2 ; subst_region = c2; subst_instance = d2} =
  { subst_ty = a1 @ Common.assoc_map (subst_ty sbst1) a2 ;
    subst_dirt = b1 @ Common.assoc_map (subst_dirt sbst1) b2 ;
    subst_region = c1 @ Common.assoc_map (subst_region sbst1) c2 ;
    subst_instance = d1 @ Common.assoc_map (subst_instance sbst1) d2 ;
  }

(** [free_params ty cnstrs] returns three lists of type parameters that occur in [ty].
    Each parameter is listed only once and in order in which it occurs when
    [ty] is displayed. *)
let free_params ty cnstrs =
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
    | RegionAtom _ -> ([], [], [])
  and free_args (tys, drts, rgns) =
    flatten_map free_ty tys @@@ flatten_map free_dirt drts @@@ flatten_map free_region rgns
  and free_constraint = function
    | TypeConstraint (ty1, ty2, pos) -> free_ty ty1 @@@ free_ty ty2
    | DirtConstraint (drt1, drt2, pos) -> free_dirt drt1 @@@ free_dirt drt2
    | RegionConstraint (rgn1, rgn2, pos) -> free_region rgn1 @@@ free_region rgn2
  in
  let (xs, ys, zs) = free_ty ty @@@ flatten_map free_constraint cnstrs in    
    (Common.uniq xs, Common.uniq ys, Common.uniq zs)


let pos_neg_params ty =
  let (@@@) (xs, ys, zs) (us, vs, ws) = (xs @ us, ys @ vs, zs @ ws) in
  let flatten_map f lst = List.fold_left (@@@) ([], [], []) (List.map f lst) in
  let pos_params is_pos ty =
    let rec pos_ty is_pos = function
      | Apply (_, args) -> pos_args is_pos args
      | Effect (_, args, rgn) -> pos_args is_pos args @@@ pos_region is_pos rgn
      | TyParam p -> ((if is_pos then [p] else []), [], [])
      | Basic _ -> ([], [], [])
      | Tuple tys -> flatten_map (pos_ty is_pos) tys
      | Arrow (ty1, dirty2) -> pos_ty (not is_pos) ty1 @@@ pos_dirty is_pos dirty2
      | Handler {value = ty1; finally = ty2} -> pos_ty (not is_pos) ty1 @@@ pos_ty is_pos ty2
    and pos_dirty is_pos (_, ty, drt) =
      pos_ty is_pos ty @@@ pos_dirt is_pos drt
    and pos_dirt is_pos = function
      | DirtEmpty -> ([], [], [])
      | DirtParam p -> ([], (if is_pos then [p] else []), [])
      | DirtAtom (rgn, _) -> pos_region is_pos rgn
    and pos_region is_pos = function
      | RegionParam r -> ([], [], if is_pos then [r] else [])
      | RegionAtom _ -> ([], [], [])
    and pos_args is_pos (tys, drts, rgns) =
      flatten_map (pos_ty is_pos) tys @@@ flatten_map (pos_dirt is_pos) drts @@@ flatten_map (pos_region is_pos) rgns
    in
    let (xs, ys, zs) = pos_ty is_pos ty in    
      (Common.uniq xs, Common.uniq ys, Common.uniq zs)
  in
  pos_params true ty, pos_params false ty

(** [occurs_in_ty p ty] checks if the type parameter [p] occurs in type [ty]. *)
let occurs_in_ty p ty = List.mem p (let (xs, _, _) = free_params ty [] in xs)

(** [fresh_ty ()] gives a type [TyParam p] where [p] is a new type parameter on
    each call. *)
let fresh_ty () = TyParam (fresh_ty_param ())

let fresh_dirt () = DirtParam (fresh_dirt_param ())

let fresh_region () = RegionParam (fresh_region_param ())

let fresh_instance () = RegionAtom (InstanceParam (fresh_instance_param ()))

(* XXX Should a fresh dirty type have no fresh instances? *)
let fresh_dirty () = ([], fresh_ty (), fresh_dirt ())

let rec variablize = function
  | Apply (ty_name, args) -> Apply (ty_name, variablize_args args)
  | Effect (ty_name, args, rgn) ->
      Effect (ty_name, variablize_args args, fresh_region ())
  | TyParam _ -> fresh_ty ()
  | Basic _ as ty -> ty
  | Tuple tys -> Tuple (List.map variablize tys)
  | Arrow (ty1, ty2) -> Arrow (variablize ty1, variablize_dirty ty2)
  | Handler {value = ty1; finally = ty2} ->
      Handler {value = variablize ty1; finally = variablize ty2}

and variablize_dirty (frsh, ty, drt) =
  (* XXX What to do about fresh instances *)
  ([], variablize ty, fresh_dirt ())

and variablize_args (tys, drts, rgns) =
  (List.map variablize tys, List.map (fun _ -> fresh_dirt ()) drts, List.map (fun _ -> fresh_region ()) rgns)

let refreshing_subst (ps, qs, rs) =
  let ps' = List.map (fun p -> (p, fresh_ty_param ())) ps in
  let qs' = List.map (fun q -> (q, fresh_dirt_param ())) qs in
  let rs' = List.map (fun r -> (r, fresh_region_param ())) rs in
  let sbst = 
    { subst_ty = Common.assoc_map (fun p' -> TyParam p') ps' ;
      subst_dirt = Common.assoc_map (fun q' -> DirtParam q') qs' ;
      subst_region = Common.assoc_map (fun r' -> RegionParam r') rs';
      subst_instance = [];
     }
  in
    (List.map snd ps', List.map snd qs', List.map snd rs'), sbst

(** [refresh (ps,qs,rs) ty] replaces the polymorphic parameters [ps,qs,rs] in [ty] with fresh
    parameters. It returns the  *)
let refresh params ty cnstrs =
  let params', sbst = refreshing_subst params in
    params', subst_ty sbst ty, subst_constraints sbst cnstrs

let disable_beautify = ref false

(** [beautify ty] returns a sequential replacement of all type parameters in
    [ty] that can be used for its pretty printing. *)
let beautify ((ps, ds, rs), ty, cnstrs) =
  if !disable_beautify then
    ((ps, ds, rs), ty, cnstrs)
  else
    let next_ty_param = Common.fresh "beautify_ty"
    and next_dirt_param =  Common.fresh "beautify_dirt"
    and next_region_param = Common.fresh "beautify_region"
    in
    let (xs, ys, zs) = free_params ty cnstrs in
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
        subst_region = Common.assoc_map (fun r' -> RegionParam r') zs_map ;
        subst_instance = [] }
    in
    (subst ps xs_map, subst ds ys_map, subst rs zs_map), subst_ty sbst ty, subst_constraints sbst cnstrs

let beautify_dirty (params, ty, cnstrs) drt =
  match beautify (params, Arrow (Tuple [], ([], ty, drt)), cnstrs) with
  | (ps, Arrow (Tuple [], ([], ty, drt)), cnstrs) -> (ps, ty, cnstrs), drt
  | _ -> assert false


let beautify2 ty1 ty2 =
  match beautify (([], [], []), Tuple [ty1; ty2], []) with
  | (ps, Tuple [ty1; ty2], cnstrs) -> (ps, ty1), (ps, ty2)
  | _ -> assert false

