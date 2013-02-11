(* We need three sorts of parameters, for types, dirt, and regions.
   In order not to confuse them, we define separate types for them.
 *)

type ty_param = Ty_Param of int
type presence_param = Presence_Param of int
type region_param = Region_Param of int
type instance_param = Instance_Param of int

let fresh_ty_param = Common.fresh (fun n -> Ty_Param n)
let fresh_presence_param = Common.fresh (fun n -> Presence_Param n)
let fresh_region_param = Common.fresh (fun n -> Region_Param n)
let fresh_instance_param = Common.fresh (fun n -> Instance_Param n)

type ty =
  | Apply of Common.tyname * args
  | Effect of Common.tyname * args * region_param
  | TyParam of ty_param
  | Basic of string
  | Tuple of ty list
  | Arrow of ty * dirty
  | Handler of dirty * dirty

and dirty = ty * dirt

and presence =
  | Region of region_param
  | Without of presence_param * region_param list

and dirt = {
  ops: (Common.opsym, presence_param) Common.assoc;
  rest: presence_param
}

and args = (ty, presence_param, region_param) Trio.t


(* This type is used when type checking is turned off. Its name
   is syntactically incorrect so that the programmer cannot accidentally
   define it. *)
let int_ty = Basic "int"
let string_ty = Basic "string"
let bool_ty = Basic "bool"
let float_ty = Basic "float"
let unit_ty = Tuple []
let empty_ty = Apply ("empty", Trio.empty)

(** [fresh_ty ()] gives a type [TyParam p] where [p] is a new type parameter on
    each call. *)
let fresh_ty () = TyParam (fresh_ty_param ())
let simple_dirt d = { ops = []; rest = d }
let fresh_dirt () = simple_dirt (fresh_presence_param ())
(* XXX Should a fresh dirty type have no fresh instances? *)
let fresh_dirty () = (fresh_ty (), fresh_dirt ())
let universal_ty = Basic "_"
let universal_dirty = (Basic "_", fresh_dirt ())


type substitution = {
  ty_param : ty_param -> ty;
  presence_param : presence_param -> presence_param;
  region_param : region_param -> region_param;
  instance_param : instance_param -> instance_param option;
  presence_rest : presence_param -> dirt;
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
  | Handler ((ty1, drt), drty2) ->
      let ty1 = subst_ty sbst ty1 in
      let drty2 = subst_dirty sbst drty2 in
      Handler ((ty1, subst_dirt sbst drt), drty2)

and subst_presence sbst = function
  | Region r -> Region (sbst.region_param r)
  | Without (p, rs) -> Without (sbst.presence_param p, List.map sbst.region_param rs)

and subst_dirt sbst drt =
  let ops = Common.assoc_map sbst.presence_param drt.ops in
  let { ops = new_ops; rest = new_rest } = sbst.presence_rest drt.rest in
  { ops = new_ops @ ops; rest = new_rest }

and subst_dirty sbst (ty, drt) =
  let ty = subst_ty sbst ty in
  let drt = subst_dirt sbst drt in
  (ty, drt)

and subst_args sbst (tys, drts, rs) =
  let tys = Common.map (subst_ty sbst) tys in
  let drts = Common.map sbst.presence_param drts in
  let rs = Common.map sbst.region_param rs in
  (tys, drts, rs)

(** [identity_subst] is a substitution that makes no changes. *)
let identity_subst =
  {
    ty_param = (fun p -> TyParam p);
    presence_param = Common.id;
    region_param = Common.id;
    instance_param = (fun i -> Some i);
    presence_rest = (fun d -> { ops = []; rest = d })
  }

(** [compose_subst sbst1 sbst2] returns a substitution that first performs
    [sbst2] and then [sbst1]. *)
let compose_subst sbst1 sbst2 =
  {
    ty_param = Common.compose (subst_ty sbst1) sbst2.ty_param;
    presence_param = Common.compose sbst1.presence_param sbst2.presence_param;
    region_param = Common.compose sbst1.region_param sbst2.region_param;
    instance_param = (fun i -> match sbst2.instance_param i with None -> None | Some j -> sbst1.instance_param j);
    presence_rest = Common.compose (subst_dirt sbst1) sbst2.presence_rest;
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

let replace ty =
  let rec replace_ty = function
    | Apply (ty_name, args) -> Apply (ty_name, replace_args args)
    | Effect (ty_name, args, r) ->
        let args = replace_args args in
        Effect (ty_name, args, fresh_region_param ())
    | TyParam p -> TyParam (fresh_ty_param ())
    | Basic _ as ty -> ty
    | Tuple tys -> Tuple (Common.map (replace_ty) tys)
    | Arrow (ty1, drty2) ->
        let ty1 = replace_ty ty1 in
        let drty2 = replace_dirty drty2 in
        Arrow (ty1, drty2)
    | Handler ((ty1, drt), drty2) ->
        let ty1 = replace_ty ty1 in
        let drty2 = replace_dirty drty2 in
        Handler ((ty1, replace_dirt drt), drty2)

  and replace_dirt drt = fresh_dirt ()

  and replace_dirty (ty, drt) =
    let ty = replace_ty ty in
    let drt = replace_dirt drt in
    (ty, drt)

  and replace_args (tys, drts, rs) =
    let tys = Common.map (replace_ty) tys in
    let drts = Common.map (fun _ -> fresh_presence_param ()) drts in
    let rs = Common.map (fun _ -> fresh_region_param ()) rs in
    (tys, drts, rs)
  in
  replace_ty ty

let disable_beautify = ref false

let beautifying_subst () =
  if !disable_beautify then
    identity_subst
  else
    {
      ty_param = refresher (Common.fresh (fun n -> TyParam (Ty_Param n)));
      presence_param = refresher (Common.fresh (fun n -> Presence_Param n));
      region_param = refresher (Common.fresh (fun n -> Region_Param n));
      instance_param = refresher (Common.fresh (fun n -> Some (Instance_Param n)));
      presence_rest = refresher (Common.fresh (fun n -> { ops = []; rest = Presence_Param n }))
    }

let refreshing_subst () =
  {
    identity_subst with
    ty_param = (let refresh = refresher fresh_ty_param in fun p -> TyParam (refresh p));
    presence_param = refresher fresh_presence_param;
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

module Ty = Graph.Make(struct
  type t = ty_param
  type bound = unit
  let inf () () = ()
  let sup () () = ()
  let compare = Pervasives.compare
end)

module Region = Graph.Make(struct
  type t = region_param
  type bound = (instance_param list) option
  let inf rgn1 rgn2 =
    match rgn1, rgn2 with
    | Some insts1, Some insts2 -> Some (List.filter (fun x -> List.mem x insts1) insts2)
    | Some insts, None | None, Some insts -> Some insts
    | None, None -> None
  let sup rgn1 rgn2 =
    match rgn1, rgn2 with
    | Some insts1, Some insts2 -> Some (Common.uniq (insts1 @ insts2))
    | Some insts, None | None, Some insts -> Some insts
    | None, None -> None
  let compare = Pervasives.compare
end)

module Dirt = Graph.Make(struct
  type t = presence_param
  type bound = unit
  let inf () () = ()
  let sup () () = ()
  let compare = Pervasives.compare
end)

type t = {
  ty_graph : Ty.t;
  region_graph : Region.t;
  dirt_graph : Dirt.t;
  dirt_bounds: (presence_param, presence list) Common.assoc;
}

type ty_scheme = (Core.variable, ty) Common.assoc * ty * t
type dirty_scheme = (Core.variable, ty) Common.assoc * dirty * t

let empty = {
  ty_graph = Ty.empty;
  region_graph = Region.empty;
  dirt_graph = Dirt.empty;
  dirt_bounds = [];
}

let remove_ty g x =
  Ty.remove_vertex x g.ty_graph
let remove_dirt g x =
  Dirt.remove_vertex x g.dirt_graph
let get_succ g x =
  Dirt.get_succ x g.dirt_graph

let subst_constraints sbst cnstr = {
  ty_graph = Ty.map (fun p -> match sbst.ty_param p with TyParam q -> q | _ -> assert false) (fun () -> ()) cnstr.ty_graph;
  dirt_graph = Dirt.map sbst.presence_param (fun () -> ()) cnstr.dirt_graph;
  region_graph = Region.map sbst.region_param (fun insts -> Common.option_map (fun insts -> List.map (fun ins -> match sbst.instance_param ins with Some i -> i | None -> assert false) insts) insts) cnstr.region_graph;
  dirt_bounds = Common.assoc_map (List.map (subst_presence sbst)) cnstr.dirt_bounds;
}

let fold_ty f g acc = Ty.fold_edges f g.ty_graph acc
let fold_region f g acc = Region.fold_edges f g.region_graph acc
let fold_dirt f g acc = Dirt.fold_edges f g.dirt_graph acc

let add_region_low_bound i r cstr =
  {cstr with region_graph = Region.add_lower_bound r (Some [i]) cstr.region_graph}

let add_ty_constraint ty1 ty2 cstr =
  {cstr with ty_graph = Ty.add_edge ty1 ty2 cstr.ty_graph}

let add_bound d bnd bounds =
  match Common.lookup d bounds with
  | None -> (d, [bnd]) :: bounds
  | Some bnds ->
      List.fold_right (fun (d', bnds) new_bounds ->
                         if d = d' then (d', bnd :: bnds) :: new_bounds else (d', bnds) :: new_bounds) bounds []

let add_dirt_constraint drt1 drt2 cstr =
  let new_dirt_graph = Dirt.add_edge drt1 drt2 cstr.dirt_graph in
  let new_dirt_bounds =
    match Common.lookup drt1 cstr.dirt_bounds with
    | None -> cstr.dirt_bounds
    | Some bnds1 ->
       List.fold_right (fun bnd -> add_bound drt2 bnd) bnds1 cstr.dirt_bounds
  in
  {cstr with dirt_graph = new_dirt_graph; dirt_bounds = new_dirt_bounds}

let add_region_constraint rgn1 rgn2 cstr =
  {cstr with region_graph = Region.add_edge rgn1 rgn2 cstr.region_graph}


let add_presence_bound d bnd cstr =
  let params = get_succ cstr d in
  {cstr with dirt_bounds = List.fold_right (fun d' -> add_bound d' bnd) (d :: params) cstr.dirt_bounds}

let join_bounds bnds1 bnds2 =
  List.fold_right (fun (d, bds1) bnds2 -> List.fold_right (fun bd1 bnds2 -> add_bound d bd1 bnds2) bds1 bnds2) bnds1 bnds2

let union_bounds bnds1 bnds2 =
  bnds1 @ bnds2

let join_constraints cstr1 cstr2 = 
  {
    ty_graph = Ty.join cstr1.ty_graph cstr2.ty_graph;
    dirt_graph = Dirt.join cstr1.dirt_graph cstr2.dirt_graph;
    region_graph = Region.join cstr1.region_graph cstr2.region_graph;
    dirt_bounds = join_bounds cstr1.dirt_bounds cstr2.dirt_bounds
  }

let join_disjoint_constraints cstr1 cstr2 = 
  {
    ty_graph = Ty.union cstr1.ty_graph cstr2.ty_graph;
    dirt_graph = Dirt.union cstr1.dirt_graph cstr2.dirt_graph;
    region_graph = Region.union cstr1.region_graph cstr2.region_graph;
    dirt_bounds = union_bounds cstr1.dirt_bounds cstr2.dirt_bounds
  }

(* let print grph ppf =
  Print.print ppf "TYPES:@.%t@.REGIONS:@.%t@.DIRT:@.%t@." 
  (Ty.print grph.ty_graph) (Region.print grph.region_graph) (Dirt.print grph.dirt_graph)
 *)
let garbage_collect (pos_ts, neg_ts) (pos_ds, neg_ds) (pos_rs, neg_rs) grph =
  let ty_subst, ty_graph = Ty.collect pos_ts neg_ts grph.ty_graph
  (* and dirt_subst, dirt_graph = Dirt.collect pos_ds neg_ds grph.dirt_graph *)
  and region_subst, region_graph = Region.collect pos_rs neg_rs grph.region_graph
  in
  let sbst = {
    identity_subst with
    ty_param = (fun p -> match Common.lookup p ty_subst with Some q -> TyParam q | None -> TyParam p);
    (* presence_param = (fun p -> match Common.lookup p dirt_subst with Some q -> simple_dirt q | None -> simple_dirt p); *)
    region_param = (fun p -> match Common.lookup p region_subst with Some q -> q | None -> p);
  }
  in
  sbst, {
    ty_graph = ty_graph;
    dirt_graph = grph.dirt_graph;
    region_graph = region_graph;
    dirt_bounds = grph.dirt_bounds
  }

let simplify (pos_ts, neg_ts) (pos_ds, neg_ds) (pos_rs, neg_rs) grph =
  let ty_subst = Ty.simplify pos_ts neg_ts grph.ty_graph
  and dirt_subst = Dirt.simplify pos_ds neg_ds grph.dirt_graph
  and region_subst = Region.simplify pos_rs neg_rs grph.region_graph
  in
  {
    identity_subst with
    ty_param = (fun p -> match Common.lookup p ty_subst with Some q -> TyParam q | None -> TyParam p);
    presence_param = (fun p -> match Common.lookup p dirt_subst with Some q -> q | None -> p);
    region_param = (fun p -> match Common.lookup p region_subst with Some q -> q | None -> p);
  }
