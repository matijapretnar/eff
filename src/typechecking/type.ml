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
  | Handler of dirty * dirty

and dirty = ty * dirt

and dirt = {
  ops: (Common.opsym, region_param) Common.assoc;
  rest: dirt_param
}

and args = (ty, dirt, region_param) Trio.t


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
let fresh_dirt () = simple_dirt (fresh_dirt_param ())
let fresh_dirty () = (fresh_ty (), fresh_dirt ())

(* These types are used when type checking is turned off. Their names
   are syntactically incorrect so that the programmer cannot accidentally
   define it. *)
let universal_ty = Basic "_"
let universal_dirty = (Basic "_", fresh_dirt ())


type substitution = {
  ty_param : ty_param -> ty;
  dirt_param : dirt_param -> dirt;
  region_param : region_param -> region_param;
  instance_param : instance_param -> instance_param;
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
  | Arrow (ty1, (ty2, drt)) ->
      let ty1 = subst_ty sbst ty1 in
      let drt = subst_dirt sbst drt in
      let ty2 = subst_ty sbst ty2 in
      Arrow (ty1, (ty2, drt))
  | Handler (drty1, drty2) ->
      let drty1 = subst_dirty sbst drty1 in
      let drty2 = subst_dirty sbst drty2 in
      Handler (drty1, drty2)

and subst_dirt sbst drt =
  let ops = Common.assoc_map sbst.region_param drt.ops in
  let { ops = new_ops; rest = new_rest } = sbst.dirt_param drt.rest in
  { ops = new_ops @ ops; rest = new_rest }

and subst_dirty sbst (ty, drt) =
  let ty = subst_ty sbst ty in
  let drt = subst_dirt sbst drt in
  (ty, drt)

and subst_args sbst (tys, drts, rs) =
  let tys = Common.map (subst_ty sbst) tys in
  let drts = Common.map (subst_dirt sbst) drts in
  let rs = Common.map sbst.region_param rs in
  (tys, drts, rs)

(** [identity_subst] is a substitution that makes no changes. *)
let identity_subst =
  {
    ty_param = (fun p -> TyParam p);
    dirt_param = (fun d -> { ops = []; rest = d });
    region_param = Common.id;
    instance_param = Common.id;
  }

(** [compose_subst sbst1 sbst2] returns a substitution that first performs
    [sbst2] and then [sbst1]. *)
let compose_subst sbst1 sbst2 =
  {
    ty_param = Common.compose (subst_ty sbst1) sbst2.ty_param;
    dirt_param = Common.compose (subst_dirt sbst1) sbst2.dirt_param;
    region_param = Common.compose sbst1.region_param sbst2.region_param;
    instance_param = Common.compose sbst2.instance_param sbst1.instance_param;
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

let beautifying_subst () =
  if !Config.disable_beautify then
    identity_subst
  else
    {
      ty_param = refresher (Common.fresh (fun n -> TyParam (Ty_Param n)));
      dirt_param = refresher (Common.fresh (fun n -> { ops = []; rest = Dirt_Param n }));
      region_param = refresher (Common.fresh (fun n -> Region_Param n));
      instance_param = refresher (Common.fresh (fun n -> Instance_Param n));
    }

let refreshing_subst () =
  {
    identity_subst with
    ty_param = (let refresh = refresher fresh_ty_param in fun p -> TyParam (refresh p));
    dirt_param = (let refresh = refresher fresh_dirt_param in fun p -> { ops = []; rest = refresh p});
    region_param = refresher fresh_region_param;
  }

let refresh ty =
  let sbst = refreshing_subst () in
  subst_ty sbst ty

let (@@@) = Trio.append

let for_parameters get_params is_pos ps lst =
  List.fold_right2 (fun (_, (cov, contra)) el params ->
                      let params = if cov then get_params is_pos el @@@ params else params in
                      if contra then get_params (not is_pos) el @@@ params else params) ps lst Trio.empty

let pos_neg_params get_variances ty =
  let rec pos_ty is_pos = function
  | Apply (ty_name, args) -> pos_args is_pos ty_name args
  | Effect (ty_name, args, rgn) -> pos_args is_pos ty_name args @@@ pos_region_param is_pos rgn
  | TyParam p -> ((if is_pos then [p] else []), [], [])
  | Basic _ -> Trio.empty
  | Tuple tys -> Trio.flatten_map (pos_ty is_pos) tys
  | Arrow (ty1, drty2) -> pos_ty (not is_pos) ty1 @@@ pos_dirty is_pos drty2
  | Handler ((ty1, drt1), drty2) -> pos_ty (not is_pos) ty1 @@@ pos_dirt (not is_pos) drt1 @@@ pos_dirty is_pos drty2
  and pos_dirty is_pos (ty, drt) =
    pos_ty is_pos ty @@@ pos_dirt is_pos drt
  and pos_dirt is_pos drt =
    pos_dirt_param is_pos drt.rest @@@ Trio.flatten_map (fun (_, dt) -> pos_region_param is_pos dt) drt.ops
  and pos_dirt_param is_pos p =
    ([], (if is_pos then [p] else []), [])
  and pos_region_param is_pos r =
    ([], [], if is_pos then [r] else [])
  and pos_args is_pos ty_name (tys, drts, rgns) =
    let (ps, ds, rs) = get_variances ty_name in
    for_parameters pos_ty is_pos ps tys @@@
    for_parameters pos_dirt is_pos ds drts @@@
    for_parameters pos_region_param is_pos rs rgns
  in
  Trio.uniq (pos_ty true ty), Trio.uniq (pos_ty false ty)

let print_region_param ?(non_poly=Trio.empty) ((Region_Param k) as p) ppf =
  let (_, _, rs) = non_poly in
  Symbols.region_param k (List.mem p rs) ppf

let print_dirt_param ?(non_poly=Trio.empty) ((Dirt_Param k) as p) ppf =
  let (_, ds, _) = non_poly in
  Symbols.dirt_param k (List.mem p ds) ppf

let dirt_bound ?non_poly r_ops =
  Print.sequence ", " (fun (op, dt) ppf -> Print.print ppf "%s:%t" op (print_region_param dt)) r_ops

let print_dirt ?(non_poly=Trio.empty) ~show_dirt_param drt ppf =
  match drt.ops with
  | [] ->
    begin match show_dirt_param drt.rest with
    | Some f -> f ppf
    | None -> ()
    end
  | _ ->
    begin match show_dirt_param drt.rest with
    | Some f -> Print.print ppf "{%t|%t}" (dirt_bound ~non_poly drt.ops) f
    | None -> Print.print ppf "{%t}" (dirt_bound ~non_poly drt.ops)
    end


let print_ty_param ?(non_poly=Trio.empty) skeletons p ppf =
  let (ps, _, _) = non_poly in
  let Ty_Param k = p in 
  let rec get_skel_id skel id = function
  | [] -> k - List.length (List.flatten skeletons) + List.length skeletons, None
  | [] :: skels -> get_skel_id (succ skel) 0 skels
  | (Ty_Param l :: xs) :: _ when k == l ->
      if id = 0 && List.length xs = 0 then skel, None else skel, Some (id + 1)
  | (_ :: xs) :: skels -> get_skel_id skel (succ id) (xs :: skels)
  in
  let skel, id = get_skel_id 0 0 skeletons in
  (* let id = if !effects then id else None in *)
  let id = None in
  Symbols.ty_param skel id (List.mem p ps) ppf

let print_instance_param (Instance_Param i) ppf =
  Print.print ppf "#%d" i

let show_dirt show_dirt_param drt = drt.ops != [] || (show_dirt_param drt.rest != None)

let rec print ?(non_poly=Trio.empty) ?(show_dirt_param=fun d -> Some (print_dirt_param ~non_poly d)) skeletons t ppf =
  let rec ty ?max_level t ppf =
    let print ?at_level = Print.print ?max_level ?at_level ppf in
    match t with
    | Arrow (t1, (t2, drt)) ->
        if !Config.effect_annotations && show_dirt show_dirt_param drt then
          print ~at_level:5 "@[%t -%t%s@ %t@]"
            (ty ~max_level:4 t1)
            (print_dirt ~non_poly ~show_dirt_param drt)
            (Symbols.short_arrow ())
            (ty ~max_level:5 t2)
        else
          print ~at_level:5 "@[%t@ %s@ %t@]" (ty ~max_level:4 t1) (Symbols.arrow ()) (ty ~max_level:5 t2)
    | Basic b -> print "%s" b
    | Apply (t, (lst, _, _)) ->
      begin match lst with
        | [] -> print "%s" t
        | [s] -> print ~at_level:1 "%t %s" (ty ~max_level:1 s) t
        | ts -> print ~at_level:1 "(%t) %s" (Print.sequence ", " ty ts) t
      end
    | Effect (t, (lst, _, _), rgn) ->
        if !Config.effect_annotations then
          begin match lst with
            | [] -> print "%s[%t]" t (print_region_param ~non_poly rgn)
            | [s] -> print ~at_level:1 "%t %s[%t]" (ty ~max_level:1 s) t (print_region_param ~non_poly rgn)
            | ts -> print ~at_level:1 "(%t) %s[%t]" (Print.sequence ", " ty ts) t (print_region_param ~non_poly rgn)
          end
        else
          begin match lst with
            | [] -> print "%s" t
            | [s] -> print ~at_level:1 "%t %s" (ty ~max_level:1 s) t
            | ts -> print ~at_level:1 "(%t) %s" (Print.sequence ", " ty ts) t
          end
    | TyParam p -> print_ty_param ~non_poly skeletons p ppf
    | Tuple [] -> print "unit"
    | Tuple ts -> print ~at_level:2 "@[<hov>%t@]" (Print.sequence (Symbols.times ()) (ty ~max_level:1) ts)
    | Handler ((t1, drt1), (t2, drt2)) ->
        if !Config.effect_annotations then
          print ~at_level:6 "%t ! %t %s@ %t ! %t"
            (ty ~max_level:4 t1)
            (print_dirt ~non_poly ~show_dirt_param drt1)
            (Symbols.handler_arrow ())
            (ty ~max_level:4 t2)
            (print_dirt ~non_poly ~show_dirt_param drt2)
        else
          print ~at_level:6 "%t %s@ %t" (ty ~max_level:4 t1) (Symbols.handler_arrow ()) (ty ~max_level:4 t2)
  in ty t ppf
