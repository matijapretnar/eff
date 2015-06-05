(** Type inference contexts *)
module C = Common
module T = Type

type tydef =
  | Record of (Common.field, Type.ty) Common.assoc
  | Sum of (Common.label, Type.ty option) Common.assoc
  | Inline of Type.ty

type variance = bool * bool
type params = (Type.ty_param * variance) list * (Type.dirt_param * variance) list * (Type.region_param * variance) list

type tyctx = (Common.tyname, params * tydef) Common.assoc

let initial_tctx : tyctx = [
  ("bool", (Trio.empty, Inline T.bool_ty));
  ("unit", (Trio.empty, Inline T.unit_ty));
  ("int", (Trio.empty, Inline T.int_ty));
  ("string", (Trio.empty, Inline T.string_ty));
  ("float", (Trio.empty, Inline T.float_ty));
  ("list", (let a = Type.fresh_ty_param () in
              (([a, (true, false)], [], []),
                 Sum [(Common.nil, None);
                      (Common.cons, Some (T.Tuple [T.TyParam a; T.Apply ("list", ([T.TyParam a], [], []))]))])));
  ("empty", (Trio.empty, Sum []))
]

let tctx = ref initial_tctx

let reset () =
  tctx := initial_tctx

let subst_tydef sbst =
  let subst = Type.subst_ty sbst in
  function
  | Record tys -> Record (Common.assoc_map subst tys)
  | Sum tys -> Sum (Common.assoc_map (Common.option_map subst) tys)
  | Inline ty -> Inline (subst ty)

(* Lookup type parameters for a given type. *)
let lookup_params ty_name =
  match Common.lookup ty_name !tctx with
    | None -> None
    | Some (params, _) -> Some params

let get_variances ty_name =
  match lookup_params ty_name with
  | None -> assert false (* this function should only be called after types have been checked. *)
  | Some params -> params

let remove_variances (ps, ds, rs) = (List.map fst ps, List.map fst ds, List.map fst rs)

let lookup_tydef ~loc ty_name =
  match Common.lookup ty_name !tctx with
  | None -> Error.typing ~loc "Unknown type %s" ty_name
  | Some (params, tydef) -> (remove_variances params, tydef)

let refreshing_subst (ps, ds, rs) =
  let refresh_ty_param = Type.refresher Type.fresh_ty_param
  and refresh_dirt_param = Type.refresher Type.fresh_dirt_param
  and refresh_region_param = Type.refresher Type.fresh_region_param in
  (List.map refresh_ty_param ps, List.map refresh_dirt_param ds, List.map refresh_region_param rs),
  {
    Type.identity_subst with
    Type.ty_param = (fun p -> Type.TyParam (refresh_ty_param p));
    Type.dirt_param = (fun d -> Type.simple_dirt d);
    Type.region_param = refresh_region_param;
  }

let fresh_tydef ~loc ty_name =
  let (params, tydef) = lookup_tydef ~loc ty_name in
  let params', sbst = refreshing_subst params in
    params', subst_tydef sbst tydef

(** [find_variant lbl] returns the information about the variant type that defines the
    label [lbl]. *)
let find_variant lbl =
  let rec find = function
    | [] -> None
    | (ty_name, (ps, Sum vs)) :: lst ->
      begin match Common.lookup lbl vs with
        | Some us -> Some (ty_name, ps, vs, us)
        | None -> find lst
      end
    | _ :: lst -> find lst
  in
    find !tctx

(** [find_field fld] returns the information about the record type that defines the field
    [fld]. *)
let find_field fld =
  let rec find = function
    | [] -> None
    | (ty_name, (ps, Record flds)) :: lst ->
      if List.mem_assoc fld flds
      then Some (ty_name, ps, flds)
      else find lst
    | _ :: lst -> find lst
  in
    find !tctx


let apply_to_params t (ps, ds, rs) =
  Type.Apply (t, (
    List.map (fun p -> Type.TyParam p) ps, List.map Type.simple_dirt ds, rs
  ))

(** [infer_variant lbl] finds a variant type that defines the label [lbl] and returns it
    with refreshed type parameters and additional information needed for type
    inference. *)
let infer_variant lbl =
  match find_variant lbl with
    | None -> None
    | Some (ty_name, ps, _, u) ->
      let ps', fresh_subst = refreshing_subst (remove_variances ps) in
      let u = C.option_map (T.subst_ty fresh_subst) u in
        Some (apply_to_params ty_name ps', u)


(** [infer_field fld] finds a record type that defines the field [fld] and returns it with
    refreshed type parameters and additional information needed for type inference. *)
let infer_field fld =
  match find_field fld with
    | None -> None
    | Some (ty_name, ps, us) ->
      let ps', fresh_subst = refreshing_subst (remove_variances ps) in
      let us' = C.assoc_map (T.subst_ty fresh_subst) us in
        Some (apply_to_params ty_name ps', (ty_name, us'))


let transparent ~loc ty_name =
    match snd (lookup_tydef ~loc ty_name) with
      | Sum _ | Record _ -> false
      | Inline _ -> true

(* [ty_apply ~loc t lst] applies the type constructor [t] to the given list of arguments. *)
let ty_apply ~loc ty_name (tys, drts, rgns) : tydef =
  let ((ts, ds, rs), ty) = lookup_tydef ~loc ty_name in
  let ty_sbst =
    try List.combine ts tys with
      Invalid_argument "List.combine" -> Error.typing ~loc "Type constructors %s should be applied to %d type arguments" ty_name (List.length ts)
  and dirt_sbst =
    try List.combine ds drts with
      Invalid_argument "List.combine" -> Error.typing ~loc "Type constructors %s should be applied to %d dirt arguments" ty_name (List.length ds)
  and region_sbst =
    try List.combine rs rgns with
      Invalid_argument "List.combine" -> Error.typing ~loc "Type constructors %s should be applied to %d region arguments" ty_name (List.length rs)
  in
  subst_tydef {
    T.identity_subst with
    T.ty_param = (fun p -> Common.lookup_default p ty_sbst (Type.TyParam p));
    T.dirt_param = (fun d -> Common.lookup_default d dirt_sbst (Type.simple_dirt d));
    T.region_param = (fun r -> Common.lookup_default r region_sbst r);
  } ty

(** [check_well_formed ~loc ty] checks that type [ty] is well-formed. *)
let check_well_formed ~loc tydef =
  let rec check = function
  | T.Basic _ | T.TyParam _ -> ()
  | T.Apply (ty_name, (tys, drts, rgns)) ->
    begin match lookup_tydef ~loc ty_name with
      | (ts, ds, rs), (Sum _  | Record _ | Inline _) ->
        let n = List.length ts in
          if List.length tys <> n then
            Error.typing ~loc "The type constructor %s expects %d type arguments" ty_name n;
          let n = List.length ds in
            if List.length drts <> n then
              Error.typing ~loc "The type constructor %s expects %d dirt arguments" ty_name n;
            let n = List.length rs in
              if List.length rgns <> n then
                Error.typing ~loc "The type constructor %s expects %d region arguments" ty_name n
    end
  | T.Arrow (ty1, drty2) -> check ty1; check_dirty drty2
  | T.Tuple tys -> List.iter check tys
  | T.Handler ((ty1, _), drty2) -> check ty1; check_dirty drty2
  and check_dirty (ty, _) = check ty
  in
  match tydef with
  | Record fields ->
      if not (Common.injective fst fields) then
        Error.typing ~loc "Field labels in a record type must be distinct";
      List.iter (fun (_, ty) -> check ty) fields
  | Sum constuctors ->
      if not (Common.injective fst constuctors) then
        Error.typing ~loc "Constructors of a sum type must be distinct";
      List.iter (function (_, None) -> () | (_, Some ty) -> check ty) constuctors
  | Inline ty -> check ty

(** [check_noncyclic ~loc ty] checks that the definition of type [ty] is non-cyclic. *)
let check_noncyclic ~loc =
  let rec check forbidden = function
  | T.Basic _ | T.TyParam _ -> ()
  | T.Apply (t, args) ->
      if List.mem t forbidden then
        Error.typing ~loc "Type definition %s is cyclic." t
      else
        check_tydef (t :: forbidden) (ty_apply ~loc t args)
  | T.Arrow (ty1, (ty2, _)) -> check forbidden ty1; check forbidden ty2
  | T.Tuple tys -> List.iter (check forbidden) tys
  | T.Handler ((ty1, _), (ty2, _)) ->
      check forbidden ty1; check forbidden ty2
  and check_tydef forbidden = function
  | Sum _ -> ()
  | Record fields -> List.iter (fun (_,t) -> check forbidden t) fields
  | Inline ty -> check forbidden ty
  in 
  check_tydef []

(** [check_shadowing ~loc ty] checks that the definition of type [ty] does
    not shadow any field labels, constructors, or operations.

    NB: In eff we _cannot_ allow shadowing because the interpreter uses the original
    field names and label, hence shadowing breaks type safety!
*)
let check_shadowing ~loc = function
  | Record lst ->
    List.iter (fun (f,_) ->
      match find_field f with
        | Some (u, _, _) -> Error.typing ~loc "Record field label %s is already used in type %s" f u
        | None -> ()
    ) lst
  | Sum lst ->
    List.iter (fun (lbl,_) ->
      match find_variant lbl with
        | Some (u, _, _, _) -> Error.typing ~loc "Constructor %s is already used in type %s" lbl u
        | None -> ()
    ) lst
  | Inline _ -> ()

let extend_with_variances ~loc tydefs =
  let prepare_variance lst = List.map (fun p -> (p, (ref false, ref false))) lst in
  let prepare_variances ((ps, ds, rs), def) =
    ((prepare_variance ps, prepare_variance ds, prepare_variance rs), def) in
  let prepared_tydefs = Common.assoc_map prepare_variances tydefs in
  let set_variances (ty_name, ((ps, ds, rs), def)) =
    let rec ty posi nega = function
      | T.Basic _ -> ()
      | T.TyParam p ->
          begin match Common.lookup p ps with
          | None -> assert false
          | Some (posvar, negvar) ->
              posvar := !posvar || posi;
              negvar := !negvar || nega
          end
      | T.Apply (t, (tys, drts, rgns)) ->
          begin match Common.lookup t !tctx with
          | None ->
              (* XXX Here, we should do some sort of an equivalence relation algorithm to compute better variances. *)
              List.iter (ty true true) tys;
              List.iter (dirt true true) drts;
              List.iter (region_param true true) rgns
          | Some ((ps, ds, rs), _) ->
              if List.length ps != List.length tys then
                Error.typing ~loc "The type constructor %s expects %d type arguments" t (List.length ps);
              if List.length ds != List.length drts then
                Error.typing ~loc "The type constructor %s expects %d dirt arguments" t (List.length drts);
              if List.length rs != List.length rgns then
                Error.typing ~loc "The type constructor %s expects %d region arguments" t (List.length rgns);
              if posi then begin
                List.iter2 (fun (_, (posi', nega')) -> ty posi' nega') ps tys;
                List.iter2 (fun (_, (posi', nega')) -> dirt posi' nega') ds drts;
                List.iter2 (fun (_, (posi', nega')) -> region_param posi' nega') rs rgns
              end;
              if nega then begin
                List.iter2 (fun (_, (posi', nega')) -> ty nega' posi') ps tys;
                List.iter2 (fun (_, (posi', nega')) -> dirt nega' posi') ds drts;
                List.iter2 (fun (_, (posi', nega')) -> region_param nega' posi') rs rgns
              end
          end
      | T.Arrow (ty1, (ty2, drt)) ->
          ty nega posi ty1;
          ty posi nega ty2;
          dirt posi nega drt
      | T.Tuple tys -> List.iter (ty posi nega) tys
      | T.Handler ((ty1, drt1), (ty2, drt2)) ->
          ty nega posi ty1;
          ty posi nega ty2;
          dirt nega posi drt1;
          dirt posi nega drt2
    and dirt posi nega drt =
      List.iter (fun (_, prs) -> region_param posi nega prs) drt.Type.ops;
      dirt_param posi nega drt.Type.rest
    and dirt_param posi nega d =
      begin match Common.lookup d ds with
      | None -> assert false
      | Some (posvar, negvar) ->
          posvar := !posvar || posi;
          negvar := !negvar || nega
      end
    and region_param posi nega r =
      begin match Common.lookup r rs with
      | None -> assert false
      | Some (posvar, negvar) ->
          posvar := !posvar || posi;
          negvar := !negvar || nega
      end
    in match def with
      | Record tys -> List.iter (fun (_, t) -> ty true false t) tys
      | Sum tys -> List.iter (function (_, Some t) -> ty true false t | (_, None) -> ()) tys
      | Inline t -> ty true false t
  in
  List.iter set_variances prepared_tydefs;
  let unref lst = Common.assoc_map (fun (ref1, ref2) -> (!ref1, !ref2)) lst in
  let extend_with_variance (ty_name, ((ps, ds, rs), def)) =
    (ty_name, ((unref ps, unref ds, unref rs), def))
  in
  List.map extend_with_variance prepared_tydefs

(** [extend_tydefs ~loc tydefs] checks that the simulatenous type definitions [tydefs] are
    well-formed and returns the extended context. *)
let extend_tydefs ~loc tydefs =
  (* We wish we wrote this in eff, where we could have transactional memory. *)
  let tctx_orig = !tctx in
  let tydefs = extend_with_variances ~loc tydefs in
  let extend_tydef ((tyname, (_, ty)) as tydef) =
    if List.mem_assoc tyname !tctx then Error.typing ~loc "Type %s is already defined" tyname ;
    check_shadowing ~loc ty ;
    tctx := tydef :: !tctx
  in 
    try 
      List.iter extend_tydef tydefs ;
      List.iter (fun (_, (_, ty)) -> check_well_formed ~loc ty) tydefs;
      List.iter (fun (_, (_, ty)) -> check_noncyclic ~loc ty) tydefs
    with e ->
      tctx := tctx_orig ; raise e (* reinstate the context on error *)
