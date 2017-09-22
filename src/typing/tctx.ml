(** Type inference contexts *)
module T = Type

type tydef =
  | Record of (Common.field, Type.ty) Common.assoc
  | Sum of (Common.label, Type.ty option) Common.assoc
  | Inline of Type.ty

type variance = bool * bool
type params = (Params.ty_param * variance) list * (Params.dirt_param * variance) list

type tyctx = (Common.tyname, params * tydef) Common.assoc

let initial_tctx : tyctx = [
  ("bool", (([], []), Inline T.bool_ty));
  ("unit", (([], []), Inline T.unit_ty));
  ("int", (([], []), Inline T.int_ty));
  ("string", (([], []), Inline T.string_ty));
  ("float", (([], []), Inline T.float_ty));
  ("list", (let a = Params.fresh_ty_param () in
            (([a, (true, false)], []),
             Sum [(Common.nil, None);
                  (Common.cons, Some (T.Tuple [T.TyVar a; T.Apply ("list", ([T.TyVar a], []))]))])));
  ("empty", (([], []), Sum []))
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

let replace_tydef rpls =
  let replace = Type.replace_ty rpls in
  function
  | Record tys -> Record (Common.assoc_map replace tys)
  | Sum tys -> Sum (Common.assoc_map (Common.option_map replace) tys)
  | Inline ty -> Inline (replace ty)

(* Lookup type parameters for a given type. *)
let lookup_params ty_name =
  match Common.lookup ty_name !tctx with
  | None -> None
  | Some (params, _) -> Some params

let get_variances ty_name =
  match lookup_params ty_name with
  | None -> assert false (* this function should only be called after types have been checked. *)
  | Some params -> params

let remove_variances (ps, ds) = (List.map fst ps, List.map fst ds)

let lookup_tydef ~loc ty_name =
  match Common.lookup ty_name !tctx with
  | None -> Error.typing ~loc "Unknown type %s" ty_name
  | Some (params, tydef) -> (remove_variances params, tydef)

let refreshing_subst (ps, ds) =
  let sbst = Params.refreshing_subst () in
  let refresh_ty_param = sbst.Params.ty_param
  and refresh_dirt_param = sbst.Params.dirt_param in
  Params.make (List.map refresh_ty_param ps, List.map refresh_dirt_param ds),
  {
    Params.ty_param = (fun p -> refresh_ty_param p);
    Params.dirt_param = Common.id;
  }

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


let apply_to_params t params =
  let (ps, ds) = Params.unmake params in
  Type.Apply (t, (
      List.map (fun p -> Type.TyVar p) ps, List.map Type.simple_dirt ds
    ))

(** [infer_variant lbl] finds a variant type that defines the label [lbl] and returns it
    with refreshed type parameters and additional information needed for type
    inference. *)
let infer_variant lbl =
  match find_variant lbl with
  | None -> None
  | Some (ty_name, ps, _, u) ->
    let ps', fresh_subst = refreshing_subst (remove_variances ps) in
    let u = Common.option_map (T.subst_ty fresh_subst) u in
    Some (apply_to_params ty_name ps', u)


(** [infer_field fld] finds a record type that defines the field [fld] and returns it with
    refreshed type parameters and additional information needed for type inference. *)
let infer_field fld =
  match find_field fld with
  | None -> None
  | Some (ty_name, ps, us) ->
    let ps', fresh_subst = refreshing_subst (remove_variances ps) in
    let us' = Common.assoc_map (T.subst_ty fresh_subst) us in
    Some (apply_to_params ty_name ps', (ty_name, us'))


let transparent ~loc ty_name =
  match snd (lookup_tydef ~loc ty_name) with
  | Sum _ | Record _ -> false
  | Inline _ -> true

(* [ty_apply ~loc t lst] applies the type constructor [t] to the given list of arguments. *)
let ty_apply ~loc ty_name (tys, drts) : tydef =
  let ((ts, ds), ty) = lookup_tydef ~loc ty_name in
  let ty_sbst =
    try List.combine ts tys with
      Invalid_argument "List.combine" -> Error.typing ~loc "Type constructors %s should be applied to %d type arguments" ty_name (List.length ts)
  and dirt_sbst =
    try List.combine ds drts with
      Invalid_argument "List.combine" -> Error.typing ~loc "Type constructors %s should be applied to %d dirt arguments" ty_name (List.length ds)
  in
  replace_tydef {
    T.ty_param_repl = (fun p -> Common.lookup_default p ty_sbst (Type.TyVar p));
    T.dirt_param_repl = (fun d -> Common.lookup_default d dirt_sbst (Type.simple_dirt d));
  } ty

(** [check_well_formed ~loc ty] checks that type [ty] is well-formed. *)
let check_well_formed ~loc tydef =
  let rec check = function
    | T.Prim _ | T.TyVar _ -> ()
    | T.Apply (ty_name, (tys, drts)) ->
      begin match lookup_tydef ~loc ty_name with
        | (ts, ds), (Sum _  | Record _ | Inline _) ->
          let n = List.length ts in
          if List.length tys <> n then
            Error.typing ~loc "The type constructor %s expects %d type arguments" ty_name n;
          let n = List.length ds in
          if List.length drts <> n then
            Error.typing ~loc "The type constructor %s expects %d dirt arguments" ty_name n;
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
    | T.Prim _ | T.TyVar _ -> ()
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
  let prepare_variances (params, def) =
    let (ps, ds) = Params.unmake params in
    ((prepare_variance ps, prepare_variance ds), def) in
  let prepared_tydefs = Common.assoc_map prepare_variances tydefs in
  let set_variances (ty_name, ((ps, ds), def)) =
    let rec ty posi nega = function
      | T.Prim _ -> ()
      | T.TyVar p ->
        begin match Common.lookup p ps with
          | None -> assert false
          | Some (posvar, negvar) ->
            posvar := !posvar || posi;
            negvar := !negvar || nega
        end
      | T.Apply (t, (tys, drts)) ->
        begin match Common.lookup t !tctx with
          | None ->
            (* XXX Here, we should do some sort of an equivalence relation algorithm to compute better variances. *)
            List.iter (ty true true) tys;
            List.iter (dirt true true) drts;
          | Some ((ps, ds), _) ->
            if List.length ps != List.length tys then
              Error.typing ~loc "The type constructor %s expects %d type arguments" t (List.length ps);
            if List.length ds != List.length drts then
              Error.typing ~loc "The type constructor %s expects %d dirt arguments" t (List.length drts);
            if posi then begin
              List.iter2 (fun (_, (posi', nega')) -> ty posi' nega') ps tys;
              List.iter2 (fun (_, (posi', nega')) -> dirt posi' nega') ds drts
            end;
            if nega then begin
              List.iter2 (fun (_, (posi', nega')) -> ty nega' posi') ps tys;
              List.iter2 (fun (_, (posi', nega')) -> dirt nega' posi') ds drts
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
      dirt_param posi nega drt.Type.rest
    and dirt_param posi nega d =
      begin match Common.lookup d ds with
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
  let extend_with_variance (ty_name, ((ps, ds), def)) =
    (ty_name, ((unref ps, unref ds), def))
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
