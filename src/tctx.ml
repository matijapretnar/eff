(** Type inference contexts *)
module C = Common
module T = Type

type tydef =
  | Record of (Common.field, Type.ty) Common.assoc
  | Sum of (Common.label, Type.ty option) Common.assoc
  | Inline of Type.ty
  | Effect of (Common.opsym, Type.ty * Type.ty) Common.assoc

type tyctx = (Common.tyname, Type.params * tydef) Common.assoc

let initial_tctx : tyctx = [
  ("bool", (([], [], []), Inline T.bool_ty));
  ("unit", (([], [], []), Inline T.unit_ty));
  ("int", (([], [], []), Inline T.int_ty));
  ("string", (([], [], []), Inline T.string_ty));
  ("float", (([], [], []), Inline T.float_ty));
  ("list", (let a = Type.fresh_ty_param () in
              (([a], [], []),
                 Sum [(Common.nil, None);
                      (Common.cons, Some (T.Tuple [T.TyParam a; T.Apply ("list", ([T.TyParam a], [], []))]))])));
  ("empty", (([], [], []), Sum []))
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
  | Effect op_sig -> Effect (Common.assoc_map (fun (ty1, ty2) -> (subst ty1, subst ty2)) op_sig)

(* Lookup type parameters for a given type. *)
let lookup_params ty_name =
  match Common.lookup ty_name !tctx with
    | None -> None
    | Some (params, _) -> Some params

let lookup_tydef ~pos ty_name =
  match Common.lookup ty_name !tctx with
  | None -> Error.typing ~pos "Unknown type %s" ty_name
  | Some (params, tydef) -> (params, tydef)

let is_effect ~pos =
  let rec find forbidden ty_name =
    match lookup_tydef ~pos ty_name with
      | (_, Effect _) -> true
      | (_, (Record _ | Sum _)) -> false
      | (_, Inline (T.Apply (ty_name', _))) ->
        if List.mem ty_name' forbidden
        then Error.typing ~pos "Type definition %s is cyclic." ty_name' (* Compare to [Tctx.check_noncyclic]. *)
        else find (ty_name :: forbidden) ty_name'
      | (_, Inline _) -> false
  in
    find []

let fresh_tydef ~pos ty_name =
  let (params, tydef) = lookup_tydef ~pos ty_name in
  let params', sbst = Type.refreshing_subst params in
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

(** [find_operation op] returns the information about the effect type
    that defines the operation symbol [op]. *)
let find_operation op_name =
  let rec find = function
    | [] -> None
    | (ty_name, (ps, Effect eff_sig)) :: lst ->
        begin match Common.lookup op_name eff_sig with
        | Some (t1, t2) -> Some (ty_name, ps, t1, t2)
        | None -> find lst
        end
    | _ :: lst -> find lst
  in
    find !tctx

let apply_to_params t (ps, ds, rs) =
  Type.Apply (t, (
    List.map (fun p -> Type.TyParam p) ps,
    List.map (fun d -> Type.DirtParam d) ds,
    List.map (fun r -> Type.RegionParam r) rs
  ))

let effect_to_params t (ps, ds, rs) rgn =
  Type.Effect (t, (
    List.map (fun p -> Type.TyParam p) ps,
    List.map (fun d -> Type.DirtParam d) ds,
    List.map (fun r -> Type.RegionParam r) rs
  ), rgn)

(** [infer_variant lbl] finds a variant type that defines the label [lbl] and returns it
    with refreshed type parameters and additional information needed for type
    inference. *)
let infer_variant lbl =
  match find_variant lbl with
    | None -> None
    | Some (ty_name, ps, _, u) ->
      let ps', fresh_subst = T.refreshing_subst ps in
      let u = C.option_map (T.subst_ty fresh_subst) u in
        Some (apply_to_params ty_name ps', u)


(** [infer_field fld] finds a record type that defines the field [fld] and returns it with
    refreshed type parameters and additional information needed for type inference. *)
let infer_field fld =
  match find_field fld with
    | None -> None
    | Some (ty_name, ps, us) ->
      let ps', fresh_subst = T.refreshing_subst ps in
      let us' = C.assoc_map (T.subst_ty fresh_subst) us in
        Some (apply_to_params ty_name ps', (ty_name, us'))


(** [infer_operation op] finds an effect type that defines the operation [op] and returns
    it with refreshed type parameters and additional information needed for type
    inference. *)
let infer_operation op =
  match find_operation op with
    | None -> None
    | Some (ty_name, ps, t1, t2) ->
      let ps', fresh_subst = T.refreshing_subst ps in
      let t1 = T.subst_ty fresh_subst t1 in
      let t2 = T.subst_ty fresh_subst t2 in
      let rgn = T.fresh_region () in
        Some (effect_to_params ty_name ps' rgn, (t1, t2))

let transparent ~pos ty_name =
    match snd (lookup_tydef ~pos ty_name) with
      | Sum _ | Record _ | Effect _ -> false
      | Inline _ -> true

(* [ty_apply pos t lst] applies the type constructor [t] to the given list of arguments. *)
let ty_apply ~pos ty_name (tys, drts, rgns) =
  let ((ts, ds, rs), ty) = lookup_tydef ~pos ty_name in
  let ty_sbst =
    try List.combine ts tys with
      Invalid_argument "List.combine" -> Error.typing ~pos "Type constructors %s should be applied to %d type arguments" ty_name (List.length ts)
  and dirt_sbst =
    try List.combine ds drts with
      Invalid_argument "List.combine" -> Error.typing ~pos "Type constructors %s should be applied to %d dirt arguments" ty_name (List.length ds)
  and region_sbst =
    try List.combine rs rgns with
      Invalid_argument "List.combine" -> Error.typing ~pos "Type constructors %s should be applied to %d region arguments" ty_name (List.length rs)
  in
  subst_tydef {
    T.subst_ty = ty_sbst;
    T.subst_dirt = dirt_sbst;
    T.subst_region = region_sbst;
  } ty

(** [check_well_formed ~pos ty] checks that type [ty] is well-formed. *)
let check_well_formed ~pos tydef =
  let rec check = function
  | T.Basic _ | T.TyParam _ -> ()
  | T.Apply (ty_name, (tys, drts, rgns)) ->
    begin match lookup_tydef ~pos ty_name with
      | (ts, ds, rs), (Sum _  | Record _ | Inline _) ->
        let n = List.length ts in
          if List.length tys <> n then
            Error.typing ~pos "The type constructor %s expects %d type arguments" ty_name n;
          let n = List.length ds in
            if List.length drts <> n then
              Error.typing ~pos "The type constructor %s expects %d dirt arguments" ty_name n;
            let n = List.length rs in
              if List.length rgns <> n then
                Error.typing ~pos "The type constructor %s expects %d region arguments" ty_name n
      | _, Effect _ ->
        Error.typing ~pos "The effect type constructor %s should be applied to a region" ty_name
    end
  | T.Effect (ty_name, (tys, drts, rgns), _) ->
    begin match lookup_tydef ~pos ty_name with
      | (ts, ds, rs), Effect _ ->
        let n = List.length ts in
          if List.length tys <> n then
            Error.typing ~pos "The type constructor %s expects %d type arguments" ty_name n;
          let n = List.length ds in
            if List.length drts <> n then
              Error.typing ~pos "The type constructor %s expects %d dirt arguments" ty_name n;
            let n = List.length rs in
              if List.length rgns <> n then
                Error.typing ~pos "The type constructor %s expects %d region arguments" ty_name n
      | _, (Sum _ | Record _ | Inline _) ->
        Error.typing ~pos "The non-effect type constructor %s cannot be applied to a region" ty_name
    end
  | T.Arrow (ty1, dirty2) -> check ty1; check_dirty dirty2
  | T.Tuple tys -> List.iter check tys
  | T.Handler {T.value = ty1; T.finally = ty2} -> check ty1; check ty2
  and check_dirty (ty, _) = check ty
  in
  match tydef with
  | Record fields ->
      if not (Common.injective fst fields) then
        Error.typing ~pos "Field labels in a record type must be distinct";
      List.iter (fun (_, ty) -> check ty) fields
  | Sum constuctors ->
      if not (Common.injective fst constuctors) then
        Error.typing ~pos "Constructors of a sum type must be distinct";
      List.iter (function (_, None) -> () | (_, Some ty) -> check ty) constuctors
  | Inline ty -> check ty
  | Effect signature ->
      if not (Common.injective fst signature) then Error.typing ~pos
        "Operations in an effect type must be distinct";
      List.iter (fun (_, (ty1, ty2)) -> check ty1; check ty2) signature

(** [check_noncyclic ~pos ty] checks that the definition of type [ty] is non-cyclic. *)
let check_noncyclic ~pos =
  let rec check forbidden = function
  | T.Basic _ | T.TyParam _ -> ()
  | T.Apply (t, args) ->
      if List.mem t forbidden then
        Error.typing ~pos "Type definition %s is cyclic." t
      else
        check_tydef (t :: forbidden) (ty_apply ~pos t args)
  | T.Effect (t, args, _) ->
      if List.mem t forbidden then
        Error.typing ~pos "Type definition %s is cyclic." t
      else
        check_tydef (t :: forbidden) (ty_apply ~pos t args)
  | T.Arrow (ty1, (ty2, _)) -> check forbidden ty1; check forbidden ty2
  | T.Tuple tys -> List.iter (check forbidden) tys
  | T.Handler {T.value = ty1; T.finally = ty2} ->
      check forbidden ty1; check forbidden ty2
  and check_tydef forbidden = function
  | Sum _ -> ()
  | Record fields -> List.iter (fun (_,t) -> check forbidden t) fields
  | Inline ty -> check forbidden ty
  | Effect signature ->
      List.iter (fun (_, (ty1, ty2)) -> check forbidden ty1; check forbidden ty2) signature
  in 
  check_tydef []

(** [check_shadowing ~pos ty] checks that the definition of type [ty] does
    not shadow any field labels, constructors, or operations.

    NB: In eff we _cannot_ allow shadowing because the interpreter uses the original
    field names and label, hence shadowing breaks type safety!
*)
let check_shadowing ~pos = function
  | Record lst ->
    List.iter (fun (f,_) ->
      match find_field f with
        | Some (u, _, _) -> Error.typing ~pos "Record field label %s is already used in type %s" f u
        | None -> ()
    ) lst
  | Sum lst ->
    List.iter (fun (lbl,_) ->
      match find_variant lbl with
        | Some (u, _, _, _) -> Error.typing ~pos "Constructor %s is already used in type %s" lbl u
        | None -> ()
    ) lst
  | Inline _ -> ()
  | Effect lst ->
    List.iter (fun (op, _) ->
      match find_operation op with
        | Some (u, _, _, _) -> Error.typing ~pos "Operation %s is already used in type %s" op u
        | None -> ()
    ) lst

(** [extend_tydefs ~pos tydefs] checks that the simulatenous type definitions [tydefs] are
    well-formed and returns the extended context. *)
let extend_tydefs ~pos tydefs =
  (* We wish we wrote this in eff, where we could have transactional memory. *)
  let tctx_orig = !tctx in
  let extend_tydef ((tyname, (_, ty)) as tydef) =
    if List.mem_assoc tyname !tctx then Error.typing ~pos "Type %s is already defined" tyname ;
    check_shadowing ~pos ty ;
    tctx := tydef :: !tctx
  in 
    try 
      List.iter extend_tydef tydefs ;
      List.iter (fun (_, (_, ty)) -> check_well_formed ~pos ty) tydefs;
      List.iter (fun (_, (_, ty)) -> check_noncyclic ~pos ty) tydefs
    with e ->
      tctx := tctx_orig ; raise e (* reinstate the context on error *)
