(** Type inference contexts *)
module C = Common
module T = Type

type tydef =
  | Record of (Common.field, Type.ty) Common.assoc
  | Sum of (Common.label, Type.ty option) Common.assoc
  | Effect of (Common.opsym, Type.ty * Type.ty) Common.assoc
  | Inline of Type.ty

type tyctx = (Common.tyname, (Type.ty_param list * Type.dirt_param list * Type.region_param list) * tydef) Common.assoc

let initial : tyctx = [
  ("bool", (([], [], []), Inline T.bool_ty));
  ("unit", (([], [], []), Inline T.unit_ty));
  ("int", (([], [], []), Inline T.int_ty));
  ("string", (([], [], []), Inline T.string_ty));
  ("float", (([], [], []), Inline T.float_ty));
  ("list", (let a = Type.fresh_ty_param () in
              (([a], [], []),
               Sum [(Common.nil, None);
                      (Common.cons, Some (T.Tuple [T.TyParam a; T.Apply ("list", [T.TyParam a])]))])));
  ("empty", (([], [], []), Sum []))
]


let global = ref initial

let reset () = global := initial

let subst_tydef sbst =
  let subst = Type.subst_ty sbst in
  function
  | Record tys -> Record (Common.assoc_map subst tys)
  | Sum tys -> Sum (Common.assoc_map (Common.option_map subst) tys)
  | Effect op_sig ->
      Effect (Common.assoc_map (fun (ty1, ty2) -> (subst ty1, subst ty2)) op_sig)
  | Inline ty -> Inline (subst ty)

let lookup_tydef ~pos ty_name =
  match Common.lookup ty_name !global with
  | None -> Error.typing ~pos "Unknown type %s" ty_name
  | Some (params, tydef) -> (params, tydef)

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
    find !global

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
    find !global

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
    find !global

let apply_to_params t (ps, _, _) =
  Type.Apply (t, List.map (fun p -> Type.TyParam p) ps)

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
        Some (apply_to_params ty_name ps', (t1, t2))


let transparent ~pos ty_name =
  let (_, ty) = lookup_tydef ~pos ty_name in
    match ty with
      | Sum _ | Effect _ | Record _ -> false
      | Inline _ -> true

(* [ty_apply pos t lst] applies the type constructor [t] to the given list of arguments. *)
let ty_apply ~pos ty_name lst =
  let ((xs, _, _), ty) = lookup_tydef ~pos ty_name in
  try
      subst_tydef {T.identity_subst with T.subst_ty = List.combine xs lst} ty
  with
    Invalid_argument "List.combine" ->
      Error.typing ~pos "Type constructors %s should be applied to %d arguments" ty_name (List.length xs)

(** [check_well_formed ~pos ty] checks that type [ty] is well-formed. *)
let check_well_formed ~pos tydef =
  let rec check = function
  | T.Basic _ | T.TyParam _ -> ()
  | T.Apply (ty_name, tys) ->
      let ((params, _, _), _) = lookup_tydef ~pos ty_name in
      let n = List.length params in
      if List.length tys <> n then
        Error.typing ~pos "The type constructor %s expects %d arguments" ty_name n
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
  | Effect signature ->
      if not (Common.injective fst signature) then Error.typing ~pos
        "Operations in an effect type must be distinct";
      List.iter (fun (_, (ty1, ty2)) -> check ty1; check ty2) signature
  | Inline ty -> check ty

(** [check_well_formed ~pos ty] checks that the definition of type [ty] is non-cyclic. *)
let check_noncyclic ~pos =
  let rec check forbidden = function
  | T.Basic _ | T.TyParam _ -> ()
  | T.Apply (t, lst) ->
      if List.mem t forbidden then
        Error.typing ~pos "Type definition %s is cyclic." t
      else
        check_tydef (t :: forbidden) (ty_apply ~pos t lst)
  | T.Arrow (ty1, (ty2, _)) -> check forbidden ty1; check forbidden ty2
  | T.Tuple tys -> List.iter (check forbidden) tys
  | T.Handler {T.value = ty1; T.finally = ty2} ->
      check forbidden ty1; check forbidden ty2
  and check_tydef forbidden = function
  | Sum _ -> ()
  | Record fields -> List.iter (fun (_,t) -> check forbidden t) fields
  | Effect signature ->
      List.iter (fun (_, (ty1, ty2)) -> check forbidden ty1; check forbidden ty2) signature
  | Inline ty -> check forbidden ty
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
  | Effect lst ->
    List.iter (fun (op, _) ->
      match find_operation op with
        | Some (u, _, _, _) -> Error.typing ~pos "Operation %s is already used in type %s" op u
        | None -> ()
    ) lst
  | Inline _ -> ()

(** [extend_tydefs ~pos tydefs] checks that the simulatenous type definitions [tydefs] are
    well-formed and returns the extended context. *)
let extend_tydefs ~pos tydefs =
  (* We wish we wrote this in eff, where we could have transactional memory. *)
  let global_orig = !global in
  let extend_tydef ((_, (_, ty)) as tydef) =
    check_shadowing ~pos ty ;
    global := tydef :: !global
  in 
    try 
      List.iter extend_tydef tydefs ;
      List.iter (fun (_, (_, ty)) -> check_well_formed ~pos ty) tydefs;
      List.iter (fun (_, (_, ty)) -> check_noncyclic ~pos ty) tydefs
    with e ->
      global := global_orig ; raise e (* reinstate the context on error *)
