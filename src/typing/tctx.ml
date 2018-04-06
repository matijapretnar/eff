(** Type inference contexts *)
module C = OldUtils
module T = Type

type tydef =
  | Record of (OldUtils.field, Type.ty) OldUtils.assoc
  | Sum of (OldUtils.label, Type.ty option) OldUtils.assoc
  | Inline of Type.ty

type tyctx = (OldUtils.tyname, Type.ty_param list * tydef) OldUtils.assoc

let initial : tyctx =
  [ ("in_channel", ([], Inline T.in_channel_ty))
  ; ("out_channel", ([], Inline T.out_channel_ty))
  ; ("char", ([], Inline T.char_ty))
  ; ("bool", ([], Inline T.bool_ty))
  ; ("unit", ([], Inline T.unit_ty))
  ; ("int", ([], Inline T.int_ty))
  ; ("string", ([], Inline T.string_ty))
  ; ("float", ([], Inline T.float_ty))
  ; ( "list"
    , let a = Type.fresh_ty_param () in
      ( [a]
      , Sum
          [ (OldUtils.nil, None)
          ; ( OldUtils.cons
            , Some (T.Tuple [T.TyParam a; T.Apply ("list", [T.TyParam a])]) )
          ] ) )
  ; ("empty", ([], Sum [])) ]


let global = ref initial

let reset () = global := initial

let subst_tydef sbst =
  let subst = Type.subst_ty sbst in
  function
    | Record tys -> Record (OldUtils.assoc_map subst tys)
    | Sum tys -> Sum (OldUtils.assoc_map (OldUtils.option_map subst) tys)
    | Inline ty -> Inline (subst ty)


let lookup_tydef ~loc ty_name =
  match OldUtils.lookup ty_name !global with
  | None -> Error.typing ~loc "Unknown type %s" ty_name
  | Some (params, tydef) -> (params, tydef)


let fresh_tydef ~loc ty_name =
  let params, tydef = lookup_tydef ~loc ty_name in
  let params', sbst = Type.refreshing_subst params in
  (params', subst_tydef sbst tydef)


(** [find_variant lbl] returns the information about the variant type that defines the
    label [lbl]. *)
let find_variant lbl =
  let rec find = function
    | [] -> None
    | (ty_name, (ps, Sum vs)) :: lst -> (
      match OldUtils.lookup lbl vs with
      | Some us -> Some (ty_name, ps, vs, us)
      | None -> find lst )
    | _ :: lst -> find lst
  in
  find !global


(** [find_field fld] returns the information about the record type that defines the field
    [fld]. *)
let find_field fld =
  let rec find = function
    | [] -> None
    | (ty_name, (ps, Record flds)) :: lst ->
        if List.mem_assoc fld flds then Some (ty_name, ps, flds) else find lst
    | _ :: lst -> find lst
  in
  find !global


let apply_to_params t ps = Type.Apply (t, List.map (fun p -> Type.TyParam p) ps)

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


let transparent ~loc ty_name =
  let _, ty = lookup_tydef ~loc ty_name in
  match ty with Sum _ | Record _ -> false | Inline _ -> true


(* [ty_apply pos t lst] applies the type constructor [t] to the given list of arguments. *)
let ty_apply ~loc ty_name lst =
  let xs, ty = lookup_tydef ~loc ty_name in
  try subst_tydef (List.combine xs lst) ty
  with Invalid_argument "List.combine" ->
    Error.typing ~loc "Type constructors %s should be applied to %d arguments"
      ty_name (List.length xs)


(** [check_well_formed ~loc ty] checks that type [ty] is well-formed. *)
let check_well_formed ~loc tydef =
  let rec check = function
    | T.Basic _ | T.TyParam _ -> ()
    | T.Apply (ty_name, tys) ->
        let params, _ = lookup_tydef ~loc ty_name in
        let n = List.length params in
        if List.length tys <> n then
          Error.typing ~loc "The type constructor %s expects %d arguments"
            ty_name n
    | T.Arrow (ty1, ty2) -> check ty1 ; check ty2
    | T.Tuple tys -> List.iter check tys
    | T.Handler {T.value= ty1; T.finally= ty2} -> check ty1 ; check ty2
  in
  match tydef with
  | Record fields ->
      if not (OldUtils.injective fst fields) then
        Error.typing ~loc "Field labels in a record type must be distinct" ;
      List.iter (fun (_, ty) -> check ty) fields
  | Sum constuctors ->
      if not (OldUtils.injective fst constuctors) then
        Error.typing ~loc "Constructors of a sum type must be distinct" ;
      List.iter (function _, None -> () | _, Some ty -> check ty) constuctors
  | Inline ty -> check ty


(** [check_well_formed ~loc ty] checks that the definition of type [ty] is non-cyclic. *)
let check_noncyclic ~loc =
  let rec check forbidden = function
    | T.Basic _ | T.TyParam _ -> ()
    | T.Apply (t, lst) ->
        if List.mem t forbidden then
          Error.typing ~loc "Type definition %s is cyclic." t
        else check_tydef (t :: forbidden) (ty_apply ~loc t lst)
    | T.Arrow (ty1, ty2) -> check forbidden ty1 ; check forbidden ty2
    | T.Tuple tys -> List.iter (check forbidden) tys
    | T.Handler {T.value= ty1; T.finally= ty2} ->
        check forbidden ty1 ; check forbidden ty2
  and check_tydef forbidden = function
    | Sum _ -> ()
    | Record fields -> List.iter (fun (_, t) -> check forbidden t) fields
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
      List.iter
        (fun (f, _) ->
          match find_field f with
          | Some (u, _, _) ->
              Error.typing ~loc
                "Record field label %s is already used in type %s" f u
          | None -> () )
        lst
  | Sum lst ->
      List.iter
        (fun (lbl, _) ->
          match find_variant lbl with
          | Some (u, _, _, _) ->
              Error.typing ~loc "Constructor %s is already used in type %s" lbl
                u
          | None -> () )
        lst
  | Inline _ -> ()


(** [extend_tydefs ~loc tydefs] checks that the simulatenous type definitions [tydefs] are
    well-formed and returns the extended context. *)
let extend_tydefs ~loc tydefs =
  (* We wish we wrote this in eff, where we could have transactional memory. *)
  let global_orig = !global in
  let extend_tydef ((_, (_, ty)) as tydef) =
    check_shadowing ~loc ty ;
    global := tydef :: !global
  in
  try
    List.iter extend_tydef tydefs ;
    List.iter (fun (_, (_, ty)) -> check_well_formed ~loc ty) tydefs ;
    List.iter (fun (_, (_, ty)) -> check_noncyclic ~loc ty) tydefs
  with e ->
    global := global_orig ;
    raise e

(* reinstate the context on error *)
