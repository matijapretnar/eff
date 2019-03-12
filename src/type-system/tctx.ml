(** Type inference contexts *)
module T = Type

type tydef =
  | Record of (CoreTypes.Field.t, Type.ty) Assoc.t
  | Sum of (CoreTypes.Label.t, Type.ty option) Assoc.t
  | Inline of Type.ty

type tyctx = (CoreTypes.TyName.t, Params.Ty.t list * tydef) Assoc.t

let initial : tyctx =
  Assoc.of_list
    [ (CoreTypes.bool_tyname, ([], Inline T.bool_ty))
    ; (CoreTypes.unit_tyname, ([], Inline T.unit_ty))
    ; (CoreTypes.int_tyname, ([], Inline T.int_ty))
    ; (CoreTypes.string_tyname, ([], Inline T.string_ty))
    ; (CoreTypes.float_tyname, ([], Inline T.float_ty))
    ; (CoreTypes.list_tyname
      , let a = Type.fresh_ty_param () in
        let list_nil = (CoreTypes.nil, None) in
        let list_cons =
          ( CoreTypes.cons
          , Some (T.Tuple [T.TyParam a; T.Apply (CoreTypes.list_tyname, [T.TyParam a])]) )
        in
        ([a], Sum (Assoc.of_list [list_nil; list_cons])) )
    ; (CoreTypes.empty_tyname, ([], Sum Assoc.empty)) ]

let global = ref initial

let reset () = global := initial

let subst_tydef sbst =
  let subst = Type.subst_ty sbst in
  function
    | Record tys -> Record (Assoc.map subst tys)
    | Sum tys -> 
        Sum (Assoc.map (function None -> None | Some x -> Some (subst x)) tys)
    | Inline ty -> Inline (subst ty)

let lookup_tydef ~loc ty_name =
  match Assoc.lookup ty_name !global with
  | None -> Error.typing ~loc "Unknown type %t" (CoreTypes.TyName.print ty_name)
  | Some (params, tydef) -> (params, tydef)

let fresh_tydef ~loc ty_name =
  let params, tydef = lookup_tydef ~loc ty_name in
  let params', sbst = Type.refreshing_subst params in
  (params', subst_tydef sbst tydef)

(** [find_variant lbl] returns the information about the variant type that defines the
    label [lbl]. *)
let find_variant lbl =
  let construct = function
    | ty_name, (ps, Sum vs) -> (
      match Assoc.lookup lbl vs with
      | Some us -> Some (ty_name, ps, vs, us)
      | None -> None )
    | _ -> None
  in
  match Assoc.find_if (fun x -> construct x <> None) !global with
  | Some x -> construct x
  | None -> None

(** [find_field fld] returns the information about the record type that defines the field
    [fld]. *)

let find_field fld =
  let construct = function
    | ty_name, (ps, Record flds) -> (
      match Assoc.lookup fld flds with
      | Some _ -> Some (ty_name, ps, flds)
      | None -> None )
    | _ -> None
  in
  match Assoc.find_if (fun x -> construct x <> None) !global with
  | Some x -> construct x
  | None -> None

let apply_to_params t ps = Type.Apply (t, List.map (fun p -> Type.TyParam p) ps)

(** [infer_variant lbl] finds a variant type that defines the label [lbl] and returns it
    with refreshed type parameters and additional information needed for type
    inference. *)
let infer_variant lbl =
  match find_variant lbl with
  | None -> None
  | Some (ty_name, ps, _, u) ->
      let ps', fresh_subst = T.refreshing_subst ps in
      let u' = 
        match u with
        | None -> None 
        | Some x -> Some (T.subst_ty fresh_subst x)
      in
      Some (apply_to_params ty_name ps', u')

(** [infer_field fld] finds a record type that defines the field [fld] and returns it with
    refreshed type parameters and additional information needed for type inference. *)
let infer_field fld =
  match find_field fld with
  | None -> None
  | Some (ty_name, ps, us) ->
      let ps', fresh_subst = T.refreshing_subst ps in
      let us' = Assoc.map (T.subst_ty fresh_subst) us in
      Some (apply_to_params ty_name ps', (ty_name, us'))

let transparent ~loc ty_name =
  let _, ty = lookup_tydef ~loc ty_name in
  match ty with Sum _ | Record _ -> false | Inline _ -> true

(* [ty_apply pos t lst] applies the type constructor [t] to the given list of arguments. *)
let ty_apply ~loc ty_name lst =
  let xs, ty = lookup_tydef ~loc ty_name in
  if List.length xs <> List.length lst then
    Error.typing ~loc "Type constructors %t should be applied to %d arguments"
      (CoreTypes.TyName.print ty_name) (List.length xs)
  else
    let combined = Assoc.of_list (List.combine xs lst) in
    subst_tydef combined ty

(** [check_well_formed ~loc ty] checks that type [ty] is well-formed. *)
let check_well_formed ~loc tydef =
  let rec check = function
    | T.Basic _ | T.TyParam _ -> ()
    | T.Apply (ty_name, tys) ->
        let params, _ = lookup_tydef ~loc ty_name in
        let n = List.length params in
        if List.length tys <> n then
          Error.typing ~loc "The type constructor %t expects %d arguments"
            (CoreTypes.TyName.print ty_name) n
    | T.Arrow (ty1, ty2) -> check ty1 ; check ty2
    | T.Tuple tys -> List.iter check tys
    | T.Handler {T.value= ty1; T.finally= ty2} -> check ty1 ; check ty2
  in
  match tydef with
  | Record fields ->
      if not (CoreUtils.no_duplicates (Assoc.keys_of fields)) then
        Error.typing ~loc "Field labels in a record type must be distinct" ;
      Assoc.iter (fun (_, ty) -> check ty) fields
  | Sum constructors ->
      if not (CoreUtils.no_duplicates (Assoc.keys_of constructors)) then
        Error.typing ~loc "Constructors of a sum type must be distinct" ;
      let checker = function _, None -> () | _, Some ty -> check ty in
      Assoc.iter checker constructors
  | Inline ty -> check ty

(** [check_well_formed ~loc ty] checks that the definition of type [ty] is non-cyclic. *)
let check_noncyclic ~loc =
  let rec check forbidden = function
    | T.Basic _ | T.TyParam _ -> ()
    | T.Apply (t, lst) ->
        if List.mem t forbidden then
          Error.typing ~loc "Type definition %t is cyclic."
            (CoreTypes.TyName.print t)
        else check_tydef (t :: forbidden) (ty_apply ~loc t lst)
    | T.Arrow (ty1, ty2) -> check forbidden ty1 ; check forbidden ty2
    | T.Tuple tys -> List.iter (check forbidden) tys
    | T.Handler {T.value= ty1; T.finally= ty2} ->
        check forbidden ty1 ; check forbidden ty2
  and check_tydef forbidden = function
    | Sum _ -> ()
    | Record fields -> Assoc.iter (fun (_, t) -> check forbidden t) fields
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
      let shadow_check_fld (f, _) =
        match find_field f with
        | Some (u, _, _) ->
            Error.typing ~loc
              "Record field label %t is already used in type %t" 
                (CoreTypes.Field.print f) (CoreTypes.TyName.print u)
        | None -> ()
      in
      Assoc.iter shadow_check_fld lst
  | Sum lst ->
      let shadow_check_sum (lbl, _) =
        match find_variant lbl with
        | Some (u, _, _, _) ->
            Error.typing ~loc 
              "Constructor %t is already used in type %t"
              (CoreTypes.Label.print lbl) (CoreTypes.TyName.print u)
        | None -> ()
      in
      Assoc.iter shadow_check_sum lst
  | Inline _ -> ()

(** [extend_tydefs ~loc tydefs] checks that the simulatenous type definitions [tydefs] are
    well-formed and returns the extended context. *)
let extend_tydefs ~loc tydefs =
  (* We wish we wrote this in eff, where we could have transactional memory. *)
  let global_orig = !global in
  let extend_tydef (name, (params, ty)) =
    check_shadowing ~loc ty ;
    global := Assoc.update name (params, ty) !global
  in
  try
    Assoc.iter extend_tydef tydefs ;
    Assoc.iter (fun (_, (_, ty)) -> check_well_formed ~loc ty) tydefs ;
    Assoc.iter (fun (_, (_, ty)) -> check_noncyclic ~loc ty) tydefs
  with e ->
    global := global_orig ;
    raise e

(* reinstate the context on error *)
