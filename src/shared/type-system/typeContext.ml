open Utils
open Language
module T = Type

type tydef =
  | Record of (CoreTypes.Field.t, T.ty) Assoc.t
  | Sum of (CoreTypes.Label.t, T.ty option) Assoc.t
  | Inline of T.ty

type type_data = { params : CoreTypes.TyParam.t list; type_def : tydef }

type state = (CoreTypes.TyName.t, type_data) Assoc.t

let initial_state =
  Assoc.of_list
    [
      (CoreTypes.bool_tyname, { params = []; type_def = Inline T.bool_ty });
      (CoreTypes.unit_tyname, { params = []; type_def = Inline T.unit_ty });
      (CoreTypes.int_tyname, { params = []; type_def = Inline T.int_ty });
      (CoreTypes.string_tyname, { params = []; type_def = Inline T.string_ty });
      (CoreTypes.float_tyname, { params = []; type_def = Inline T.float_ty });
      ( CoreTypes.list_tyname,
        let a = Type.fresh_ty_param () in
        let list_nil = (CoreTypes.nil, None) in
        let list_cons =
          ( CoreTypes.cons,
            Some
              (T.Tuple
                 [
                   T.TyParam a; T.Apply (CoreTypes.list_tyname, [ T.TyParam a ]);
                 ]) )
        in
        {
          params = [ a ];
          type_def = Sum (Assoc.of_list [ list_nil; list_cons ]);
        } );
      (CoreTypes.empty_tyname, { params = []; type_def = Sum Assoc.empty });
    ]

let subst_tydef sbst =
  let subst = T.subst_ty sbst in
  function
  | Record tys -> Record (Assoc.map subst tys)
  | Sum tys ->
      Sum (Assoc.map (function None -> None | Some x -> Some (subst x)) tys)
  | Inline ty -> Inline (subst ty)

let lookup_tydef ~loc ty_name st =
  match Assoc.lookup ty_name st with
  | None -> Error.typing ~loc "Unknown type %t" (CoreTypes.TyName.print ty_name)
  | Some tdata -> tdata

(** [find_variant lbl] returns the information about the variant type that defines the
    label [lbl]. *)
let find_variant lbl st =
  let construct = function
    | ty_name, { params; type_def = Sum vs } -> (
        match Assoc.lookup lbl vs with
        | Some us -> Some (ty_name, params, vs, us)
        | None -> None)
    | _ -> None
  in
  match Assoc.find_if (fun x -> construct x <> None) st with
  | Some x -> construct x
  | None -> None

(** [find_field fld] returns the information about the record type that defines the field
    [fld]. *)

let find_field fld (st : state) =
  let construct = function
    | ty_name, { params; type_def = Record flds } -> (
        match Assoc.lookup fld flds with
        | Some _ -> Some (ty_name, params, flds)
        | None -> None)
    | _ -> None
  in
  match Assoc.find_if (fun x -> construct x <> None) st with
  | Some x -> construct x
  | None -> None

let apply_to_params t ps = T.Apply (t, List.map (fun p -> T.TyParam p) ps)

(** [infer_variant lbl] finds a variant type that defines the label [lbl] and returns it
    with refreshed type parameters and additional information needed for type
    inference. *)
let infer_variant lbl st =
  match find_variant lbl st with
  | None -> None
  | Some (ty_name, ps, _, u) ->
      let ps', fresh_subst = T.refreshing_subst ps in
      let u' =
        match u with None -> None | Some x -> Some (T.subst_ty fresh_subst x)
      in
      Some (apply_to_params ty_name ps', u')

(** [infer_field fld] finds a record type that defines the field [fld] and returns it with
    refreshed type parameters and additional information needed for type inference. *)
let infer_field fld st =
  match find_field fld st with
  | None -> None
  | Some (ty_name, ps, us) ->
      let ps', fresh_subst = T.refreshing_subst ps in
      let us' = Assoc.map (T.subst_ty fresh_subst) us in
      Some (apply_to_params ty_name ps', (ty_name, us'))

let transparent ~loc ty_name st =
  let { type_def; _ } = lookup_tydef ~loc ty_name st in
  match type_def with Sum _ | Record _ -> false | Inline _ -> true

(* [ty_apply pos ty_name lst st] applies the type constructor [ty_name] to the given list of arguments. *)
let ty_apply ~loc ty_name lst st =
  let { params; type_def } = lookup_tydef ~loc ty_name st in
  if List.length params <> List.length lst then
    Error.typing ~loc "Type constructors %t should be applied to %d arguments"
      (CoreTypes.TyName.print ty_name)
      (List.length params)
  else
    let combined = Assoc.of_list (List.combine params lst) in
    subst_tydef combined type_def

(** [check_well_formed ~loc st ty] checks that type [ty] is well-formed. *)
let check_well_formed ~loc tydef st =
  let rec check = function
    | T.Basic _ | T.TyParam _ -> ()
    | T.Apply (ty_name, tys) ->
        let { params; _ } = lookup_tydef ~loc ty_name st in
        let n = List.length params in
        if List.length tys <> n then
          Error.typing ~loc "The type constructor %t expects %d arguments"
            (CoreTypes.TyName.print ty_name)
            n
    | T.Arrow (ty1, ty2) ->
        check ty1;
        check ty2
    | T.Tuple tys -> List.iter check tys
    | T.Handler { T.value = ty1; T.finally = ty2 } ->
        check ty1;
        check ty2
  in
  match tydef with
  | Record fields ->
      if not (CoreUtils.no_duplicates (Assoc.keys_of fields)) then
        Error.typing ~loc "Field labels in a record type must be distinct";
      Assoc.iter (fun (_, ty) -> check ty) fields
  | Sum constructors ->
      if not (CoreUtils.no_duplicates (Assoc.keys_of constructors)) then
        Error.typing ~loc "Constructors of a sum type must be distinct";
      let checker = function _, None -> () | _, Some ty -> check ty in
      Assoc.iter checker constructors
  | Inline ty -> check ty

(** [check_noncyclic ~loc st ty] checks that the definition of type [ty] is non-cyclic. *)
let check_noncyclic ~loc st =
  let rec check forbidden = function
    | T.Basic _ | T.TyParam _ -> ()
    | T.Apply (t, lst) ->
        if List.mem t forbidden then
          Error.typing ~loc "Type definition %t is cyclic."
            (CoreTypes.TyName.print t)
        else check_tydef (t :: forbidden) (ty_apply ~loc t lst st)
    | T.Arrow (ty1, ty2) ->
        check forbidden ty1;
        check forbidden ty2
    | T.Tuple tys -> List.iter (check forbidden) tys
    | T.Handler { T.value = ty1; T.finally = ty2 } ->
        check forbidden ty1;
        check forbidden ty2
  and check_tydef forbidden = function
    | Sum _ -> ()
    | Record fields -> Assoc.iter (fun (_, t) -> check forbidden t) fields
    | Inline ty -> check forbidden ty
  in
  check_tydef []

(** [check_shadowing ~loc st ty] checks that the definition of type [ty] does
    not shadow any field labels, constructors, or operations.

    NB: In eff we _cannot_ allow shadowing because the interpreter uses the original
    field names and label, hence shadowing breaks type safety!
*)
let check_shadowing ~loc st = function
  | Record lst ->
      let shadow_check_fld (f, _) =
        match find_field f st with
        | Some (u, _, _) ->
            Error.typing ~loc "Record field label %t is already used in type %t"
              (CoreTypes.Field.print f) (CoreTypes.TyName.print u)
        | None -> ()
      in
      Assoc.iter shadow_check_fld lst
  | Sum lst ->
      let shadow_check_sum (lbl, _) =
        match find_variant lbl st with
        | Some (u, _, _, _) ->
            Error.typing ~loc "Constructor %t is already used in type %t"
              (CoreTypes.Label.print lbl)
              (CoreTypes.TyName.print u)
        | None -> ()
      in
      Assoc.iter shadow_check_sum lst
  | Inline _ -> ()

(** [extend_type_definitions ~loc tydefs state] checks that the simulatenous type definitions [tydefs] are
    well-formed and returns the extended type context. *)
let extend_type_definitions ~loc tydefs st =
  (* We wish we wrote this in eff, where we could have transactional memory. *)
  let tydefs' =
    Assoc.map (fun (params, type_def) -> { params; type_def }) tydefs
  in
  let extend_tydef st' (name, { params; type_def }) =
    check_shadowing ~loc st' type_def;
    match Assoc.lookup name st' with
    | Some _ ->
        Error.typing ~loc "Type %t already defined."
          (CoreTypes.TyName.print name)
    | None -> Assoc.update name { params; type_def } st'
  in
  try
    let st = Assoc.fold_left extend_tydef st tydefs' in
    Assoc.iter
      (fun (_, { type_def; _ }) -> check_well_formed ~loc type_def st)
      tydefs';
    Assoc.iter
      (fun (_, { type_def; _ }) -> check_noncyclic ~loc st type_def)
      tydefs';
    st
  with e -> raise e
