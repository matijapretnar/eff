(** Type inference contexts *)
module C = Common
module T = Type

let initial : (string, Ctx.ty_scheme) C.assoc = [
  ("bool", (([], [], []), T.bool_ty));
  ("unit", (([], [], []), T.unit_ty));
  ("int", (([], [], []), T.int_ty));
  ("string", (([], [], []), T.string_ty));
  ("float", (([], [], []), T.float_ty));
  ("list", (let a = Type.fresh_ty_param () in
              (([a], [], []),
               T.Sum [(Common.nil, None);
                      (Common.cons, Some (T.Tuple [T.TyParam a; T.Apply ("list", [T.TyParam a])]))])));
  ("empty", (([], [], []), T.empty_ty));
]

(** All functions use the global typing context. *)
let global = ref initial

let reset () = global := initial

let lookup_tydef ~pos ty_name =
  match Common.lookup ty_name !global with
  | None -> Error.typing ~pos "Unknown type %s" ty_name
  | Some (params, ty) -> (params, ty)

let fresh_tydef ~pos ty_name =
  let (params, ty) = lookup_tydef ~pos ty_name in
  Type.refresh params ty

(** [find_variant lbl] returns the name of the variant type that defines the label [lbl] *)
let find_variant cons =
  let rec find = function
  | [] -> None
  | (ty_name, (_, T.Sum vs) as ty) :: lst ->
      begin match Common.lookup cons vs with
      | Some us -> Some (ty_name, ty, vs, us)
      | None -> find lst
      end
  | _ :: lst -> find lst
  in
  find !global

(** [find_field fld] returns the name of the record type that defines the field [fld] *)
let find_field lbl =
  let rec find = function
    | [] -> None
    | (ty_name, (_, T.Record flds) as ty) :: lst ->
      if List.mem_assoc lbl flds
      then Some (ty_name, ty, flds)
      else find lst
    | _ :: lst -> find lst
  in
    find !global

(** [find_operation op] returns the name of the effect type that defines the operation
    symbol [op] *)
let find_operation op_name =
  let rec find = function
    | [] -> None
    | (ty_name, (_, T.Effect eff_sig) as ty) :: lst ->
      if List.mem_assoc op_name eff_sig
      then Some (ty_name, ty, eff_sig)
      else find lst
    | _ :: lst -> find lst
  in
    find !global
      
(** [infer_variant lbl] finds a variant type that defines the label [lbl] and returns it
    with refreshed type parameters. *)
let infer_variant lbl =
  let rec find = function
    | [] -> None
    | (t, (ps, T.Sum vs)) :: lst ->
      begin match C.lookup lbl vs with
        | Some u ->
          let ps', fresh_subst = T.refreshing_subst ps in
          let u = C.option_map (T.subst_ty fresh_subst) u in
            Some (t, ps', u)
        | None -> find lst
      end
    | _ :: lst -> find lst
  in
    find !global

(** [infer_field fld] finds a record type that defines the field [fld] and returns it with
    refreshed type parameters. *)
let infer_field fld  =
  let rec find = function
    | [] -> None
    | (t, (ps, T.Record us)) :: _ when List.mem_assoc fld us ->
      let ps', fresh_subst = T.refreshing_subst ps in
      let us' = C.assoc_map (T.subst_ty fresh_subst) us in
        Some (t, ps', us')
    | _ :: lst -> find lst
  in
    find !global

(** [infer_operation op] finds an effect type that defines the operation [op] and returns
    it with refreshed type parameters. *)
let infer_operation op =
  let rec find = function
    | [] -> None
    | (t, (ps, T.Effect vs)) :: lst ->
      begin match C.lookup op vs with
        | Some (t1, t2) ->
          let ps', fresh_subst = T.refreshing_subst ps in
          let t1 = T.subst_ty fresh_subst t1 in
          let t2 = T.subst_ty fresh_subst t2 in
            Some (t, ps', t1, t2)
        | None -> find lst
      end
    | _ :: lst -> find lst
  in
    find !global

(** Is the given type transparent, i.e., should we unfold its definition? *)
let transparent ~pos ty_name =
  let (_, ty) = lookup_tydef ~pos ty_name in
    match ty with
      | T.Sum (_::_) | T.Effect _ | T.Record _ -> false
      | T.Basic _ | T.Apply _ | T.TyParam _ | T.Sum [] |
          T.Arrow _ | T.Tuple _ | T.Handler _ -> true

(* [ty_apply ctx pos t lst] applies the type constructor [t] to the given list of arguments. *)
let ty_apply ~pos ty_name lst =
  let ((xs, _, _), ty) = lookup_tydef ~pos ty_name in
  try
      T.subst_ty {T.identity_subst with T.subst_ty = List.combine xs lst} ty
  with
    Invalid_argument "List.combine" ->
      Error.typing ~pos "Type constructors %s should be applied to %d arguments" ty_name (List.length xs)

(** [check_well_formed ~pos ty] checks that type [ty] is well-formed. *)
let check_well_formed ~pos =
  let rec check = function
  | T.Basic _ | T.TyParam _ -> ()
  | T.Apply (ty_name, tys) ->
      let ((params, _, _), _) = lookup_tydef ~pos ty_name in
      let n = List.length params in
      if List.length tys <> n then
        Error.typing ~pos "The type constructor %s expects %d arguments" ty_name n
  | T.Arrow (ty1, dirty2) -> check ty1; check_dirty dirty2
  | T.Tuple tys -> List.iter check tys
  | T.Record fields ->
      if not (Common.injective fst fields) then
        Error.typing ~pos "Field labels in a record type must be distinct";
      List.iter (fun (_, ty) -> check ty) fields
  | T.Sum constuctors ->
      if not (Common.injective fst constuctors) then
        Error.typing ~pos "Constructors of a sum type must be distinct";
      List.iter (function (_, None) -> () | (_, Some ty) -> check ty) constuctors
  | T.Effect signature ->
      if not (Common.injective fst signature) then Error.typing ~pos
        "Operations in an effect type must be distinct";
      List.iter (fun (_, (ty1, ty2)) -> check ty1; check ty2) signature
  | T.Handler {T.value = ty1; T.finally = ty2} -> check ty1; check ty2
  and check_dirty (ty, _) = check ty
  in
  check

(** [check_well_formed ~pos ty] checks that the definition of type [ty] is non-cyclic. *)
let check_noncyclic ~pos =
  let rec check forbidden = function
  | T.Basic _ | T.Sum _ | T.TyParam _ -> ()
  | T.Apply (t, lst) ->
      if List.mem t forbidden then
        Error.typing ~pos "Type definition %s is cyclic." t
      else
        check (t :: forbidden) (ty_apply ~pos t lst)
  | T.Arrow (ty1, (ty2, _)) -> check forbidden ty1; check forbidden ty2
  | T.Tuple tys -> List.iter (check forbidden) tys
  | T.Record fields -> List.iter (fun (_,t) -> check forbidden t) fields
  | T.Effect signature ->
      List.iter (fun (_, (ty1, ty2)) -> check forbidden ty1; check forbidden ty2) signature
  | T.Handler {T.value = ty1; T.finally = ty2} ->
      check forbidden ty1; check forbidden ty2
  in
  check []

(** [check_shadowing ~pos ty] checks that the definition of type [ty] does
    not shadow any field labels, constructors, or operations defined so far.

    NB: In eff we _cannot_ allow shadowing because the interpreter uses the original
    field names and label, hence shadowing breaks type safety!
*)
let check_shadowing ~pos = function
  | (T.Basic _ | T.Apply _ | T.TyParam _ | T.Arrow _ | T.Tuple _ | T.Handler _) -> ()
  | T.Record lst ->
    List.iter (fun (f,_) ->
      match find_field f with
        | Some (u, _, _) -> Error.typing ~pos:pos "Record field label %s is already used in type %s" f u
        | None -> ()
    ) lst
  | T.Sum lst ->
    List.iter (fun (lbl,_) ->
      match find_variant lbl with
        | Some (u, _, _, _) -> Error.typing ~pos:pos "Constructor %s is already used in type %s" lbl u
        | None -> ()
    ) lst
  | T.Effect lst ->
    List.iter (fun (op, _) ->
      match find_operation op with
        | Some (u, _, _) -> Error.typing ~pos:pos "Operation %s is already used in type %s" op u
        | None -> ()
    ) lst

(** [extend_tydefs ~pos tydefs] checks that the simulatenous type definitions [tydefs] are
    well-formed and extends the type context. *)

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
