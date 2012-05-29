(** Type inference contexts *)
module C = Common
module T = Type

(** A context binds types to variables and type definitions to type names *)
type context = {
  (** each variable is assigned a type together with a list of polymorphic
      type parameters (not restricted by value restriction) *)
  variables: (C.variable * (T.param list * T.ty)) list;
  (** each type name is assigned a type definition according with a list of
      type parameters *)
  types: (C.tyname * (T.param list * T.ty)) list;
}

let lookup_tydef ?pos tctx ty_name =
  match Common.lookup ty_name tctx with
  | None -> Error.typing ?pos "Unknown type %s" ty_name
  | Some (params, ty) -> (params, ty)

let fresh_tydef ?pos tctx ty_name =
  let (params, ty) = lookup_tydef ?pos tctx ty_name in
  Type.refresh params ty

let extend_var x pt ctx =
  { ctx with variables = (x, pt) :: ctx.variables }

let extend_vars vars ctx =
  List.fold_right (fun (x, t) ctx -> extend_var x ([], t) ctx) vars ctx

(** Initial context has no variables and only builtin types *)
let initial = {
  variables = [];
  types = External.types;
}

(** [freeparams ctx] returns a list of all free type parameters in [ctx] *)
let free_params {variables=lst} =
  C.uniq (List.flatten (List.map (fun (_,(ps,t)) -> C.diff (T.free_params t) ps) lst))

(** [subst_ctx sbst ctx] applies a type substitution to all types occurring in
    [ctx]. *)
let subst_ctx sbst ctx =
  { ctx with variables =
      C.assoc_map
        (fun (ps,t) -> 
          assert (List.for_all (fun (p,_) -> not (List.mem p ps)) sbst) ;
          (ps, T.subst_ty sbst t))
        ctx.variables }

(** [find_variant lbl tctx] returns the name of the variant type from [tcxt]
    that defines the label [lbl] *)
let find_variant ?pos tctx cons =
  let rec find = function
  | [] -> Error.typing ?pos "Unbound constructor %s" cons
  | (ty_name, (_, T.Sum vs) as ty) :: lst ->
      begin match Common.lookup cons vs with
      | Some us -> (ty_name, ty, vs, us)
      | None -> find lst
      end
  | _ :: lst -> find lst
  in
  find tctx

(** [find_field fld tctx] returns the name of the record type from [tcxt] that
    defines the field [fld] *)
let find_field ?pos tctx lbl =
  let rec find = function
  | [] -> Error.typing ?pos "Unbound record field label %s" lbl
  | (ty_name, (_, T.Record flds) as ty) :: lst
      when List.mem_assoc lbl flds -> (ty_name, ty, flds)
  | _ :: lst -> find lst
  in
  find tctx

(** [find_operation op tctx] returns the name of the effect type from [tcxt]
    that defines the operation symbol [op] *)
let find_operation ?pos tctx op_name =
  let rec find = function
  | [] -> Error.typing ?pos "Unbound operation %s" op_name
  | (ty_name, (_, T.Effect eff_sig) as ty) :: lst
      when List.mem_assoc op_name eff_sig -> (ty_name, ty, eff_sig)
  | _ :: lst -> find lst
  in
  find tctx

(** [infer_variant lbl tctx] finds a variant type from [tctx] that defines the
    label [lbl] and returns it with refreshed type parameters. *)
let infer_variant lbl tctx =
  let rec find = function
    | [] -> Error.typing "Unknown variant %s." lbl
    | (t, (ps, T.Sum vs)) :: lst ->
        begin match C.lookup lbl vs with
        | Some u ->
            let fresh_subst = List.map (fun p -> p, T.fresh_param ()) ps in
            let ps = List.map snd fresh_subst in
            let u = C.option_map (T.subst_ty fresh_subst) u in
            (t, ps, u)
        | None -> find lst
        end
    | _ :: lst -> find lst
  in
    find tctx

(** [infer_field fld tctx] finds a record type from [tctx] that defines the
    field [fld] and returns it with refreshed type parameters. *)
let infer_field fld tctx =
  let rec find = function
    | [] -> Error.typing "Unknown field %s." fld
    | (t, (ps, T.Record us)) :: lst when List.mem_assoc fld us ->
        let fresh_subst = List.map (fun p -> p, T.fresh_param ()) ps in
        let ps = List.map snd fresh_subst in
        let us = C.assoc_map (T.subst_ty fresh_subst) us in
        (t, ps, us)
    | _ :: lst -> find lst
  in
    find tctx

(** [infer_operation op tctx] finds an effect type from [tctx] that defines the
    operation [op] and returns it with refreshed type parameters. *)
let infer_operation op tctx =
  let rec find = function
    | [] -> Error.typing "Unknown operation %s" op
    | (t, (ps, T.Effect vs)) :: lst ->
        begin match C.lookup op vs with
          | Some (t1, t2) ->
              let fresh_subst = List.map (fun p -> p, T.fresh_param ()) ps in
              let ps = List.map snd fresh_subst in
              let t1 = T.subst_ty fresh_subst t1 in
              let t2 = T.subst_ty fresh_subst t2 in
              (t, ps, t1, t2)
          | None -> find lst
        end
    | _ :: lst -> find lst
  in
    find tctx


let transparent ?pos tctx ty_name =
  let (_, ty) = lookup_tydef ?pos tctx ty_name in
  match ty with
  | T.Sum (_::_) | T.Effect _ | T.Record _ -> false
  | T.Basic _ | T.Apply _ | T.Param _ | T.Sum [] |
    T.Arrow _ | T.Tuple _ | T.Handler _ -> true

(* [ty_apply ctx pos t lst] applies the type constructor [t] to the given list of arguments. *)
let ty_apply ?pos tctx ty_name lst =
  let (params, ty) = lookup_tydef ?pos tctx ty_name in
  try
    let s = List.combine params lst in
      T.subst_ty s ty
  with
    Invalid_argument "List.combine" ->
      Error.typing ?pos "Type constructors %s should be applied to %d arguments" ty_name (List.length params)

(** [check_well_formed ?pos tctx ty] checks that type [ty] is well-formed in
    a type context [tctx]. *)
let check_well_formed ?pos ctx =
  let rec check = function
  | T.Basic _ | T.Param _ -> ()
  | T.Apply (ty_name, tys) ->
      let (params, _) = lookup_tydef ?pos ctx ty_name in
      let n = List.length params in
      if List.length tys <> n then
        Error.typing ?pos "The type constructor %s expects %d arguments" ty_name n
  | T.Arrow (ty1, ty2) -> check ty1; check ty2
  | T.Tuple tys -> List.iter check tys
  | T.Record fields ->
      if not (Common.injective fst fields) then
        Error.typing ?pos "Field labels in a record type must be distinct";
      List.iter (fun (_, ty) -> check ty) fields
  | T.Sum constuctors ->
      if not (Common.injective fst constuctors) then
        Error.typing ?pos "Constructors of a sum type must be distinct";
      List.iter (function (_, None) -> () | (_, Some ty) -> check ty) constuctors
  | T.Effect signature ->
      if not (Common.injective fst signature) then Error.typing ?pos
        "Operations in an effect type must be distinct";
      List.iter (fun (_, (ty1, ty2)) -> check ty1; check ty2) signature
  | T.Handler {T.value = ty1; T.finally = ty2} -> check ty1; check ty2
  in
  check

(** [check_well_formed ?pos tctx ty] checks that the definition of type [ty] is
    non-cyclic in [tctx]. *)
let check_noncyclic ?pos ctx =
  let rec check forbidden = function
  | T.Basic _ | T.Sum _ | T.Param _ -> ()
  | T.Apply (t, lst) ->
      if List.mem t forbidden then
        Error.typing ?pos "Type definition %s is cyclic." t
      else
        check (t :: forbidden) (ty_apply ?pos ctx t lst)
  | T.Arrow (ty1, ty2) -> check forbidden ty1; check forbidden ty2
  | T.Tuple tys -> List.iter (check forbidden) tys
  | T.Record fields -> List.iter (fun (_,t) -> check forbidden t) fields
  | T.Effect signature ->
      List.iter (fun (_, (ty1, ty2)) -> check forbidden ty1; check forbidden ty2) signature
  | T.Handler {T.value = ty1; T.finally = ty2} ->
      check forbidden ty1; check forbidden ty2
  in
  check []

(** [check_shadowing ?pos tctx ty] checks that the definition of type [ty] does
    not shadow any field labels, constructors, or operations defined in [tctx]. *)
(* XXX Not implemented yet *)
let check_shadowing ?pos tctx ty = ()

(** [extend_tydefs ?pos ctx tydefs] checks that the simulatenous type
    definitions [tydefs] are well-formed in context [ctx] and returns the
    extended context. *)

let extend_tydef ty def ctx = {ctx with types = (ty, def) :: ctx.types}


let extend_tydefs ?pos ctx tydefs =
  let extend_tydef ctx ((_, (_, ty)) as tydef) =
    check_shadowing ctx.types ty;
    {ctx with types = tydef :: ctx.types}
  in 
  let ctx = List.fold_left extend_tydef ctx tydefs in
  List.iter (fun (_, (_, ty)) -> check_well_formed ?pos ctx.types ty) tydefs;
  List.iter (fun (_, (_, ty)) -> check_noncyclic ?pos ctx.types ty) tydefs;
  ctx
