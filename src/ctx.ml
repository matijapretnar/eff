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

let lookup_tydef ty tctx = C.lookup ty tctx

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
let find_variant lbl tctx =
  let rec find = function
    | [] -> None
    | (t, (ps, T.Sum vs)) :: lst ->
        begin match C.lookup lbl vs with
          | Some us -> Some t
          | None -> find lst
        end
    | _ :: lst -> find lst
  in
    find tctx

(** [find_field fld tctx] returns the name of the record type from [tcxt] that
    defines the field [fld] *)
let find_field fld tctx =
  let rec find = function
    | [] -> None
    | (t, (ps, T.Record vs)) :: lst when List.mem_assoc fld vs -> Some t
    | _ :: lst -> find lst
  in
    find tctx

(** [find_operation op tctx] returns the name of the effect type from [tcxt]
    that defines the operation symbol [op] *)
let find_operation op tctx =
  let rec find = function
    | [] -> None
    | (t, (ps, T.Effect vs)) :: lst ->
        begin match C.lookup op vs with
          | Some (t1, t2) -> Some t
          | None -> find lst
        end
    | _ :: lst -> find lst
  in
    find tctx

let extend_tydef ty def ctx = {ctx with types = (ty, def) :: ctx.types}

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
