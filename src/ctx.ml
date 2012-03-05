module C = Common
module T = Type

type context = {
  variables: (C.variable * (T.param list * T.ty)) list;
  types: (C.tyname * (T.param list * T.ty)) list;
}

let lookup_tydef ty tctx = C.lookup ty tctx

let extend_var x pt ctx =
  { ctx with variables = (x, pt) :: ctx.variables }

let extend_vars vars ctx =
  List.fold_right (fun (x, t) ctx -> extend_var x ([], t) ctx) vars ctx

let initial = {
  variables = [];
  types = External.types;
}

let free_params {variables=lst} =
  C.uniq (List.flatten (List.map (fun (_,(ps,t)) -> C.diff (T.free_params t) ps) lst))

let subst_ctx sbst ctx =
  { ctx with variables =
      C.assoc_map
        (fun (ps,t) -> 
          assert (List.for_all (fun (p,_) -> not (List.mem p ps)) sbst) ;
          (ps, T.subst_ty sbst t))
        ctx.variables }

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

let find_field fld tctx =
  let rec find = function
    | [] -> None
    | (t, (ps, T.Record vs)) :: lst when List.mem_assoc fld vs -> Some t
    | _ :: lst -> find lst
  in
    find tctx

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
