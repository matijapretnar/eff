module Untyped = UntypedSyntax
module EffectMap = Map.Make (CoreTypes.Effect)

type ty_scheme = CoreTypes.TyParam.t list * Type.ty

type t = {variables: (CoreTypes.Variable.t, ty_scheme) Assoc.t}

let empty = {variables= Assoc.empty}

let lookup ~loc ctx x =
  match Assoc.lookup x ctx.variables with
  | Some (ps, t) ->
      snd (Type.refresh ps t)
  | None ->
      Error.typing ~loc "Unknown name %t" (CoreTypes.Variable.print x)

let extend ctx x ty_scheme = {variables= Assoc.update x ty_scheme ctx.variables}

let extend_ty ctx x ty = extend ctx x ([], ty)

let subst_ctx ctx sbst =
  let subst_ty_scheme (ps, ty) =
    assert (List.for_all (fun p -> not (List.mem p ps)) (Assoc.keys_of sbst)) ;
    (ps, Type.subst_ty sbst ty)
  in
  {variables= Assoc.map subst_ty_scheme ctx.variables}

(** [free_params ctx] returns list of all free type parameters in [ctx]. *)
let free_params ctx =
  let binding_params (_, (ps, ty)) =
    CoreUtils.list_diff (Type.free_params ty) ps
  in
  let xs = List.map binding_params (Assoc.to_list ctx) |> List.flatten in
  CoreUtils.unique_elements xs

let generalize ctx poly ty =
  if poly then
    let ps =
      CoreUtils.list_diff (Type.free_params ty) (free_params ctx.variables)
    in
    (ps, ty)
  else ([], ty)
