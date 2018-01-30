type ty_scheme = Type.ty_param list * Type.ty

type t =
  { variables: (CoreSyntax.variable, ty_scheme) OldUtils.assoc
  ; effects: (Type.ty * Type.ty) CoreSyntax.EffectMap.t }

let empty = {variables= []; effects= CoreSyntax.EffectMap.empty}

let lookup ~loc ctx x =
  match OldUtils.lookup x ctx.variables with
  | Some (ps, t) -> snd (Type.refresh ps t)
  | None -> Error.typing ~loc "Unknown name %t" (CoreSyntax.Variable.print x)


let extend ctx x ty_scheme =
  {ctx with variables= (x, ty_scheme) :: ctx.variables}


let extend_ty ctx x ty = extend ctx x ([], ty)

let subst_ctx ctx sbst =
  let subst_ty_scheme (ps, ty) =
    assert (List.for_all (fun (p, _) -> not (List.mem p ps)) sbst) ;
    (ps, Type.subst_ty sbst ty)
  in
  {ctx with variables= OldUtils.assoc_map subst_ty_scheme ctx.variables}


(** [free_params ctx] returns a list of all free type parameters in [ctx]. *)
let free_params ctx =
  let binding_params (_, (ps, ty)) = OldUtils.diff (Type.free_params ty) ps in
  let xs = OldUtils.flatten_map binding_params ctx in
  OldUtils.uniq xs


let generalize ctx poly ty =
  if poly then
    let ps = OldUtils.diff (Type.free_params ty) (free_params ctx.variables) in
    (ps, ty)
  else ([], ty)


let infer_effect env eff =
  try Some (CoreSyntax.EffectMap.find eff env.effects) with Not_found -> None


let add_effect env eff (ty1, ty2) =
  match infer_effect env eff with
  | None ->
      {env with effects= CoreSyntax.EffectMap.add eff (ty1, ty2) env.effects}
  | Some _ ->
      Error.typing ~loc:Location.unknown "Effect %s already defined." eff
