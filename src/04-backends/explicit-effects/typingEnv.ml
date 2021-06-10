open Utils

type t = (Language.CoreTypes.Variable.t, Type.ty_scheme) Assoc.t

let empty = Assoc.empty

let lookup ctx x : Term.expression * Constraint.omega_ct list =
  match Assoc.lookup x ctx with
  | Some ty_scheme ->
      let sbst : Type.Renaming.t =
        {
          skel_params =
            ty_scheme.Type.parameters.skeleton_params
            |> List.map (fun p -> (p, Type.SkelParam.refresh p))
            |> List.to_seq |> Type.SkelParamMap.of_seq;
          ty_params =
            ty_scheme.Type.parameters.ty_params
            |> List.map (fun (p, _skel) ->
                   (p, Language.CoreTypes.TyParam.refresh p))
            |> List.to_seq |> Type.TyParamMap.of_seq;
          dirt_params =
            ty_scheme.Type.parameters.dirt_params
            |> List.map (fun p -> (p, Type.DirtParam.refresh p))
            |> List.to_seq |> Type.DirtParamMap.of_seq;
          ty_coercion_params =
            ty_scheme.Type.parameters.ty_constraints
            |> List.map (fun (p, _) -> (p, Type.TyCoercionParam.refresh p))
            |> List.to_seq |> Type.TyCoercionParamMap.of_seq;
          dirt_coercion_params =
            ty_scheme.Type.parameters.dirt_constraints
            |> List.map (fun (p, _) -> (p, Type.DirtCoercionParam.refresh p))
            |> List.to_seq |> Type.DirtCoercionParamMap.of_seq;
        }
      in
      let ty_scheme = Type.rename_ty_scheme sbst ty_scheme in
      let x =
        Term.poly_var_with_parameters x ty_scheme.parameters ty_scheme.monotype
      in
      let cnstrs =
        List.map
          (fun (w, ct) -> Constraint.TyOmega (w, ct))
          ty_scheme.parameters.ty_constraints
        @ List.map
            (fun (w, dt) -> Constraint.DirtOmega (w, dt))
            ty_scheme.parameters.dirt_constraints
      in
      (x, cnstrs)
  | None -> assert false

let update ctx x sch = Assoc.update x sch ctx
