open Utils

type t = (Language.CoreTypes.Variable.t, Type.ty_scheme) Assoc.t

let empty = Assoc.empty

let lookup ctx x =
  match Assoc.lookup x ctx with
  | Some ty_scheme ->
      let sbst : Type.Renaming.t =
        {
          skel_params =
            ty_scheme.Type.skeleton_params
            |> List.map (fun p -> (p, Type.SkelParam.refresh p))
            |> List.to_seq |> Type.SkelParamMap.of_seq;
          ty_params =
            ty_scheme.Type.ty_params
            |> List.map (fun (p, _skel) ->
                   (p, Language.CoreTypes.TyParam.refresh p))
            |> List.to_seq |> Type.TyParamMap.of_seq;
          dirt_params =
            ty_scheme.Type.dirt_params
            |> List.map (fun p -> (p, Type.DirtParam.refresh p))
            |> List.to_seq |> Type.DirtParamMap.of_seq;
        }
      in
      let monotype = Type.rename_ty sbst ty_scheme.Type.monotype
      and skeletons =
        List.map
          (fun p -> Type.SkelParam (Type.SkelParamMap.find p sbst.skel_params))
          ty_scheme.Type.skeleton_params
      and tys =
        List.map
          (fun (p, skel) ->
            Type.TyParam
              ( Type.TyParamMap.find p sbst.ty_params,
                Type.rename_skeleton sbst skel ))
          ty_scheme.Type.ty_params
      and dirts =
        List.map
          (fun p ->
            (p, Type.no_effect_dirt (Type.DirtParamMap.find p sbst.dirt_params)))
          ty_scheme.Type.dirt_params
      and ty_coercions, ty_constraints =
        ty_scheme.Type.ty_constraints
        |> List.map (fun ct ->
               Constraint.fresh_ty_coer (Type.rename_ct_ty sbst ct))
        |> List.split
      and dirt_coercions, dirt_constraints =
        ty_scheme.Type.dirt_constraints
        |> List.map (fun ct ->
               Constraint.fresh_dirt_coer (Type.rename_ct_dirt sbst ct))
        |> List.split
      in
      ( Term.poly_var (Term.variable x monotype) skeletons tys dirts
          ty_coercions dirt_coercions,
        ty_constraints @ dirt_constraints )
  | None -> assert false

let update ctx x sch = Assoc.update x sch ctx
