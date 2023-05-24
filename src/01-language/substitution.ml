(** Substitution implementation *)

open Utils

type t = {
  type_param_to_type_coercions :
    Coercion.ty_coercion Type.TyCoercionParam.Map.t;
  type_param_to_type_subs : Type.ty Type.TyParam.Map.t;
  dirt_var_to_dirt_coercions :
    Coercion.dirt_coercion Type.DirtCoercionParam.Map.t;
  dirt_var_to_dirt_subs : Dirt.t Dirt.Param.Map.t;
  skel_param_to_skel_subs : Skeleton.t Skeleton.Param.Map.t;
}

let empty =
  {
    type_param_to_type_coercions = Type.TyCoercionParam.Map.empty;
    type_param_to_type_subs = Type.TyParam.Map.empty;
    dirt_var_to_dirt_coercions = Type.DirtCoercionParam.Map.empty;
    dirt_var_to_dirt_subs = Dirt.Param.Map.empty;
    skel_param_to_skel_subs = Skeleton.Param.Map.empty;
  }

let is_empty sub =
  Type.TyCoercionParam.Map.is_empty sub.type_param_to_type_coercions
  && Type.TyParam.Map.is_empty sub.type_param_to_type_subs
  && Type.DirtCoercionParam.Map.is_empty sub.dirt_var_to_dirt_coercions
  && Dirt.Param.Map.is_empty sub.dirt_var_to_dirt_subs
  && Skeleton.Param.Map.is_empty sub.skel_param_to_skel_subs

(* Substitution application *)
open Type

let apply_sub_dirt sub (dirt : Dirt.t) =
  match dirt.row with
  | Dirt.Row.Param p -> (
      match Dirt.Param.Map.find_opt p sub.dirt_var_to_dirt_subs with
      | Some drt2 -> Dirt.add_effects dirt.effect_set drt2
      | None -> dirt)
  | Dirt.Row.Empty -> dirt

let rec apply_sub_skel sub skeleton =
  match skeleton with
  | Skeleton.Param p -> (
      match Skeleton.Param.Map.find_opt p sub.skel_param_to_skel_subs with
      | Some sk1 -> sk1
      | None -> skeleton)
  | Basic _ -> skeleton
  | Arrow (sk1, sk2) -> Arrow (apply_sub_skel sub sk1, apply_sub_skel sub sk2)
  | Handler (sk1, sk2) ->
      Handler (apply_sub_skel sub sk1, apply_sub_skel sub sk2)
  (* Really consider other cases *)
  | Apply { ty_name; skel_args } ->
      Apply
        {
          ty_name;
          skel_args = TyParam.Map.map (fun s -> apply_sub_skel sub s) skel_args;
        }
  | Tuple skels -> Tuple (List.map (apply_sub_skel sub) skels)

let rec apply_sub_ty sub ty =
  let ty' = apply_sub_ty' sub ty in
  { ty' with ty = apply_sub_skel sub ty'.ty }

and apply_sub_ty' sub ty : ty =
  match ty.term with
  | TyParam typ1 -> (
      match Type.TyParam.Map.find_opt typ1 sub.type_param_to_type_subs with
      | Some ttype -> ttype
      | None -> { ty with ty = apply_sub_skel sub ty.ty })
  | Arrow (tty1, tty2) ->
      arrow (apply_sub_ty sub tty1, apply_sub_dirty_ty sub tty2)
  | Apply { ty_name; ty_args } ->
      Type.apply
        ( ty_name,
          TyParam.Map.map
            (fun (ty, variance) -> (apply_sub_ty sub ty, variance))
            ty_args )
  | Tuple ttyl -> Type.tuple (List.map (fun x -> apply_sub_ty sub x) ttyl)
  | Handler (tydrty1, tydrty2) ->
      Type.handler
        (apply_sub_dirty_ty sub tydrty1, apply_sub_dirty_ty sub tydrty2)
  | TyBasic p -> tyBasic p

and apply_sub_dirty_ty sub (ty, drt) =
  (apply_sub_ty sub ty, apply_sub_dirt sub drt)

let apply_sub_eff_ty sub (ty1, ty2) =
  (apply_sub_ty sub ty1, apply_sub_ty sub ty2)

let apply_sub_abs_ty sub (ty, drty) =
  (apply_sub_ty sub ty, apply_sub_dirty_ty sub drty)

let apply_sub_abs2_ty sub (ty1, ty2, drty) =
  (apply_sub_ty sub ty1, apply_sub_ty sub ty2, apply_sub_dirty_ty sub drty)

let apply_sub_ct_ty sub (ty1, ty2) = (apply_sub_ty sub ty1, apply_sub_ty sub ty2)

let apply_sub_ct_dirt sub (drt1, drt2) =
  (apply_sub_dirt sub drt1, apply_sub_dirt sub drt2)

let rec apply_sub_tycoer sub ty_coer =
  match ty_coer.term with
  | Coercion.TyCoercionVar p -> (
      match
        Type.TyCoercionParam.Map.find_opt p sub.type_param_to_type_coercions
      with
      | Some t_coer -> t_coer
      | None -> { ty_coer with ty = apply_sub_ct_ty sub ty_coer.ty })
  | Coercion.ReflTy -> Coercion.reflTy (apply_sub_ty sub (fst ty_coer.ty))
  | ArrowCoercion (tycoer1, dirtycoer) ->
      Coercion.arrowCoercion
        (apply_sub_tycoer sub tycoer1, apply_sub_dirtycoer sub dirtycoer)
  | HandlerCoercion (dirtycoer1, dirtycoer2) ->
      Coercion.handlerCoercion
        (apply_sub_dirtycoer sub dirtycoer1, apply_sub_dirtycoer sub dirtycoer2)
  | TupleCoercion tcl ->
      Coercion.tupleCoercion (List.map (fun x -> apply_sub_tycoer sub x) tcl)
  | ApplyCoercion { ty_name; tcoers } ->
      Coercion.applyCoercion
        ( ty_name,
          TyParam.Map.map
            (fun (x, variance) -> (apply_sub_tycoer sub x, variance))
            tcoers )

and apply_sub_dirtcoer sub drt_coer =
  match drt_coer.term with
  | Coercion.ReflDirt | Empty ->
      { drt_coer with ty = apply_sub_ct_dirt sub drt_coer.ty }
  | Coercion.DirtCoercionVar p -> (
      match
        Type.DirtCoercionParam.Map.find_opt p sub.dirt_var_to_dirt_coercions
      with
      | Some dc -> dc
      | None -> { drt_coer with ty = apply_sub_ct_dirt sub drt_coer.ty })
  | UnionDirt (es, dirt_coer1) ->
      Coercion.unionDirt (es, apply_sub_dirtcoer sub dirt_coer1)

and apply_sub_dirtycoer (sub : t) { term = ty_coer, dirt_coer; _ } :
    Coercion.dirty_coercion =
  let ty_coer' = apply_sub_tycoer sub ty_coer
  and dirt_coer' = apply_sub_dirtcoer sub dirt_coer in
  Coercion.bangCoercion (ty_coer', dirt_coer')

let apply_substitutions_to_type = apply_sub_ty
let apply_substitutions_to_dirt = apply_sub_dirt
let apply_substitutions_to_skeleton = apply_sub_skel

(* Other type information *)

(* Printing and other debug stuff *)

let print subs =
  [
    subs.type_param_to_type_coercions
    |> Type.TyCoercionParam.Map.print Coercion.print_ty_coercion;
    subs.type_param_to_type_subs |> Type.TyParam.Map.print Type.print_ty;
    subs.dirt_var_to_dirt_subs |> Dirt.Param.Map.print Dirt.print;
    subs.dirt_var_to_dirt_coercions
    |> Type.DirtCoercionParam.Map.print Coercion.print_dirt_coercion;
    subs.skel_param_to_skel_subs |> Skeleton.Param.Map.print Skeleton.print;
  ]
  |> Print.printer_sequence ", "

let of_tydef_parameters (params : Type.tydef_params) =
  let skel_params' =
    Skeleton.Param.Set.elements params.skel_params
    |> List.map (fun s -> (s, Skeleton.Param.refresh s))
    |> Skeleton.Param.Map.of_bindings
  and dirt_params' =
    Dirt.Param.Set.elements params.dirt_params
    |> List.map (fun d -> (d, Dirt.Param.refresh d))
    |> Dirt.Param.Map.of_bindings
  in
  let subst =
    {
      empty with
      dirt_var_to_dirt_subs =
        Dirt.Param.Map.map (fun d' -> Dirt.no_effect d') dirt_params';
      skel_param_to_skel_subs =
        Skeleton.Param.Map.map (fun s' -> Skeleton.Param s') skel_params';
    }
  in
  let ty_params' =
    Type.TyParam.Map.bindings params.type_params
    |> List.map (fun (p, (skel, variance)) ->
           ( p,
             ( TyParam.refresh p,
               (apply_substitutions_to_skeleton subst skel, variance) ) ))
  in
  let params' =
    {
      type_params = ty_params' |> List.map snd |> Type.TyParam.Map.of_bindings;
      dirt_params =
        Dirt.Param.Map.bindings dirt_params'
        |> List.map fst |> Dirt.Param.Set.of_list;
      skel_params =
        Skeleton.Param.Map.bindings skel_params'
        |> List.map fst |> Skeleton.Param.Set.of_list;
    }
  and subst' =
    {
      subst with
      type_param_to_type_subs =
        List.map
          (fun (k, (p', (skel, _))) -> (k, Type.tyParam p' skel))
          ty_params'
        |> Type.TyParam.Map.of_bindings;
    }
  in
  ( params',
    subst',
    List.map (fun (p, (p', _)) -> (p, p')) ty_params' |> TyParam.Map.of_bindings
  )

let of_parameters (params : Type.Params.t) =
  let skel_params' =
    Skeleton.Param.Set.elements params.skel_params
    |> List.map (fun s -> (s, Skeleton.Param.refresh s))
    |> Skeleton.Param.Map.of_bindings
  and dirt_params' =
    Dirt.Param.Set.elements params.dirt_params
    |> List.map (fun d -> (d, Dirt.Param.refresh d))
    |> Dirt.Param.Map.of_bindings
  in
  let subst =
    {
      empty with
      dirt_var_to_dirt_subs =
        Dirt.Param.Map.map (fun d' -> Dirt.no_effect d') dirt_params';
      skel_param_to_skel_subs =
        Skeleton.Param.Map.map (fun s' -> Skeleton.Param s') skel_params';
    }
  in
  let ty_params' =
    Type.TyParam.Map.bindings params.ty_params
    |> List.map (fun (p, skel) ->
           ( p,
             (Type.TyParam.refresh p, apply_substitutions_to_skeleton subst skel)
           ))
  in
  let params' =
    {
      Type.Params.ty_params =
        ty_params' |> List.map snd |> Type.TyParam.Map.of_bindings;
      dirt_params =
        Dirt.Param.Map.bindings dirt_params'
        |> List.map fst |> Dirt.Param.Set.of_list;
      skel_params =
        Skeleton.Param.Map.bindings skel_params'
        |> List.map fst |> Skeleton.Param.Set.of_list;
    }
  and subst' =
    {
      subst with
      type_param_to_type_subs =
        List.map (fun (k, (p', skel)) -> (k, Type.tyParam p' skel)) ty_params'
        |> Type.TyParam.Map.of_bindings;
    }
  in
  (params', subst')

let apply_substitutions_to_substitution new_sub old_sub =
  {
    type_param_to_type_coercions =
      Type.TyCoercionParam.Map.map (apply_sub_tycoer new_sub)
        old_sub.type_param_to_type_coercions;
    type_param_to_type_subs =
      Type.TyParam.Map.map (apply_sub_ty new_sub)
        old_sub.type_param_to_type_subs;
    dirt_var_to_dirt_coercions =
      Type.DirtCoercionParam.Map.map
        (apply_sub_dirtcoer new_sub)
        old_sub.dirt_var_to_dirt_coercions;
    dirt_var_to_dirt_subs =
      Dirt.Param.Map.map (apply_sub_dirt new_sub) old_sub.dirt_var_to_dirt_subs;
    skel_param_to_skel_subs =
      Skeleton.Param.Map.map (apply_sub_skel new_sub)
        old_sub.skel_param_to_skel_subs;
  }

let merge new_sub old_sub =
  let old_sub' = apply_substitutions_to_substitution new_sub old_sub in
  {
    type_param_to_type_coercions =
      Type.TyCoercionParam.Map.compatible_union
        new_sub.type_param_to_type_coercions
        old_sub'.type_param_to_type_coercions;
    type_param_to_type_subs =
      Type.TyParam.Map.compatible_union new_sub.type_param_to_type_subs
        old_sub'.type_param_to_type_subs;
    dirt_var_to_dirt_coercions =
      Type.DirtCoercionParam.Map.compatible_union
        new_sub.dirt_var_to_dirt_coercions old_sub'.dirt_var_to_dirt_coercions;
    dirt_var_to_dirt_subs =
      Dirt.Param.Map.compatible_union new_sub.dirt_var_to_dirt_subs
        old_sub'.dirt_var_to_dirt_subs;
    skel_param_to_skel_subs =
      Skeleton.Param.Map.compatible_union new_sub.skel_param_to_skel_subs
        old_sub'.skel_param_to_skel_subs;
  }

let add_type_coercion_e parameter t_coercion =
  {
    empty with
    type_param_to_type_coercions =
      Type.TyCoercionParam.Map.singleton parameter t_coercion;
  }

let add_type_coercion parameter t_coercion sub =
  assert (
    Coercion.equal_ty_coercion t_coercion (apply_sub_tycoer sub t_coercion));
  merge (add_type_coercion_e parameter t_coercion) sub

let add_type_substitution_e parameter ty =
  {
    empty with
    type_param_to_type_subs = Type.TyParam.Map.singleton parameter ty;
  }

let add_type_substitution parameter ty sub =
  assert (ty = apply_sub_ty sub ty);
  merge (add_type_substitution_e parameter ty) sub

let add_dirt_var_coercion_e dirt_var dc =
  {
    empty with
    dirt_var_to_dirt_coercions =
      Type.DirtCoercionParam.Map.singleton dirt_var dc;
  }

let add_dirt_var_coercion dirt_var dc sub =
  assert (dc = apply_sub_dirtcoer sub dc);
  merge (add_dirt_var_coercion_e dirt_var dc) sub

let add_dirt_substitution_e dirt_var dirt =
  { empty with dirt_var_to_dirt_subs = Dirt.Param.Map.singleton dirt_var dirt }

let add_dirt_substitution dirt_var dirt sub =
  assert (dirt = apply_sub_dirt sub dirt);
  merge (add_dirt_substitution_e dirt_var dirt) sub

let empty_dirt_substitution empty_dirt_params =
  Dirt.Param.Set.fold
    (fun t sbst -> add_dirt_substitution t Dirt.empty sbst)
    empty_dirt_params empty

let add_skel_param_substitution_e param skel =
  {
    empty with
    skel_param_to_skel_subs = Skeleton.Param.Map.singleton param skel;
  }

let add_skel_param_substitution param skel sub =
  assert (skel = apply_sub_skel sub skel);
  merge (add_skel_param_substitution_e param skel) sub
