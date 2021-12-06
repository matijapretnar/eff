(** Substitution implementation *)

open Utils

type t = {
  type_param_to_type_coercions :
    Coercion.ty_coercion Type.TyCoercionParam.Map.t;
  type_param_to_type_subs : Type.ty Type.TyParam.Map.t;
  dirt_var_to_dirt_coercions :
    Coercion.dirt_coercion Type.DirtCoercionParam.Map.t;
  dirt_var_to_dirt_subs : Type.dirt Type.DirtParam.Map.t;
  skel_param_to_skel_subs : Type.skeleton Type.SkelParam.Map.t;
}

let empty =
  {
    type_param_to_type_coercions = Type.TyCoercionParam.Map.empty;
    type_param_to_type_subs = Type.TyParam.Map.empty;
    dirt_var_to_dirt_coercions = Type.DirtCoercionParam.Map.empty;
    dirt_var_to_dirt_subs = Type.DirtParam.Map.empty;
    skel_param_to_skel_subs = Type.SkelParam.Map.empty;
  }

let is_empty sub =
  Type.TyCoercionParam.Map.is_empty sub.type_param_to_type_coercions
  && Type.TyParam.Map.is_empty sub.type_param_to_type_subs
  && Type.DirtCoercionParam.Map.is_empty sub.dirt_var_to_dirt_coercions
  && Type.DirtParam.Map.is_empty sub.dirt_var_to_dirt_subs
  && Type.SkelParam.Map.is_empty sub.skel_param_to_skel_subs

(* Substitution application *)
open Type

let apply_sub_dirt sub dirt =
  match dirt.row with
  | ParamRow p -> (
      match Type.DirtParam.Map.find_opt p sub.dirt_var_to_dirt_subs with
      | Some drt2 -> Type.add_effects dirt.effect_set drt2
      | None -> dirt)
  | EmptyRow -> dirt

let rec apply_sub_skel sub skeleton =
  match skeleton with
  | SkelParam p -> (
      match Type.SkelParam.Map.find_opt p sub.skel_param_to_skel_subs with
      | Some sk1 -> sk1
      | None -> skeleton)
  | SkelBasic _ -> skeleton
  | SkelArrow (sk1, sk2) ->
      SkelArrow (apply_sub_skel sub sk1, apply_sub_skel sub sk2)
  | SkelHandler (sk1, sk2) ->
      SkelHandler (apply_sub_skel sub sk1, apply_sub_skel sub sk2)
  (* Really consider other cases *)
  | SkelApply (t, l) -> SkelApply (t, List.map (apply_sub_skel sub) l)
  | SkelTuple skels -> SkelTuple (List.map (apply_sub_skel sub) skels)

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
      Type.apply (ty_name, List.map (apply_sub_ty sub) ty_args)
  | Tuple ttyl -> Type.tuple (List.map (fun x -> apply_sub_ty sub x) ttyl)
  | Handler (tydrty1, tydrty2) ->
      Type.handler
        (apply_sub_dirty_ty sub tydrty1, apply_sub_dirty_ty sub tydrty2)
  | TyBasic p -> tyBasic p

and apply_sub_dirty_ty sub (ty, drt) =
  (apply_sub_ty sub ty, apply_sub_dirt sub drt)

and apply_sub_abs_ty sub (ty, drty) =
  (apply_sub_ty sub ty, apply_sub_dirty_ty sub drty)

and apply_sub_abs2_ty sub (ty1, ty2, drty) =
  (apply_sub_ty sub ty1, apply_sub_ty sub ty2, apply_sub_dirty_ty sub drty)

and apply_sub_ct_ty sub (ty1, ty2) = (apply_sub_ty sub ty1, apply_sub_ty sub ty2)

and apply_sub_ct_dirt sub (drt1, drt2) =
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
  | ApplyCoercion (ty_name, tcl) ->
      Coercion.applyCoercion
        (ty_name, List.map (fun x -> apply_sub_tycoer sub x) tcl)

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

let printy ?at_level ppf = Print.print ?at_level ppf

let print_type_coercion p t ppf =
  printy ppf "%t ↦ %t"
    (Type.TyCoercionParam.print p)
    (Coercion.print_ty_coercion t)

let print_type_param_to_type p t ppf =
  printy ppf "%t ↦ %t" (Type.TyParam.print p) (Type.print_ty t)

let print_dirt_var_sub p t ppf =
  printy ppf "%t ↦ %t" (Type.DirtParam.print p) (Type.print_dirt t)

let print_dirt_var_coercion p t ppf =
  printy ppf "%t ↦ %t"
    (Type.DirtCoercionParam.print p)
    (Coercion.print_dirt_coercion t)

let print_skel_param_sub p t ppf =
  printy ppf "%t ↦ %t" (Type.SkelParam.print p) (Type.print_skeleton t)

let print subs =
  [
    subs.type_param_to_type_coercions |> Type.TyCoercionParam.Map.bindings
    |> List.map (fun (x, y) -> print_type_coercion x y);
    subs.type_param_to_type_subs |> Type.TyParam.Map.bindings
    |> List.map (fun (x, y) -> print_type_param_to_type x y);
    subs.dirt_var_to_dirt_subs |> Type.DirtParam.Map.bindings
    |> List.map (fun (x, y) -> print_dirt_var_sub x y);
    subs.dirt_var_to_dirt_coercions |> Type.DirtCoercionParam.Map.bindings
    |> List.map (fun (x, y) -> print_dirt_var_coercion x y);
    subs.skel_param_to_skel_subs |> Type.SkelParam.Map.bindings
    |> List.map (fun (x, y) -> print_skel_param_sub x y);
  ]
  |> List.concat
  |> Print.printer_sequence ", "

let of_parameters (params : Type.Params.t) =
  let skel_params' =
    Type.SkelParam.Set.elements params.skel_params
    |> List.map (fun s -> (s, Type.SkelParam.refresh s))
    |> Type.SkelParam.Map.of_bindings
  and dirt_params' =
    Type.DirtParam.Set.elements params.dirt_params
    |> List.map (fun d -> (d, Type.DirtParam.refresh d))
    |> Type.DirtParam.Map.of_bindings
  in
  let subst =
    {
      empty with
      dirt_var_to_dirt_subs =
        Type.DirtParam.Map.map (fun d' -> Type.no_effect_dirt d') dirt_params';
      skel_param_to_skel_subs =
        Type.SkelParam.Map.map (fun s' -> Type.SkelParam s') skel_params';
    }
  in
  (* Print.debug "SUBSTITUTION: %t" (print subst); *)
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
        Type.DirtParam.Map.bindings dirt_params'
        |> List.map fst |> Type.DirtParam.Set.of_list;
      skel_params =
        Type.SkelParam.Map.bindings skel_params'
        |> List.map fst |> Type.SkelParam.Set.of_list;
    }
  and subst' =
    {
      subst with
      type_param_to_type_subs =
        List.map (fun (k, (p', skel)) -> (k, Type.tyParam p' skel)) ty_params'
        |> Type.TyParam.Map.of_bindings;
    }
  in
  (* Print.debug "SUBSTITUTION': %t" (print subst'); *)
  (params', subst')

let merge new_sub old_sub =
  {
    type_param_to_type_coercions =
      Type.TyCoercionParam.Map.compatible_union
        new_sub.type_param_to_type_coercions
        (Type.TyCoercionParam.Map.map (apply_sub_tycoer new_sub)
           old_sub.type_param_to_type_coercions);
    type_param_to_type_subs =
      Type.TyParam.Map.compatible_union new_sub.type_param_to_type_subs
        (Type.TyParam.Map.map (apply_sub_ty new_sub)
           old_sub.type_param_to_type_subs);
    dirt_var_to_dirt_coercions =
      Type.DirtCoercionParam.Map.compatible_union
        new_sub.dirt_var_to_dirt_coercions
        (Type.DirtCoercionParam.Map.map
           (apply_sub_dirtcoer new_sub)
           old_sub.dirt_var_to_dirt_coercions);
    dirt_var_to_dirt_subs =
      Type.DirtParam.Map.compatible_union new_sub.dirt_var_to_dirt_subs
        (Type.DirtParam.Map.map (apply_sub_dirt new_sub)
           old_sub.dirt_var_to_dirt_subs);
    skel_param_to_skel_subs =
      Type.SkelParam.Map.compatible_union new_sub.skel_param_to_skel_subs
        (Type.SkelParam.Map.map (apply_sub_skel new_sub)
           old_sub.skel_param_to_skel_subs);
  }

let add_type_coercion_e parameter t_coercion =
  {
    empty with
    type_param_to_type_coercions =
      Type.TyCoercionParam.Map.singleton parameter t_coercion;
  }

let add_type_coercion parameter t_coercion sub =
  assert (t_coercion = apply_sub_tycoer sub t_coercion);
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
  {
    empty with
    dirt_var_to_dirt_subs = Type.DirtParam.Map.singleton dirt_var dirt;
  }

let add_dirt_substitution dirt_var dirt sub =
  assert (dirt = apply_sub_dirt sub dirt);
  merge (add_dirt_substitution_e dirt_var dirt) sub

let empty_dirt_substitution empty_dirt_params =
  Type.DirtParam.Set.fold
    (fun t sbst -> add_dirt_substitution t Type.empty_dirt sbst)
    empty_dirt_params empty

let add_skel_param_substitution_e param skel =
  {
    empty with
    skel_param_to_skel_subs = Type.SkelParam.Map.singleton param skel;
  }

let add_skel_param_substitution param skel sub =
  assert (skel = apply_sub_skel sub skel);
  merge (add_skel_param_substitution_e param skel) sub
