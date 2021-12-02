(** Substitution implementation *)

open Utils

type t = {
  type_param_to_type_coercions :
    (Type.TyCoercionParam.t, Coercion.ty_coercion) Assoc.t;
  type_param_to_type_subs : (CoreTypes.TyParam.t, Type.ty) Assoc.t;
  dirt_var_to_dirt_coercions :
    (Type.DirtCoercionParam.t, Coercion.dirt_coercion) Assoc.t;
  dirt_var_to_dirt_subs : (Type.DirtParam.t, Type.dirt) Assoc.t;
  skel_param_to_skel_subs : (Type.SkelParam.t, Type.skeleton) Assoc.t;
}

let empty =
  {
    type_param_to_type_coercions = Assoc.empty;
    dirt_var_to_dirt_coercions = Assoc.empty;
    type_param_to_type_subs = Assoc.empty;
    dirt_var_to_dirt_subs = Assoc.empty;
    skel_param_to_skel_subs = Assoc.empty;
  }

let is_empty sub =
  Assoc.is_empty sub.type_param_to_type_coercions
  && Assoc.is_empty sub.dirt_var_to_dirt_coercions
  && Assoc.is_empty sub.type_param_to_type_subs
  && Assoc.is_empty sub.dirt_var_to_dirt_subs
  && Assoc.is_empty sub.skel_param_to_skel_subs

(* Substitution application *)
open Type

let apply_sub_dirt sub dirt =
  match dirt.row with
  | ParamRow p -> (
      match Assoc.lookup p sub.dirt_var_to_dirt_subs with
      | Some drt2 -> Type.add_effects dirt.effect_set drt2
      | None -> dirt)
  | EmptyRow -> dirt

let rec apply_sub_skel sub skeleton =
  match skeleton with
  | SkelParam p -> (
      match Assoc.lookup p sub.skel_param_to_skel_subs with
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
      match Assoc.lookup typ1 sub.type_param_to_type_subs with
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
      match Assoc.lookup p sub.type_param_to_type_coercions with
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
      match Assoc.lookup p sub.dirt_var_to_dirt_coercions with
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
  printy ppf "%t ↦ %t" (CoreTypes.TyParam.print p) (Type.print_ty t)

let print_dirt_var_sub p t ppf =
  printy ppf "%t ↦ %t" (Type.DirtParam.print p) (Type.print_dirt t)

let print_dirt_var_coercion p t ppf =
  printy ppf "%t ↦ %t"
    (Type.DirtCoercionParam.print p)
    (Coercion.print_dirt_coercion t)

let print_skel_param_sub p t ppf =
  printy ppf "%t ↦ %t" (Type.SkelParam.print p) (Type.print_skeleton t)

let print_sub_list subs ppf =
  Assoc.iter
    (fun (x, y) -> Print.print ppf "%t, " (print_type_coercion x y))
    subs.type_param_to_type_coercions;
  Assoc.iter
    (fun (x, y) -> Print.print ppf "%t, " (print_type_param_to_type x y))
    subs.type_param_to_type_subs;
  Assoc.iter
    (fun (x, y) -> Print.print ppf "%t, " (print_dirt_var_sub x y))
    subs.dirt_var_to_dirt_subs;
  Assoc.iter
    (fun (x, y) -> Print.print ppf "%t, " (print_dirt_var_coercion x y))
    subs.dirt_var_to_dirt_coercions;
  Assoc.iter
    (fun (x, y) -> Print.print ppf "%t, " (print_skel_param_sub x y))
    subs.skel_param_to_skel_subs

let print_substitutions subs ppf = print_sub_list subs ppf

let of_parameters (params : Type.Params.t) =
  let skel_params' =
    Type.SkelParamSet.elements params.skel_params
    |> List.map (fun s -> (s, Type.SkelParam.refresh s))
    |> Assoc.of_list
  and dirt_params' =
    Type.DirtParamSet.elements params.dirt_params
    |> List.map (fun d -> (d, Type.DirtParam.refresh d))
    |> Assoc.of_list
  in
  let subst =
    {
      empty with
      dirt_var_to_dirt_subs =
        Assoc.map (fun d' -> Type.no_effect_dirt d') dirt_params';
      skel_param_to_skel_subs =
        Assoc.map (fun s' -> Type.SkelParam s') skel_params';
    }
  in
  (* Print.debug "SUBSTITUTION: %t" (print_substitutions subst); *)
  let ty_params' =
    Type.TyParamMap.bindings params.ty_params
    |> List.map (fun (p, skel) ->
           ( p,
             ( CoreTypes.TyParam.refresh p,
               apply_substitutions_to_skeleton subst skel ) ))
    |> Assoc.of_list
  in
  let params' =
    {
      Type.Params.ty_params =
        Assoc.values_of ty_params' |> List.to_seq |> Type.TyParamMap.of_seq;
      dirt_params =
        Assoc.values_of dirt_params' |> List.to_seq |> Type.DirtParamSet.of_seq;
      skel_params =
        Assoc.values_of skel_params' |> List.to_seq |> Type.SkelParamSet.of_seq;
    }
  and subst' =
    {
      subst with
      type_param_to_type_subs =
        Assoc.map (fun (p', skel) -> Type.tyParam p' skel) ty_params';
    }
  in
  (* Print.debug "SUBSTITUTION': %t" (print_substitutions subst'); *)
  (params', subst')

let update_and_merge updater new_map old_map =
  Assoc.concat new_map (Assoc.map updater old_map)

let merge new_sub old_sub =
  {
    type_param_to_type_coercions =
      update_and_merge (apply_sub_tycoer new_sub)
        new_sub.type_param_to_type_coercions
        old_sub.type_param_to_type_coercions;
    type_param_to_type_subs =
      update_and_merge (apply_sub_ty new_sub) new_sub.type_param_to_type_subs
        old_sub.type_param_to_type_subs;
    dirt_var_to_dirt_coercions =
      update_and_merge
        (apply_sub_dirtcoer new_sub)
        new_sub.dirt_var_to_dirt_coercions old_sub.dirt_var_to_dirt_coercions;
    dirt_var_to_dirt_subs =
      update_and_merge (apply_sub_dirt new_sub) new_sub.dirt_var_to_dirt_subs
        old_sub.dirt_var_to_dirt_subs;
    skel_param_to_skel_subs =
      update_and_merge (apply_sub_skel new_sub) new_sub.skel_param_to_skel_subs
        old_sub.skel_param_to_skel_subs;
  }

let add_type_coercion_e parameter t_coercion =
  {
    empty with
    type_param_to_type_coercions = Assoc.update parameter t_coercion Assoc.empty;
  }

let add_type_coercion parameter t_coercion sub =
  assert (t_coercion = apply_sub_tycoer sub t_coercion);
  merge (add_type_coercion_e parameter t_coercion) sub

let add_type_substitution_e parameter ty =
  { empty with type_param_to_type_subs = Assoc.update parameter ty Assoc.empty }

let add_type_substitution parameter ty sub =
  assert (ty = apply_sub_ty sub ty);
  merge (add_type_substitution_e parameter ty) sub

let add_dirt_var_coercion_e dirt_var dc =
  {
    empty with
    dirt_var_to_dirt_coercions = Assoc.update dirt_var dc Assoc.empty;
  }

let add_dirt_var_coercion dirt_var dc sub =
  assert (dc = apply_sub_dirtcoer sub dc);
  merge (add_dirt_var_coercion_e dirt_var dc) sub

let add_dirt_substitution_e dirt_var dirt =
  { empty with dirt_var_to_dirt_subs = Assoc.update dirt_var dirt Assoc.empty }

let add_dirt_substitution dirt_var dirt sub =
  assert (dirt = apply_sub_dirt sub dirt);
  merge (add_dirt_substitution_e dirt_var dirt) sub

let empty_dirt_substitution empty_dirt_params =
  Type.DirtParamSet.fold
    (fun t sbst -> add_dirt_substitution t Type.empty_dirt sbst)
    empty_dirt_params empty

let add_skel_param_substitution_e param skel =
  { empty with skel_param_to_skel_subs = Assoc.update param skel Assoc.empty }

let add_skel_param_substitution param skel sub =
  assert (skel = apply_sub_skel sub skel);
  merge (add_skel_param_substitution_e param skel) sub
