(** Substitution implementation *)

open Utils
module CoreTypes = Language.CoreTypes

type t = {
  type_param_to_type_coercions :
    (Type.TyCoercionParam.t, Constraint.ty_coercion) Assoc.t;
  type_param_to_type_subs : (CoreTypes.TyParam.t, Type.ty) Assoc.t;
  dirt_var_to_dirt_coercions :
    (Type.DirtCoercionParam.t, Constraint.dirt_coercion) Assoc.t;
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

let add_to_empty f a b = f a b empty

let add_type_coercion parameter t_coercion sub =
  {
    sub with
    type_param_to_type_coercions =
      Assoc.update parameter t_coercion sub.type_param_to_type_coercions;
  }

let add_type_coercion_e parameter t_coercion =
  add_to_empty add_type_coercion parameter t_coercion

let add_type_substitution parameter ty sub =
  {
    sub with
    type_param_to_type_subs =
      Assoc.update parameter ty sub.type_param_to_type_subs;
  }

let add_type_substitution_e parameter ty =
  add_to_empty add_type_substitution parameter ty

let add_dirt_var_coercion dirt_var dc sub =
  {
    sub with
    dirt_var_to_dirt_coercions =
      Assoc.update dirt_var dc sub.dirt_var_to_dirt_coercions;
  }

let add_dirt_var_coercion_e dirt_var dc =
  add_to_empty add_dirt_var_coercion dirt_var dc

let add_dirt_substitution dirt_var t_coercion sub =
  {
    sub with
    dirt_var_to_dirt_subs =
      Assoc.update dirt_var t_coercion sub.dirt_var_to_dirt_subs;
  }

let add_dirt_substitution_e dirt_var t_coercion =
  add_to_empty add_dirt_substitution dirt_var t_coercion

let add_skel_param_substitution param skel sub =
  {
    sub with
    skel_param_to_skel_subs =
      Assoc.update param skel sub.skel_param_to_skel_subs;
  }

let add_skel_param_substitution_e param skel =
  add_to_empty add_skel_param_substitution param skel

let merge subs1 subs2 =
  {
    type_param_to_type_coercions =
      Assoc.concat subs1.type_param_to_type_coercions
        subs2.type_param_to_type_coercions;
    type_param_to_type_subs =
      Assoc.concat subs1.type_param_to_type_subs subs2.type_param_to_type_subs;
    dirt_var_to_dirt_coercions =
      Assoc.concat subs1.dirt_var_to_dirt_coercions
        subs2.dirt_var_to_dirt_coercions;
    dirt_var_to_dirt_subs =
      Assoc.concat subs1.dirt_var_to_dirt_subs subs2.dirt_var_to_dirt_subs;
    skel_param_to_skel_subs =
      Assoc.concat subs1.skel_param_to_skel_subs subs2.skel_param_to_skel_subs;
  }

(* Substitution application *)
open Type
open Term

let rec apply_sub_dirt sub dirt =
  match dirt.row with
  | ParamRow p -> (
      match Assoc.lookup p sub.dirt_var_to_dirt_subs with
      | Some drt2 -> apply_sub_dirt sub (Type.add_effects dirt.effect_set drt2)
      | None -> dirt)
  | EmptyRow -> dirt

let rec apply_sub_skel sub skeleton =
  match skeleton with
  | SkelParam p -> (
      match Assoc.lookup p sub.skel_param_to_skel_subs with
      | Some sk1 -> apply_sub_skel sub sk1
      | None -> skeleton)
  | SkelBasic _ -> skeleton
  | SkelArrow (sk1, sk2) ->
      SkelArrow (apply_sub_skel sub sk1, apply_sub_skel sub sk2)
  | SkelHandler (sk1, sk2) ->
      SkelHandler (apply_sub_skel sub sk1, apply_sub_skel sub sk2)
  (* Really consider other cases *)
  | SkelApply (t, l) -> SkelApply (t, List.map (apply_sub_skel sub) l)
  | SkelTuple skels -> SkelTuple (List.map (apply_sub_skel sub) skels)

let rec apply_sub_ty sub = function
  | TyParam (typ1, skel) -> (
      match Assoc.lookup typ1 sub.type_param_to_type_subs with
      | Some ttype ->
          apply_sub_ty sub ttype
          (* We don't assume that substitutions are fully expanded *)
      | None -> TyParam (typ1, apply_sub_skel sub skel))
  | Arrow (tty1, tty2) ->
      Arrow (apply_sub_ty sub tty1, apply_sub_dirty_ty sub tty2)
  | Apply (ty_name, tys) -> Apply (ty_name, List.map (apply_sub_ty sub) tys)
  | Tuple ttyl -> Tuple (List.map (fun x -> apply_sub_ty sub x) ttyl)
  | Handler (tydrty1, tydrty2) ->
      Handler (apply_sub_dirty_ty sub tydrty1, apply_sub_dirty_ty sub tydrty2)
  | TyBasic p -> TyBasic p

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
  let ty' = apply_sub_ct_ty sub ty_coer.ty in
  match ty_coer.term with
  | Constraint.TyCoercionVar p -> (
      match Assoc.lookup p sub.type_param_to_type_coercions with
      | Some t_coer -> apply_sub_tycoer sub t_coer
      | None -> { ty_coer with ty = ty' })
  | _ -> { term = apply_sub_tycoer' sub ty_coer.term; ty = ty' }

and apply_sub_tycoer' sub ty_coer =
  match ty_coer with
  | TyCoercionVar _ -> assert false
  | Constraint.ReflTy -> Constraint.ReflTy
  | ArrowCoercion (tycoer1, dirtycoer) ->
      ArrowCoercion
        (apply_sub_tycoer sub tycoer1, apply_sub_dirtycoer sub dirtycoer)
  | HandlerCoercion (dirtycoer1, dirtycoer2) ->
      HandlerCoercion
        (apply_sub_dirtycoer sub dirtycoer1, apply_sub_dirtycoer sub dirtycoer2)
  | TupleCoercion tcl ->
      TupleCoercion (List.map (fun x -> apply_sub_tycoer sub x) tcl)
  | ApplyCoercion (ty_name, tcl) ->
      ApplyCoercion (ty_name, List.map (fun x -> apply_sub_tycoer sub x) tcl)

and apply_sub_dirtcoer sub drt_coer =
  let drt' = apply_sub_ct_dirt sub drt_coer.ty in
  match drt_coer.term with
  | Constraint.DirtCoercionVar p -> (
      match Assoc.lookup p sub.dirt_var_to_dirt_coercions with
      | Some dc -> apply_sub_dirtcoer sub dc
      | None -> { drt_coer with ty = drt' })
  | _ -> { term = apply_sub_dirtcoer' sub drt_coer.term; ty = drt' }

and apply_sub_dirtcoer' sub ty_coer =
  match ty_coer with
  | Constraint.ReflDirt -> ty_coer
  | DirtCoercionVar _ -> assert false
  | Empty -> Empty
  | UnionDirt (es, dirt_coer1) ->
      UnionDirt (es, apply_sub_dirtcoer sub dirt_coer1)

and apply_sub_dirtycoer (sub : t) { term = ty_coer, dirt_coer; _ } :
    Constraint.dirty_coercion =
  let ty_coer' = apply_sub_tycoer sub ty_coer
  and dirt_coer' = apply_sub_dirtcoer sub dirt_coer in
  Constraint.bangCoercion (ty_coer', dirt_coer')

let rec apply_sub_comp sub computation =
  {
    term = apply_sub_comp' sub computation.term;
    ty = apply_sub_dirty_ty sub computation.ty;
  }

and apply_sub_comp' sub computation =
  match computation with
  | Value e -> Value (apply_sub_exp sub e)
  | LetVal (e1, abs) -> LetVal (apply_sub_exp sub e1, apply_sub_abs sub abs)
  | LetRec (defs, c1) ->
      LetRec (apply_sub_definitions sub defs, apply_sub_comp sub c1)
  | Match (e, alist) ->
      Match (apply_sub_exp sub e, List.map (apply_sub_abs sub) alist)
  | Apply (e1, e2) -> Apply (apply_sub_exp sub e1, apply_sub_exp sub e2)
  | Handle (e1, c1) -> Handle (apply_sub_exp sub e1, apply_sub_comp sub c1)
  | Call (effekt, e1, abs) ->
      Call (effekt, apply_sub_exp sub e1, apply_sub_abs sub abs)
  | Bind (c1, a1) -> Bind (apply_sub_comp sub c1, apply_sub_abs sub a1)
  | CastComp (c1, dc1) ->
      CastComp (apply_sub_comp sub c1, apply_sub_dirtycoer sub dc1)

and apply_sub_exp sub expression =
  {
    term = apply_sub_exp' sub expression.term;
    ty = apply_sub_ty sub expression.ty;
  }

and apply_sub_exp' sub expression =
  match expression with
  | Var v -> Var v
  | Const c -> Const c
  | Tuple elist -> Tuple (List.map (fun x -> apply_sub_exp sub x) elist)
  | Variant (lbl, e1) -> Variant (lbl, Option.map (apply_sub_exp sub) e1)
  | Lambda abs -> Lambda (apply_sub_abs sub abs)
  | Handler h -> Handler (apply_sub_handler sub h)
  | CastExp (e1, tc1) -> CastExp (apply_sub_exp sub e1, apply_sub_tycoer sub tc1)
  | _ -> failwith __LOC__

and apply_sub_abs sub abs =
  { term = apply_sub_abs' sub abs.term; ty = apply_sub_abs_ty sub abs.ty }

and apply_sub_abs' sub (p, c) = (apply_sub_pat sub p, apply_sub_comp sub c)

and apply_sub_pat sub pat =
  { term = apply_sub_pat' sub pat.term; ty = apply_sub_ty sub pat.ty }

and apply_sub_pat' sub pat =
  match pat with
  | PVar _ -> pat
  | PAs (p, x) -> PAs (apply_sub_pat sub p, x)
  | PTuple ps -> PTuple (List.map (apply_sub_pat sub) ps)
  | PRecord flds -> PRecord (Assoc.map (apply_sub_pat sub) flds)
  | PVariant (lbl, pat) -> PVariant (lbl, Option.map (apply_sub_pat sub) pat)
  | PConst _ -> pat
  | PNonbinding -> pat

and apply_sub_definitions sub defs = Assoc.map (apply_sub_abs sub) defs

and apply_sub_abs2 sub abs2 =
  { term = apply_sub_abs2' sub abs2.term; ty = apply_sub_abs2_ty sub abs2.ty }

and apply_sub_abs2' sub (p1, p2, c) =
  (apply_sub_pat sub p1, apply_sub_pat sub p2, apply_sub_comp sub c)

and apply_sub_handler sub h =
  let drty1, drty2 = h.ty in
  let eff_clauses = h.term.effect_clauses in
  let new_value_clause = apply_sub_abs sub h.term.value_clause in
  let new_eff_clauses =
    Assoc.map (fun abs2 -> apply_sub_abs2 sub abs2) eff_clauses.effect_part
  in
  {
    term =
      {
        effect_clauses = { eff_clauses with effect_part = new_eff_clauses };
        value_clause = new_value_clause;
      };
    ty = (apply_sub_dirty_ty sub drty1, apply_sub_dirty_ty sub drty2);
  }

let apply_substitutions_to_computation = apply_sub_comp

let apply_substitutions_to_expression = apply_sub_exp

let apply_substitutions_to_abstraction = apply_sub_abs

let apply_substitutions_to_type = apply_sub_ty

let apply_substitutions_to_dirt = apply_sub_dirt

let apply_substitutions_to_skeleton = apply_sub_skel

let apply_sub1 subs cons =
  match cons with
  | Constraint.TyOmega (coer_p, (ty1, ty2)) ->
      Constraint.TyOmega (coer_p, (apply_sub_ty subs ty1, apply_sub_ty subs ty2))
  | Constraint.DirtOmega (coer_p, (drt1, drt2)) ->
      Constraint.DirtOmega
        (coer_p, (apply_sub_dirt subs drt1, apply_sub_dirt subs drt2))
  | _ -> cons

let apply_substitutions_to_constraints subs c_list =
  List.map (apply_sub1 subs) c_list

(* Other type information *)

(* Printing and other debug stuff *)

let printy ?at_level ppf = Print.print ?at_level ppf

let print_type_coercion p t ppf =
  printy ppf "%t ↦ %t"
    (Type.TyCoercionParam.print p)
    (Constraint.print_ty_coercion t)

let print_type_param_to_type p t ppf =
  printy ppf "%t ↦ %t" (CoreTypes.TyParam.print p) (Type.print_ty t)

let print_dirt_var_sub p t ppf =
  printy ppf "%t ↦ %t" (Type.DirtParam.print p) (Type.print_dirt t)

let print_dirt_var_coercion p t ppf =
  printy ppf "%t ↦ %t"
    (Type.DirtCoercionParam.print p)
    (Constraint.print_dirt_coercion t)

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
