(** Substitution implementation *)

open Utils
module CoreTypes = Language.CoreTypes

type t = {
  type_param_to_type_coercions :
    (Type.TyCoercionParam.t, Constraint.ty_coercion) Assoc.t;
  type_param_to_type_subs : (CoreTypes.TyParam.t, Type.target_ty) Assoc.t;
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

let add_type_substitution parameter target_type sub =
  {
    sub with
    type_param_to_type_subs =
      Assoc.update parameter target_type sub.type_param_to_type_subs;
  }

let add_type_substitution_e parameter target_type =
  add_to_empty add_type_substitution parameter target_type

let add_dirt_var_coercion dirt_var target_dc sub =
  {
    sub with
    dirt_var_to_dirt_coercions =
      Assoc.update dirt_var target_dc sub.dirt_var_to_dirt_coercions;
  }

let add_dirt_var_coercion_e dirt_var target_dc =
  add_to_empty add_dirt_var_coercion dirt_var target_dc

let add_dirt_substitution dirt_var t_coercion sub =
  {
    sub with
    dirt_var_to_dirt_subs =
      Assoc.update dirt_var t_coercion sub.dirt_var_to_dirt_subs;
  }

let add_dirt_substitution_e dirt_var t_coercion =
  add_to_empty add_dirt_substitution dirt_var t_coercion

let add_skel_param_substitution param target_skel sub =
  {
    sub with
    skel_param_to_skel_subs =
      Assoc.update param target_skel sub.skel_param_to_skel_subs;
  }

let add_skel_param_substitution_e param target_skel =
  add_to_empty add_skel_param_substitution param target_skel

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
  | TyParam typ1 -> (
      match Assoc.lookup typ1 sub.type_param_to_type_subs with
      | Some ttype ->
          apply_sub_ty sub ttype
          (* We don't assume that substitutions are fully expanded *)
      | None -> TyParam typ1)
  | Arrow (tty1, tty2) ->
      Arrow (apply_sub_ty sub tty1, apply_sub_dirty_ty sub tty2)
  | Apply (ty_name, tys) -> Apply (ty_name, List.map (apply_sub_ty sub) tys)
  | Tuple ttyl -> Tuple (List.map (fun x -> apply_sub_ty sub x) ttyl)
  | Handler (tydrty1, tydrty2) ->
      Handler (apply_sub_dirty_ty sub tydrty1, apply_sub_dirty_ty sub tydrty2)
  | TyBasic p -> TyBasic p
  | QualTy (ct_ty1, tty1) ->
      QualTy (apply_sub_ct_ty sub ct_ty1, apply_sub_ty sub tty1)
  | QualDirt (ct_drt1, tty1) ->
      QualDirt (apply_sub_ct_dirt sub ct_drt1, apply_sub_ty sub tty1)

and apply_sub_dirty_ty sub (ty, drt) =
  (apply_sub_ty sub ty, apply_sub_dirt sub drt)

and apply_sub_ct_ty sub (ty1, ty2) = (apply_sub_ty sub ty1, apply_sub_ty sub ty2)

and apply_sub_ct_dirt sub (drt1, drt2) =
  (apply_sub_dirt sub drt1, apply_sub_dirt sub drt2)

let rec apply_sub_tycoer sub ty_coer =
  match ty_coer with
  | Constraint.ReflTy tty -> Constraint.ReflTy (apply_sub_ty sub tty)
  | ArrowCoercion (tycoer1, dirtycoer) ->
      ArrowCoercion
        (apply_sub_tycoer sub tycoer1, apply_sub_dirtycoer sub dirtycoer)
  | HandlerCoercion (dirtycoer1, dirtycoer2) ->
      HandlerCoercion
        (apply_sub_dirtycoer sub dirtycoer1, apply_sub_dirtycoer sub dirtycoer2)
  | TyCoercionVar p -> (
      match Assoc.lookup p sub.type_param_to_type_coercions with
      | Some t_coer -> apply_sub_tycoer sub t_coer
      | None -> TyCoercionVar p)
  | SequenceTyCoer (ty_coer1, ty_coer2) ->
      SequenceTyCoer
        (apply_sub_tycoer sub ty_coer1, apply_sub_tycoer sub ty_coer2)
  | TupleCoercion tcl ->
      TupleCoercion (List.map (fun x -> apply_sub_tycoer sub x) tcl)
  | ApplyCoercion (ty_name, tcl) ->
      ApplyCoercion (ty_name, List.map (fun x -> apply_sub_tycoer sub x) tcl)
  | LeftArrow tc1 -> LeftArrow (apply_sub_tycoer sub tc1)
  | PureCoercion dirty_coer1 ->
      PureCoercion (apply_sub_dirtycoer sub dirty_coer1)
  | _ -> failwith __LOC__

and apply_sub_dirtcoer sub dirt_coer =
  match dirt_coer with
  | Constraint.ReflDirt d -> Constraint.ReflDirt (apply_sub_dirt sub d)
  | DirtCoercionVar p -> (
      match Assoc.lookup p sub.dirt_var_to_dirt_coercions with
      | Some dc -> apply_sub_dirtcoer sub dc
      | _ -> dirt_coer)
  | Empty d -> Empty (apply_sub_dirt sub d)
  | UnionDirt (es, dirt_coer1) ->
      UnionDirt (es, apply_sub_dirtcoer sub dirt_coer1)
  | SequenceDirtCoer (dirt_coer1, dirt_coer2) ->
      SequenceDirtCoer
        (apply_sub_dirtcoer sub dirt_coer1, apply_sub_dirtcoer sub dirt_coer2)
  | DirtCoercion dirty_coer1 ->
      DirtCoercion (apply_sub_dirtycoer sub dirty_coer1)

and apply_sub_dirtycoer (sub : t) (dirty_coer : Constraint.dirty_coercion) :
    Constraint.dirty_coercion =
  match dirty_coer with
  | BangCoercion (ty_coer, dirt_coer) ->
      BangCoercion
        (apply_sub_tycoer sub ty_coer, apply_sub_dirtcoer sub dirt_coer)
  | RightArrow ty_coer1 -> RightArrow (apply_sub_tycoer sub ty_coer1)
  | RightHandler ty_coer1 -> RightHandler (apply_sub_tycoer sub ty_coer1)
  | LeftHandler ty_coer1 -> LeftHandler (apply_sub_tycoer sub ty_coer1)
  | SequenceDirtyCoer (dirty_coer1, dirty_coer2) ->
      SequenceDirtyCoer
        ( apply_sub_dirtycoer sub dirty_coer1,
          apply_sub_dirtycoer sub dirty_coer2 )

let rec apply_sub_comp sub computation =
  match computation with
  | Value e -> Value (apply_sub_exp sub e)
  | LetVal (e1, abs) ->
      LetVal (apply_sub_exp sub e1, apply_sub_abs_with_ty sub abs)
  | LetRec ([ letrec ], c1) ->
      LetRec ([ apply_sub_letrec_abs sub letrec ], apply_sub_comp sub c1)
  | Match (e, resTy, alist) ->
      Match
        ( apply_sub_exp sub e,
          apply_sub_dirty_ty sub resTy,
          List.map (apply_sub_abs sub) alist )
  | Apply (e1, e2) -> Apply (apply_sub_exp sub e1, apply_sub_exp sub e2)
  | Handle (e1, c1) -> Handle (apply_sub_exp sub e1, apply_sub_comp sub c1)
  | Call (effect, e1, abs) ->
      Call (effect, apply_sub_exp sub e1, apply_sub_abs_with_ty sub abs)
  | Op (ef, e1) -> Op (ef, apply_sub_exp sub e1)
  | Bind (c1, a1) -> Bind (apply_sub_comp sub c1, apply_sub_abs sub a1)
  | CastComp (c1, dc1) ->
      CastComp (apply_sub_comp sub c1, apply_sub_dirtycoer sub dc1)
  | _ -> failwith __LOC__

and apply_sub_exp sub expression =
  match expression with
  | Var v -> Var v
  | Const c -> Const c
  | Tuple elist -> Tuple (List.map (fun x -> apply_sub_exp sub x) elist)
  | Variant (lbl, e1) -> Variant (lbl, apply_sub_exp sub e1)
  | Lambda abs -> Lambda (apply_sub_abs_with_ty sub abs)
  | Effect eff -> Effect eff
  | Handler h -> Handler (apply_sub_handler sub h)
  | CastExp (e1, tc1) -> CastExp (apply_sub_exp sub e1, apply_sub_tycoer sub tc1)
  | LambdaTyCoerVar (tcp1, (ty1, ty2), e1) ->
      LambdaTyCoerVar
        ( tcp1,
          (apply_sub_ty sub ty1, apply_sub_ty sub ty2),
          apply_sub_exp sub e1 )
  | LambdaDirtCoerVar (dcp1, (d1, d2), e1) ->
      LambdaDirtCoerVar
        ( dcp1,
          (apply_sub_dirt sub d1, apply_sub_dirt sub d2),
          apply_sub_exp sub e1 )
  | ApplyTyCoercion (e1, tc1) ->
      ApplyTyCoercion (apply_sub_exp sub e1, apply_sub_tycoer sub tc1)
  | ApplyDirtCoercion (e1, dc1) ->
      ApplyDirtCoercion (apply_sub_exp sub e1, apply_sub_dirtcoer sub dc1)
  | _ -> failwith __LOC__

and apply_sub_abs sub (p, c) = (p, apply_sub_comp sub c)

and apply_sub_abs_with_ty sub (p, t, c) =
  (p, apply_sub_ty sub t, apply_sub_comp sub c)

and apply_sub_letrec_abs sub (f, arg_ty, res_ty, abs) =
  ( f,
    apply_sub_ty sub arg_ty,
    apply_sub_dirty_ty sub res_ty,
    apply_sub_abs sub abs )

and apply_sub_abs2 sub (p1, p2, c) = (p1, p2, apply_sub_comp sub c)

and apply_sub_handler sub h =
  let eff_clauses = h.effect_clauses in
  let new_value_clause = apply_sub_abs_with_ty sub h.value_clause in
  let new_eff_clauses =
    Assoc.map (fun abs2 -> apply_sub_abs2 sub abs2) eff_clauses
  in
  { effect_clauses = new_eff_clauses; value_clause = new_value_clause }

let apply_substitutions_to_computation = apply_sub_comp

let apply_substitutions_to_expression = apply_sub_exp

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
  | Constraint.TyParamHasSkel (tv, sp) ->
      Constraint.TyParamHasSkel (tv, apply_sub_skel subs sp)
  | _ -> cons

let apply_substitutions_to_constraints subs c_list =
  List.map (apply_sub1 subs) c_list

(* Other type information *)

(* Printing and other debug stuff *)

let printy ?at_level ppf = Print.print ?at_level ppf

let print_type_coercion p t ppf =
  Print.print ppf "substitution: ";
  printy ppf "%t :-coertyTotyCoer-> %t"
    (Type.TyCoercionParam.print p)
    (Constraint.print_ty_coercion t)

let print_type_param_to_type p t ppf =
  Print.print ppf "substitution: ";
  printy ppf "%t :-tyvarToTargetty-> %t"
    (CoreTypes.TyParam.print p)
    (Type.print_target_ty t)

let print_dirt_var_sub p t ppf =
  Print.print ppf "substitution: ";
  printy ppf "%t :-dirtvarToTargetdirt-> %t" (Type.DirtParam.print p)
    (Type.print_target_dirt t)

let print_dirt_var_coercion p t ppf =
  Print.print ppf "substitution: ";
  printy ppf "%t :-coertyDirtoDirtCoer-> %t"
    (Type.DirtCoercionParam.print p)
    (Constraint.print_dirt_coercion t)

let print_skel_param_sub p t ppf =
  Print.print ppf "substitution: ";
  printy ppf "%t :-skelvarToSkeleton-> %t" (Type.SkelParam.print p)
    (Type.print_skeleton t)

let print_sub_list subs =
  List.iter
    (fun (x, y) -> Print.debug "%t" (print_type_coercion x y))
    (Assoc.to_list subs.type_param_to_type_coercions);
  List.iter
    (fun (x, y) -> Print.debug "%t" (print_type_param_to_type x y))
    (Assoc.to_list subs.type_param_to_type_subs);
  List.iter
    (fun (x, y) -> Print.debug "%t" (print_dirt_var_sub x y))
    (Assoc.to_list subs.dirt_var_to_dirt_subs);
  List.iter
    (fun (x, y) -> Print.debug "%t" (print_dirt_var_coercion x y))
    (Assoc.to_list subs.dirt_var_to_dirt_coercions);
  List.iter
    (fun (x, y) -> Print.debug "%t" (print_skel_param_sub x y))
    (Assoc.to_list subs.skel_param_to_skel_subs)

let print_substitutions subs = print_sub_list subs
