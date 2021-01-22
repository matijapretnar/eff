open Utils
module CoreTypes = Language.CoreTypes

let add_to_constraints con constraints = con :: constraints

let add_list_to_constraints new_constraints old_constraints =
  new_constraints @ old_constraints

type ty_coercion =
  | ReflTy of Type.target_ty
  | ArrowCoercion of ty_coercion * dirty_coercion
  | HandlerCoercion of dirty_coercion * dirty_coercion
  | TyCoercionVar of Type.TyCoercionParam.t
  | SequenceTyCoer of ty_coercion * ty_coercion
  | ApplyCoercion of CoreTypes.TyName.t * ty_coercion list
  | TupleCoercion of ty_coercion list
  | LeftArrow of ty_coercion
  | PureCoercion of dirty_coercion
  | QualTyCoer of Type.ct_ty * ty_coercion
  | QualDirtCoer of Type.ct_dirt * ty_coercion
  | ApplyQualTyCoer of ty_coercion * ty_coercion
  | ApplyQualDirtCoer of ty_coercion * dirt_coercion

and dirt_coercion =
  | ReflDirt of Type.dirt
  | DirtCoercionVar of Type.DirtCoercionParam.t
  | Empty of Type.dirt
  | UnionDirt of (Type.effect_set * dirt_coercion)
  | SequenceDirtCoer of dirt_coercion * dirt_coercion
  | DirtCoercion of dirty_coercion

and dirty_coercion =
  | BangCoercion of ty_coercion * dirt_coercion
  | RightArrow of ty_coercion
  | RightHandler of ty_coercion
  | LeftHandler of ty_coercion
  | SequenceDirtyCoer of (dirty_coercion * dirty_coercion)

type omega_ct =
  | TyOmega of (Type.TyCoercionParam.t * Type.ct_ty)
  | DirtOmega of (Type.DirtCoercionParam.t * Type.ct_dirt)
  | SkelEq of Type.skeleton * Type.skeleton
  | TyParamHasSkel of (CoreTypes.TyParam.t * Type.skeleton)

(* ************************************************************************* *)
(*                         COERCION VARIABLES OF                             *)
(* ************************************************************************* *)

module TyCoercionParamSet = Set.Make (Type.TyCoercionParam)
module DirtCoercionParamSet = Set.Make (Type.DirtCoercionParam)

let rec print_ty_coercion ?max_level c ppf =
  let print ?at_level = Print.print ?max_level ?at_level ppf in
  match c with
  | ReflTy p -> print "<%t>" (Type.print_target_ty p)
  | ArrowCoercion (tc, dc) ->
      print "%t -> %t" (print_ty_coercion tc) (print_dirty_coercion dc)
  | HandlerCoercion (dc1, dc2) ->
      print "%t ==> %t" (print_dirty_coercion dc1) (print_dirty_coercion dc2)
  | TyCoercionVar tcp -> print "%t " (Type.TyCoercionParam.print tcp)
  | SequenceTyCoer (tc1, tc2) ->
      print "%t ; %t" (print_ty_coercion tc1) (print_ty_coercion tc2)
  | PureCoercion dtyco -> print "pure(%t)" (print_dirty_coercion dtyco)
  | ApplyCoercion (t, []) -> print "%t" (CoreTypes.TyName.print t)
  | ApplyCoercion (t, [ c ]) ->
      print ~at_level:1 "%t %t"
        (print_ty_coercion ~max_level:1 c)
        (CoreTypes.TyName.print t)
  | ApplyCoercion (t, cs) ->
      print ~at_level:1 "(%t) %t"
        (Print.sequence ", " print_ty_coercion cs)
        (CoreTypes.TyName.print t)
  | TupleCoercion [] -> print "unit"
  | TupleCoercion cos ->
      print ~at_level:2 "@[<hov>%t@]"
        (Print.sequence (Symbols.times ()) (print_ty_coercion ~max_level:1) cos)
  | LeftArrow co -> print "fst(%t)" (print_ty_coercion co)
  | _ -> failwith "Not yet implemented __LOC__"

(* THE FOLLOWING ARE UNEXPECTED. SOMETHING MUST BE WRONG TO GET THEM.
   ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
  | ForallTy of CoreTypes.TyParam.t * ty_coercion
  | ApplyTyCoer of ty_coercion * target_ty

  | ForallDirt of Type.DirtParam.t * ty_coercion
  | ApplyDirCoer of ty_coercion * dirt

  | QualTyCoer of ct_ty * ty_coercion
  | ApplyQualTyCoer of ty_coercion * ty_coercion

  | QualDirtCoer of ct_dirt * ty_coercion
  | ApplyQualDirtCoer of ty_coercion * dirt_coercion

  | ForallSkel of Type.SkelParam.t * ty_coercion
  | ApplySkelCoer of ty_coercion * skeleton
*)
and print_dirty_coercion ?max_level c ppf =
  let print ?at_level = Print.print ?max_level ?at_level ppf in
  match c with
  | BangCoercion (tc, dirtc) ->
      print "%t ! %t" (print_ty_coercion tc) (print_dirt_coercion dirtc)
  | LeftHandler tyco -> print "fst(%t)" (print_ty_coercion tyco)
  | RightHandler tyco -> print "snd(%t)" (print_ty_coercion tyco)
  | RightArrow tyco -> print "snd(%t)" (print_ty_coercion tyco)
  | SequenceDirtyCoer (c1, c2) ->
      print "(%t;%t)" (print_dirty_coercion c1) (print_dirty_coercion c2)

and print_dirt_coercion ?max_level c ppf =
  let print ?at_level = Print.print ?max_level ?at_level ppf in
  match c with
  | ReflDirt p -> print "<%t>" (Type.print_target_dirt p)
  | DirtCoercionVar tcp -> print "%t" (Type.DirtCoercionParam.print tcp)
  | Empty d -> print "Empty__(%t)" (Type.print_target_dirt d)
  | UnionDirt (eset, dc) ->
      print "{%t} U %t" (Type.print_effect_set eset) (print_dirt_coercion dc)
  | DirtCoercion dtyco -> print "dirtOf(%t)" (print_dirty_coercion dtyco)
  | SequenceDirtCoer (dco1, dco2) ->
      print "(%t;%t)" (print_dirt_coercion dco1) (print_dirt_coercion dco2)

and print_omega_ct ?max_level c ppf =
  let print ?at_level = Print.print ?max_level ?at_level ppf in
  match c with
  | TyOmega (p, (ty1, ty2)) ->
      print "%t: (%t =< %t)"
        (Type.TyCoercionParam.print p)
        (Type.print_target_ty ty1) (Type.print_target_ty ty2)
  | DirtOmega (p, (ty1, ty2)) ->
      print "%t: (%t =< %t)"
        (Type.DirtCoercionParam.print p)
        (Type.print_target_dirt ty1)
        (Type.print_target_dirt ty2)
  | SkelEq (sk1, sk2) ->
      print "%t ~ %t" (Type.print_skeleton sk1) (Type.print_skeleton sk2)
  | TyParamHasSkel (tp, sk1) ->
      print "%t : %t" (CoreTypes.TyParam.print tp) (Type.print_skeleton sk1)

let fresh_dirt_coer cons =
  let param = Type.DirtCoercionParam.fresh () in
  (DirtCoercionVar param, DirtOmega (param, cons))

let fresh_ty_with_skel skel =
  let ty_var = CoreTypes.TyParam.fresh () in
  (Type.TyParam (ty_var, skel), TyParamHasSkel (ty_var, skel))

let fresh_dirty_with_skel skel =
  let ty, cons = fresh_ty_with_skel skel and drt = Type.fresh_dirt () in
  ((ty, drt), cons)

let fresh_ty_with_fresh_skel () =
  let skel_var = Type.SkelParam.fresh () in
  fresh_ty_with_skel (Type.SkelParam skel_var)

let fresh_dirty_with_fresh_skel () =
  let skel_var = Type.SkelParam.fresh () in
  fresh_dirty_with_skel (Type.SkelParam skel_var)

let fresh_ty_coer cons =
  let param = Type.TyCoercionParam.fresh () in
  (TyCoercionVar param, TyOmega (param, cons))

let fresh_dirty_coer ((ty1, drt1), (ty2, drt2)) =
  let ty_param = Type.TyCoercionParam.fresh () in
  let dirt_param = Type.DirtCoercionParam.fresh () in
  let coer =
    BangCoercion (TyCoercionVar ty_param, DirtCoercionVar dirt_param)
  in
  (coer, TyOmega (ty_param, (ty1, ty2)), DirtOmega (dirt_param, (drt1, drt2)))

(* ************************************************************************* *)
(*                        FREE PARAMETER COMPUTATION                         *)
(* ************************************************************************* *)

let free_params_constraint = function
  | TyOmega (_, ct) -> Type.free_params_ct_ty ct
  | DirtOmega (_, ct) -> Type.free_params_ct_dirt ct
  | SkelEq (sk1, sk2) ->
      Type.FreeParams.union
        (Type.free_params_skeleton sk1)
        (Type.free_params_skeleton sk2)
  | TyParamHasSkel (_t, sk) -> Type.free_params_skeleton sk

(* ************************************************************************* *)

(* free variables in target terms *)

let rec free_params_ty_coercion = function
  | ReflTy ty -> Type.free_params_ty ty
  | ArrowCoercion (tc, dc) ->
      Type.FreeParams.union
        (free_params_ty_coercion tc)
        (free_params_dirty_coercion dc)
  | HandlerCoercion (dc1, dc2) ->
      Type.FreeParams.union
        (free_params_dirty_coercion dc1)
        (free_params_dirty_coercion dc2)
  | TyCoercionVar _tcp -> Type.FreeParams.empty
  | SequenceTyCoer (tc1, tc2) ->
      Type.FreeParams.union
        (free_params_ty_coercion tc1)
        (free_params_ty_coercion tc2)
  | TupleCoercion tcs ->
      List.fold_left
        (fun free tc -> Type.FreeParams.union free (free_params_ty_coercion tc))
        Type.FreeParams.empty tcs
  | LeftArrow tc -> free_params_ty_coercion tc
  | PureCoercion dc -> free_params_dirty_coercion dc
  | QualTyCoer (_ctty, tc) -> free_params_ty_coercion tc
  | QualDirtCoer (_ctd, tc) -> free_params_ty_coercion tc
  | ApplyQualTyCoer (tc1, tc2) ->
      Type.FreeParams.union
        (free_params_ty_coercion tc1)
        (free_params_ty_coercion tc2)
  | ApplyQualDirtCoer (tc, dc) ->
      Type.FreeParams.union
        (free_params_ty_coercion tc)
        (free_params_dirt_coercion dc)
  | ApplyCoercion (_ty_name, tcs) ->
      List.fold_left
        (fun free tc -> Type.FreeParams.union free (free_params_ty_coercion tc))
        Type.FreeParams.empty tcs

and free_params_dirt_coercion = function
  | ReflDirt d -> Type.free_params_dirt d
  | DirtCoercionVar _dcv -> Type.FreeParams.empty
  | Empty d -> Type.free_params_dirt d
  | UnionDirt (_, dc) -> free_params_dirt_coercion dc
  | SequenceDirtCoer (dc1, dc2) ->
      Type.FreeParams.union
        (free_params_dirt_coercion dc1)
        (free_params_dirt_coercion dc2)
  | DirtCoercion dc -> free_params_dirty_coercion dc

and free_params_dirty_coercion = function
  | BangCoercion (tc, dc) ->
      Type.FreeParams.union
        (free_params_ty_coercion tc)
        (free_params_dirt_coercion dc)
  | RightArrow tc -> free_params_ty_coercion tc
  | RightHandler tc -> free_params_ty_coercion tc
  | LeftHandler tc -> free_params_ty_coercion tc
  | SequenceDirtyCoer (dc1, dc2) ->
      Type.FreeParams.union
        (free_params_dirty_coercion dc1)
        (free_params_dirty_coercion dc2)

let rec get_skel_vars_from_constraints = function
  | [] -> []
  | TyParamHasSkel (_, Type.SkelParam sv) :: xs ->
      sv :: get_skel_vars_from_constraints xs
  | _ :: xs -> get_skel_vars_from_constraints xs

(* Get all constraints of the form (alpha : skelvar) from a bag of constraints *)
(* (CoreTypes.TyParam.t, Type.SkelParam.t) *)
let rec getSkelVarAnnotationsFromCs = function
  | [] -> []
  | TyParamHasSkel (alpha, Type.SkelParam sv) :: cs ->
      (alpha, sv) :: getSkelVarAnnotationsFromCs cs
  | _ :: cs -> getSkelVarAnnotationsFromCs cs

(* Get all constraints of the form (alpha : skeleton) from a bag of constraints *)
(* (CoreTypes.TyParam.t, skeleton) *)
let rec getSkelAnnotationsFromCs = function
  | [] -> []
  | TyParamHasSkel (alpha, skeleton) :: cs ->
      (alpha, skeleton) :: getSkelAnnotationsFromCs cs
  | _ :: cs -> getSkelAnnotationsFromCs cs
