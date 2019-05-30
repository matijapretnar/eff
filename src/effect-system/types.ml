module EffectSet = Set.Make (CoreTypes.Effect)
module TyParamSet = Set.Make (CoreTypes.TyParam)
module DirtParamSet = Set.Make (CoreTypes.DirtParam)

type effect_set = EffectSet.t

type skeleton =
  | SkelParam of CoreTypes.SkelParam.t
  | PrimSkel of Const.ty
  | SkelArrow of skeleton * skeleton
  | SkelApply of CoreTypes.TyName.t * skeleton list
  | SkelHandler of skeleton * skeleton
  | SkelTuple of skeleton list
  | SkelRecord of (CoreTypes.Field.t, skeleton) Assoc.t 
  | ForallSkel of CoreTypes.SkelParam.t * skeleton

and target_ty =
  | TyParam of CoreTypes.TyParam.t
  | Apply of CoreTypes.TyName.t * target_ty list
  | Arrow of target_ty * target_dirty
  | Tuple of target_ty list
  | Record of (CoreTypes.Field.t, target_ty) Assoc.t 
  | Handler of target_dirty * target_dirty
  | PrimTy of Const.ty
  | QualTy of ct_ty * target_ty
  | QualDirt of ct_dirt * target_ty
  | TySchemeTy of CoreTypes.TyParam.t * skeleton * target_ty
  | TySchemeDirt of CoreTypes.DirtParam.t * target_ty
  | TySchemeSkel of CoreTypes.SkelParam.t * target_ty

and target_dirty = (target_ty * dirt)

and dirt = {effect_set: effect_set; row: row}

and row = ParamRow of CoreTypes.DirtParam.t | EmptyRow

and ct_ty = (target_ty * target_ty)

and ct_dirt = (dirt * dirt)

and ct_dirty = (target_dirty * target_dirty)

let rec print_target_ty ?max_level ty ppf =
  let print ?at_level = Print.print ?max_level ?at_level ppf in
  match ty with
  | TyParam p -> CoreTypes.TyParam.print p ppf
  | Arrow (t1, (t2, drt)) ->
      print ~at_level:5 "@[%t -%t%s@ %t@]"
        (print_target_ty ~max_level:4 t1)
        (print_target_dirt drt) (Symbols.short_arrow ())
        (print_target_ty ~max_level:5 t2)
  | Apply (t, []) -> print "%t" (CoreTypes.TyName.print t)
  | Apply (t, [s]) ->
      print ~at_level:1 "%t %t" (print_target_ty ~max_level:1 s) (CoreTypes.TyName.print t)
  | Apply (t, ts) ->
      print ~at_level:1 "(%t) %t" (Print.sequence ", " print_target_ty ts) (CoreTypes.TyName.print t)
  | Tuple [] -> print "unit"
  | Tuple tys ->
      print ~at_level:2 "@[<hov>%t@]"
        (Print.sequence (Symbols.times ()) (print_target_ty ~max_level:1) tys)
  | Tuple tys ->
      print ~at_level:2 "@[<hov>%t@]"
        (Print.sequence (Symbols.times ()) (print_target_ty ~max_level:1) tys)
  | Handler ((t1, drt1), (t2, drt2)) ->
      print ~at_level:6 "%t ! %t %s@ %t ! %t"
        (print_target_ty ~max_level:4 t1)
        (print_target_dirt drt1) (Symbols.handler_arrow ())
        (print_target_ty ~max_level:4 t2)
        (print_target_dirt drt2)
  | PrimTy p -> print "%t" (Const.print_ty p)
  | QualTy (c, tty) -> print "%t => %t" (print_ct_ty c) (print_target_ty tty)
  | QualDirt (c, tty) ->
      print "%t => %t" (print_ct_dirt c) (print_target_ty tty)
  | TySchemeTy (p, sk, tty) ->
      print "ForallTy (%t:%t). %t" (CoreTypes.TyParam.print p) (print_skeleton sk)
        (print_target_ty tty)
  | TySchemeDirt (p, tty) ->
      print "ForallDirt %t. %t" (CoreTypes.DirtParam.print p) (print_target_ty tty)
  | TySchemeSkel (p, tty) ->
      print "ForallSkel %t. %t" (CoreTypes.SkelParam.print p) (print_target_ty tty)
  | Record tmap -> 
      print ~at_level:2 "{@[<hov>%t@]}"
        (Print.sequence (Symbols.semicolon ()) 
          (fun (field, typ) ->  CoreTypes.Field.print field ppf;print ": ";print_target_ty ~max_level:1 typ) 
          (Assoc.to_list tmap)
          )

and print_skeleton ?max_level sk ppf =
  let print ?at_level = Print.print ?max_level ?at_level ppf in
  match sk with
  | SkelParam p -> CoreTypes.SkelParam.print p ppf
  | PrimSkel s -> print "prim_skel %t" (Const.print_ty s)
  | SkelArrow (sk1, sk2) ->
      print "%t -sk-> %t" (print_skeleton sk1) (print_skeleton sk2)
  | SkelApply (t, []) -> print "%t" (CoreTypes.TyName.print t)
  | SkelApply (t, [s]) ->
      print ~at_level:1 "%t %t" (print_skeleton ~max_level:1 s) (CoreTypes.TyName.print t)
  | SkelApply (t, ts) ->
      print ~at_level:1 "(%t) %t" (Print.sequence ", " print_skeleton ts) (CoreTypes.TyName.print t)
  | SkelTuple [] -> print "unit"
  | SkelTuple sks ->
      print ~at_level:2 "@[<hov>%t@]"
        (Print.sequence (Symbols.times ()) (print_skeleton ~max_level:1) sks)
  | SkelRecord sks ->
      print ~at_level:2 "{@[<hov>%t@]}"
        (Print.sequence (Symbols.semicolon ()) 
          (fun (field, typ) ->  CoreTypes.Field.print field ppf;print ": ";print_skeleton ~max_level:1 typ) 
          (Assoc.to_list sks)
          )
  | SkelHandler (sk1, sk2) ->
      print "%t =sk=> %t" (print_skeleton sk1) (print_skeleton sk2)
  | ForallSkel (p, sk1) ->
      print "ForallSkelSkel %t. %t" (CoreTypes.SkelParam.print p) (print_skeleton sk1)


and print_target_dirt drt ppf =
  let print ?at_level = Print.print ?at_level ppf in
  match (drt.effect_set, drt.row) with
  | effect_set, EmptyRow -> print "{%t}" (print_effect_set effect_set)
  | effect_set, ParamRow p when EffectSet.is_empty effect_set ->
      print "%t" (CoreTypes.DirtParam.print p)
  | effect_set, ParamRow p ->
      print "{%t} U %t" (print_effect_set effect_set) (CoreTypes.DirtParam.print p)


and print_effect_set effect_set =
  Print.sequence "," CoreTypes.Effect.print (EffectSet.elements effect_set)


and print_target_dirty (t1, drt1) ppf =
  let print ?at_level = Print.print ?at_level ppf in
  print "%t ! %t" (print_target_ty t1) (print_target_dirt drt1)


and print_ct_ty (ty1, ty2) ppf =
  let print ?at_level = Print.print ?at_level ppf in
  print "%t <= %t" (print_target_ty ty1) (print_target_ty ty2)


and print_ct_dirt (ty1, ty2) ppf =
  let print ?at_level = Print.print ?at_level ppf in
  print "%t <= %t" (print_target_dirt ty1) (print_target_dirt ty2)

let type_const c = PrimTy (Const.infer_ty c)

  let rec types_are_equal ty1 ty2 =
  match (ty1, ty2) with
  | TyParam tv1, TyParam tv2 -> tv1 = tv2
  | Arrow (ttya1, dirtya1), Arrow (ttyb1, dirtyb1) ->
      types_are_equal ttya1 ttyb1 && dirty_types_are_equal dirtya1 dirtyb1
  | Tuple tys1, Tuple tys2 -> List.for_all2 types_are_equal tys1 tys2
  | Apply (ty_name1, tys1), Apply (ty_name2, tys2) ->
      ty_name1 = ty_name2 && List.for_all2 types_are_equal tys1 tys2
  | Handler (dirtya1, dirtya2), Handler (dirtyb1, dirtyb2) ->
      dirty_types_are_equal dirtya1 dirtyb1
      && dirty_types_are_equal dirtya2 dirtyb2
  | PrimTy ptya, PrimTy ptyb -> ptya = ptyb
  | QualTy (ctty1, ty1), QualTy (ctty2, ty2) -> failwith __LOC__
  | QualDirt (ctd1, ty1), QualDirt (ctd2, ty2) ->
      ctd1 = ctd2 && types_are_equal ty1 ty2
  | TySchemeTy (tyvar1, sk1, ty1), TySchemeTy (tyvar2, sk2, ty2) ->
      failwith __LOC__
  | TySchemeDirt (dvar1, ty1), TySchemeDirt (dvar2, ty2) ->
      dvar1 = dvar2 && types_are_equal ty1 ty2
  | TySchemeSkel (skvar1, ty1), TySchemeSkel (skvar2, ty2) -> failwith __LOC__
  | Record r1, Record r2 -> 
    Assoc.equals r1 r2
  | _ -> false

(*       Error.typing ~loc:Location.unknown "%t <> %t" (print_target_ty ty1)
        (print_target_ty ty2)
 *)
and dirty_types_are_equal (ty1, d1) (ty2, d2) =
  types_are_equal ty1 ty2 && dirts_are_equal d1 d2


and dirts_are_equal d1 d2 =
  EffectSet.equal d1.effect_set d2.effect_set && d1.row = d2.row


let no_effect_dirt dirt_param =
  {effect_set= EffectSet.empty; row= ParamRow dirt_param}


let fresh_dirt () = no_effect_dirt (CoreTypes.DirtParam.fresh ())

let closed_dirt effect_set = {effect_set; row= EmptyRow}

let empty_dirt = closed_dirt EffectSet.empty

let make_dirty ty = (ty, fresh_dirt ())

let add_effects effect_set drt =
  {drt with effect_set= EffectSet.union drt.effect_set effect_set}


let remove_effects effect_set drt =
  {drt with effect_set= EffectSet.diff drt.effect_set effect_set}


let rec free_skeleton sk =
  match sk with
  | SkelParam p -> [p]
  | PrimSkel _ -> []
  | SkelApply (_, sks) -> List.concat (List.map free_skeleton sks)
  | SkelArrow (sk1, sk2) -> free_skeleton sk1 @ free_skeleton sk2
  | SkelHandler (sk1, sk2) -> free_skeleton sk1 @ free_skeleton sk2
  | SkelTuple sks -> List.concat (List.map free_skeleton sks)
  | SkelRecord sks -> 
      List.concat (Assoc.values_of (Assoc.map free_skeleton sks))
  | ForallSkel (p, sk1) ->
      let free_a = free_skeleton sk1 in
      List.filter (fun x -> not (List.mem x [p])) free_a


let rec free_target_ty t =
  match t with
  | TyParam x -> [x]
  | Arrow (a, c) -> free_target_ty a @ free_target_dirty c
  | Tuple tup -> List.flatten (List.map free_target_ty tup)
  | Record rc -> List.flatten (Assoc.values_of (Assoc.map free_target_ty rc))
  | Handler (c1, c2) -> free_target_dirty c1 @ free_target_dirty c2
  | PrimTy _ -> []
  | QualTy (_, a) -> failwith __LOC__
  | QualDirt (_, a) -> failwith __LOC__
  | TySchemeTy (ty_param, _, a) ->
      let free_a = free_target_ty a in
      List.filter (fun x -> not (List.mem x [ty_param])) free_a
  | TySchemeDirt (dirt_param, a) -> free_target_ty a


and free_target_dirty (a, d) = free_target_ty a

let rec refresh_target_ty (ty_sbst, dirt_sbst) t =
  match t with
  | TyParam x -> (
    match Assoc.lookup x ty_sbst with
    | Some x' -> ((ty_sbst, dirt_sbst), TyParam x')
    | None ->
        let y = CoreTypes.TyParam.fresh () in
        ((Assoc.update x y ty_sbst, dirt_sbst), TyParam y) )
  | Arrow (a, c) ->
      let (a_ty_sbst, a_dirt_sbst), a' =
        refresh_target_ty (ty_sbst, dirt_sbst) a
      in
      let temp_ty_sbst = Assoc.concat a_ty_sbst ty_sbst in
      let temp_dirt_sbst = Assoc.concat a_dirt_sbst dirt_sbst in
      let (c_ty_sbst, c_dirt_sbst), c' =
        refresh_target_dirty (temp_ty_sbst, temp_dirt_sbst) c
      in
      ((c_ty_sbst, c_dirt_sbst), Arrow (a', c'))
  | Tuple tup -> ((ty_sbst, dirt_sbst), t)
  | Handler (c1, c2) ->
      let (c1_ty_sbst, c1_dirt_sbst), c1' =
        refresh_target_dirty (ty_sbst, dirt_sbst) c1
      in
      let temp_ty_sbst = Assoc.concat c1_ty_sbst ty_sbst in
      let temp_dirt_sbst = Assoc.concat c1_dirt_sbst dirt_sbst in
      let (c2_ty_sbst, c2_dirt_sbst), c2' =
        refresh_target_dirty (temp_ty_sbst, temp_dirt_sbst) c2
      in
      ((c2_ty_sbst, c2_dirt_sbst), Handler (c1', c2'))
  | PrimTy x -> ((ty_sbst, dirt_sbst), PrimTy x)
  | QualTy (_, a) -> failwith __LOC__
  | QualDirt (_, a) -> failwith __LOC__
  | TySchemeTy (ty_param, _, a) -> failwith __LOC__
  | TySchemeDirt (dirt_param, a) -> failwith __LOC__


and refresh_target_dirty (ty_sbst, dirt_sbst) (t, d) =
  let (t_ty_sbst, t_dirt_sbst), t' =
    refresh_target_ty (ty_sbst, dirt_sbst) t
  in
  let temp_ty_sbst = Assoc.concat t_ty_sbst ty_sbst in
  let temp_dirt_sbst = Assoc.concat t_dirt_sbst dirt_sbst in
  let (d_ty_sbst, d_dirt_sbst), d' =
    refresh_target_dirt (temp_ty_sbst, temp_dirt_sbst) d
  in
  ((d_ty_sbst, d_dirt_sbst), (t', d'))


and refresh_target_dirt (ty_sbst, dirt_sbst) drt =
  match drt.row with
  | ParamRow x -> (
    match Assoc.lookup x dirt_sbst with
    | Some x' -> ((ty_sbst, dirt_sbst), {drt with row= ParamRow x'})
    | None ->
        let y = CoreTypes.DirtParam.fresh () in
        ((ty_sbst, Assoc.update x y dirt_sbst), {drt with row= ParamRow y})
    )
  | EmptyRow -> ((ty_sbst, dirt_sbst), drt)


let rec source_to_target ty =
  let loc = Location.unknown in
  match ty with
  | Type.Apply (ty_name, args) when Tctx.transparent ~loc ty_name -> (
    match Tctx.lookup_tydef ~loc ty_name with
    | [], Tctx.Inline ty -> source_to_target ty
    | _, Tctx.Sum _ | _, Tctx.Record _ ->
        assert false (* None of these are transparent *) )
  | Type.Apply (ty_name, args) ->
      Apply (ty_name, List.map source_to_target args)
  | Type.TyParam p -> TyParam p
  | Type.Basic b -> PrimTy b
  | Type.Tuple l -> Tuple (List.map source_to_target l)
  | Type.Arrow (ty, dirty) ->
      Arrow (source_to_target ty, source_to_target_dirty dirty)
  | Type.Handler {value= dirty1; finally= dirty2} ->
      Handler (source_to_target_dirty dirty1, source_to_target_dirty dirty2)


and source_to_target_dirty ty = (source_to_target ty, empty_dirt)

let constructor_signature lbl =
  match Tctx.infer_variant lbl with
  | None -> assert false
  | Some (ty_out, ty_in) ->
      let ty_in =
        match ty_in with Some ty_in -> ty_in | None -> Type.Tuple []
      in
      (source_to_target ty_in, source_to_target ty_out)


let rec free_ty_vars_ty = function
  | TyParam x -> TyParamSet.singleton x
  | Arrow (a, c) -> TyParamSet.union (free_ty_vars_ty a) (free_ty_var_dirty c)
  | Tuple tup ->
      List.fold_left
        (fun free ty -> TyParamSet.union free (free_ty_vars_ty ty))
        TyParamSet.empty tup
  | Record tmap -> 
      Assoc.fold_left 
      (fun free (_,ty) -> TyParamSet.union free (free_ty_vars_ty ty))
      TyParamSet.empty tmap
  | Apply (_, tup) ->
      List.fold_left
        (fun free ty -> TyParamSet.union free (free_ty_vars_ty ty))
        TyParamSet.empty tup
  | Handler (c1, c2) ->
      TyParamSet.union (free_ty_var_dirty c1) (free_ty_var_dirty c2)
  | PrimTy _ -> TyParamSet.empty
  | QualTy (_, a) -> free_ty_vars_ty a
  | QualDirt (_, a) -> free_ty_vars_ty a
  | TySchemeTy (ty_param, _, a) ->
      let free_a = free_ty_vars_ty a in
      TyParamSet.remove ty_param free_a
  | TySchemeDirt (dirt_param, a) -> free_ty_vars_ty a


and free_ty_var_dirty (a, _) = free_ty_vars_ty a

let constraint_free_row_vars = function
  | ParamRow p -> DirtParamSet.singleton p
  | EmptyRow -> DirtParamSet.empty


let rec free_dirt_vars_ty = function
  | Arrow (a, c) ->
      DirtParamSet.union (free_dirt_vars_ty a) (free_dirt_vars_dirty c)
  | Tuple tup ->
      List.fold_left
        (fun free ty -> DirtParamSet.union free (free_dirt_vars_ty ty))
        DirtParamSet.empty tup
  | Apply (_, tup) ->
      List.fold_left
        (fun free ty -> DirtParamSet.union free (free_dirt_vars_ty ty))
        DirtParamSet.empty tup
  | Handler (c1, c2) ->
      DirtParamSet.union (free_dirt_vars_dirty c1) (free_dirt_vars_dirty c2)
  | QualTy (_, a) -> free_dirt_vars_ty a
  | QualDirt (_, a) -> free_dirt_vars_ty a
  | TySchemeTy (ty_param, _, a) -> free_dirt_vars_ty a
  | TySchemeDirt (dirt_param, a) ->
      let free_a = free_dirt_vars_ty a in
      DirtParamSet.remove dirt_param free_a
  | _ -> DirtParamSet.empty

and free_dirt_vars_dirty (a, d) = free_dirt_vars_dirt d

and free_dirt_vars_dirt drt = constraint_free_row_vars drt.row
