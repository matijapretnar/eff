module EffectSet = Set.Make (struct
  type t = OldUtils.effect

  let compare = compare
end)

type effect_set = EffectSet.t

type skeleton =
  | SkelParam of Params.Skel.t
  | PrimSkel of prim_ty
  | SkelArrow of skeleton * skeleton
  | SkelHandler of skeleton * skeleton
  | ForallSkel of Params.Skel.t * skeleton

and target_ty =
  | TyParam of Params.Ty.t
  | Arrow of target_ty * target_dirty
  | Tuple of target_ty list
  | Handler of target_dirty * target_dirty
  | PrimTy of prim_ty
  | QualTy of ct_ty * target_ty
  | QualDirt of ct_dirt * target_ty
  | TySchemeTy of Params.Ty.t * skeleton * target_ty
  | TySchemeDirt of Params.Dirt.t * target_ty
  | TySchemeSkel of Params.Skel.t * target_ty

and target_dirty = (target_ty * dirt)

and dirt = {effect_set: effect_set; row: row}

and row = ParamRow of Params.Dirt.t | EmptyRow

and ct =
  | LeqTy of (target_ty * target_ty)
  | LeqDirty of (target_dirty * target_dirty)
  | LeqDirt of (dirt * dirt)

and prim_ty = IntTy | BoolTy | StringTy | FloatTy

and ct_ty = (target_ty * target_ty)

and ct_dirt = (dirt * dirt)

and ct_dirty = (target_dirty * target_dirty)

let rec types_are_equal ty1 ty2 =
  match (ty1, ty2) with
  | TyParam tv1, TyParam tv2 -> tv1 = tv2
  | Arrow (ttya1, dirtya1), Arrow (ttyb1, dirtyb1) ->
      types_are_equal ttya1 ttyb1 && dirty_types_are_equal dirtya1 dirtyb1
  | Handler (dirtya1, dirtya2), Handler (dirtyb1, dirtyb2) ->
      dirty_types_are_equal dirtya1 dirtyb1
      && dirty_types_are_equal dirtya2 dirtyb2
  | PrimTy ptya, PrimTy ptyb -> ptya = ptyb
  | QualTy (ctty1, ty1), QualTy (ctty2, ty2) -> assert false
  | QualDirt (ctd1, ty1), QualDirt (ctd2, ty2) ->
      ctd1 = ctd2 && types_are_equal ty1 ty2
  | TySchemeTy (tyvar1, sk1, ty1), TySchemeTy (tyvar2, sk2, ty2) ->
      assert false
  | TySchemeDirt (dvar1, ty1), TySchemeDirt (dvar2, ty2) ->
      dvar1 = dvar2 && types_are_equal ty1 ty2
  | TySchemeSkel (skvar1, ty1), TySchemeSkel (skvar2, ty2) -> assert false
  | _ -> false


and dirty_types_are_equal (ty1, d1) (ty2, d2) =
  types_are_equal ty1 ty2 && dirts_are_equal d1 d2


and dirts_are_equal d1 d2 =
  EffectSet.equal d1.effect_set d2.effect_set && d1.row = d2.row


let rec print_target_ty ?max_level ty ppf =
  let print ?at_level = Print.print ?max_level ?at_level ppf in
  match ty with
  | TyParam p -> Params.Ty.print p ppf
  | Arrow (t1, (t2, drt)) ->
      print ~at_level:5 "@[%t -%t%s@ %t@]"
        (print_target_ty ~max_level:4 t1)
        (print_target_dirt drt) (Symbols.short_arrow ())
        (print_target_ty ~max_level:5 t2)
  | Tuple [] -> print "unit"
  | Tuple tys ->
      print ~at_level:2 "@[<hov>%t@]"
        (Print.sequence (Symbols.times ()) (print_target_ty ~max_level:1) tys)
  | Handler ((t1, drt1), (t2, drt2)) ->
      print ~at_level:6 "%t ! %t %s@ %t ! %t"
        (print_target_ty ~max_level:4 t1)
        (print_target_dirt drt1) (Symbols.handler_arrow ())
        (print_target_ty ~max_level:4 t2)
        (print_target_dirt drt2)
  | PrimTy p -> print_prim_ty p ppf
  | QualTy (c, tty) -> print "%t => %t" (print_ct_ty c) (print_target_ty tty)
  | QualDirt (c, tty) ->
      print "%t => %t" (print_ct_dirt c) (print_target_ty tty)
  | TySchemeTy (p, sk, tty) ->
      print "ForallTy (%t:%t). %t" (Params.Ty.print p) (print_skeleton sk)
        (print_target_ty tty)
  | TySchemeDirt (p, tty) ->
      print "ForallDirt %t. %t" (Params.Dirt.print p) (print_target_ty tty)
  | TySchemeSkel (p, tty) ->
      print "ForallSkel %t. %t" (Params.Skel.print p) (print_target_ty tty)


and print_skeleton ?max_level sk ppf =
  let print ?at_level = Print.print ?max_level ?at_level ppf in
  match sk with
  | SkelParam p -> Params.Skel.print p ppf
  | PrimSkel s -> print "prim_skel %t" (print_prim_ty s)
  | SkelArrow (sk1, sk2) ->
      print "%t -sk-> %t" (print_skeleton sk1) (print_skeleton sk2)
  | SkelHandler (sk1, sk2) ->
      print "%t =sk=> %t" (print_skeleton sk1) (print_skeleton sk2)
  | ForallSkel (p, sk1) ->
      print "ForallSkelSkel %t. %t" (Params.Skel.print p) (print_skeleton sk1)


and print_target_dirt drt ppf =
  let print ?at_level = Print.print ?at_level ppf in
  match (drt.effect_set, drt.row) with
  | effect_set, EmptyRow -> print "{%t}" (print_effect_set effect_set)
  | effect_set, ParamRow p when EffectSet.is_empty effect_set ->
      print "%t" (Params.Dirt.print p)
  | effect_set, ParamRow p ->
      print "{%t} U %t" (print_effect_set effect_set) (Params.Dirt.print p)


and print_effect_set effect_set =
  Print.sequence ","
    (fun str ppf -> Format.pp_print_string ppf str)
    (EffectSet.elements effect_set)


and print_target_dirty (t1, drt1) ppf =
  let print ?at_level = Print.print ?at_level ppf in
  print "%t ! %t" (print_target_ty t1) (print_target_dirt drt1)


and print_constraint c ppf =
  let print ?at_level = Print.print ?at_level ppf in
  match c with
  | LeqTy (ty1, ty2) ->
      print "%t <= %t" (print_target_ty ty1) (print_target_ty ty2)
  | LeqDirty ((t1, drt1), (t2, drt2)) ->
      print "%t ! %t <= %t ! %t" (print_target_ty t1) (print_target_dirt drt1)
        (print_target_ty t2) (print_target_dirt drt2)
  | LeqDirt (d1, d2) ->
      print "%t <= %t" (print_target_dirt d1) (print_target_dirt d2)


and print_ct_ty (ty1, ty2) ppf =
  let print ?at_level = Print.print ?at_level ppf in
  print "%t <= %t" (print_target_ty ty1) (print_target_ty ty2)


and print_ct_dirt (ty1, ty2) ppf =
  let print ?at_level = Print.print ?at_level ppf in
  print "%t <= %t" (print_target_dirt ty1) (print_target_dirt ty2)


and print_prim_ty pty ppf =
  let print ?at_level = Print.print ?at_level ppf in
  match pty with
  | IntTy -> print "int"
  | BoolTy -> print "bool"
  | StringTy -> print "string"
  | FloatTy -> print "float"


let no_effect_dirt dirt_param =
  {effect_set= EffectSet.empty; row= ParamRow dirt_param}


let fresh_dirt () = no_effect_dirt (Params.Dirt.fresh ())

let closed_dirt effect_set = {effect_set; row= EmptyRow}

let empty_dirt = closed_dirt EffectSet.empty

let make_dirty ty = (ty, fresh_dirt ())
