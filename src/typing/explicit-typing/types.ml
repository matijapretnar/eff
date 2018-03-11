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

let add_effects effect_set drt =
  {drt with effect_set= EffectSet.union drt.effect_set effect_set}


let remove_effects effect_set drt =
  {drt with effect_set= EffectSet.diff drt.effect_set effect_set}


let rec free_skeleton sk =
  match sk with
  | SkelParam p -> [p]
  | PrimSkel _ -> []
  | SkelArrow (sk1, sk2) -> free_skeleton sk1 @ free_skeleton sk2
  | SkelHandler (sk1, sk2) -> free_skeleton sk1 @ free_skeleton sk2
  | ForallSkel (p, sk1) ->
      let free_a = free_skeleton sk1 in
      List.filter (fun x -> not (List.mem x [p])) free_a


let rec free_target_ty t =
  match t with
  | TyParam x -> [x]
  | Arrow (a, c) -> free_target_ty a @ free_target_dirty c
  | Tuple tup -> List.flatten (List.map free_target_ty tup)
  | Handler (c1, c2) -> free_target_dirty c1 @ free_target_dirty c2
  | PrimTy _ -> []
  | QualTy (_, a) -> assert false
  | QualDirt (_, a) -> assert false
  | TySchemeTy (ty_param, _, a) ->
      let free_a = free_target_ty a in
      List.filter (fun x -> not (List.mem x [ty_param])) free_a
  | TySchemeDirt (dirt_param, a) -> free_target_ty a


and free_target_dirty (a, d) = free_target_ty a

let rec refresh_target_ty (ty_sbst, dirt_sbst) t =
  match t with
  | TyParam x -> (
    match OldUtils.lookup x ty_sbst with
    | Some x' -> ((ty_sbst, dirt_sbst), TyParam x')
    | None ->
        let y = Params.Ty.fresh () in
        ((OldUtils.update x y ty_sbst, dirt_sbst), TyParam y) )
  | Arrow (a, c) ->
      let (a_ty_sbst, a_dirt_sbst), a' =
        refresh_target_ty (ty_sbst, dirt_sbst) a
      in
      let temp_ty_sbst = a_ty_sbst @ ty_sbst in
      let temp_dirt_sbst = a_dirt_sbst @ dirt_sbst in
      let (c_ty_sbst, c_dirt_sbst), c' =
        refresh_target_dirty (temp_ty_sbst, temp_dirt_sbst) c
      in
      ((c_ty_sbst, c_dirt_sbst), Arrow (a', c'))
  | Tuple tup -> ((ty_sbst, dirt_sbst), t)
  | Handler (c1, c2) ->
      let (c1_ty_sbst, c1_dirt_sbst), c1' =
        refresh_target_dirty (ty_sbst, dirt_sbst) c1
      in
      let temp_ty_sbst = c1_ty_sbst @ ty_sbst in
      let temp_dirt_sbst = c1_dirt_sbst @ dirt_sbst in
      let (c2_ty_sbst, c2_dirt_sbst), c2' =
        refresh_target_dirty (temp_ty_sbst, temp_dirt_sbst) c2
      in
      ((c2_ty_sbst, c2_dirt_sbst), Handler (c1', c2'))
  | PrimTy x -> ((ty_sbst, dirt_sbst), PrimTy x)
  | QualTy (_, a) -> assert false
  | QualDirt (_, a) -> assert false
  | TySchemeTy (ty_param, _, a) -> assert false
  | TySchemeDirt (dirt_param, a) -> assert false

and refresh_target_dirty (ty_sbst, dirt_sbst) (t, d) =
  let (t_ty_sbst, t_dirt_sbst), t' =
    refresh_target_ty (ty_sbst, dirt_sbst) t
  in
  let temp_ty_sbst = t_ty_sbst @ ty_sbst in
  let temp_dirt_sbst = t_dirt_sbst @ dirt_sbst in
  let (d_ty_sbst, d_dirt_sbst), d' =
    refresh_target_dirt (temp_ty_sbst, temp_dirt_sbst) d
  in
  ((d_ty_sbst, d_dirt_sbst), (t', d'))

and refresh_target_dirt (ty_sbst, dirt_sbst) drt =
  match drt.row with
  | ParamRow x -> (
    match OldUtils.lookup x dirt_sbst with
    | Some x' -> ((ty_sbst, dirt_sbst), {drt with row= ParamRow x'})
    | None ->
        let y = Params.Dirt.fresh () in
        ((ty_sbst, OldUtils.update x y dirt_sbst), {drt with row= ParamRow y})
    )
  | EmptyRow -> ((ty_sbst, dirt_sbst), drt)
