module EffectSet = Set.Make (struct
                             type t = OldUtils.effect
                             let compare = compare
                           end);;

type effect_set = EffectSet.t

let empty_effect_set =  EffectSet.empty

let list_to_effect_set l = 
      List.fold_right (EffectSet.add) l (EffectSet.empty) 

let effect_set_to_list s = 
      EffectSet.fold (fun a b -> (a:: b)) s []

let effect_set_diff s1 s2 = 
      EffectSet.diff s1 s2

let effect_set_union s1 s2 = 
      EffectSet.union s1 s2

let effect_set_is_empty s = 
      EffectSet.is_empty s

let effect_set_mem eff s = 
      EffectSet.mem eff s

let effect_set_is_subseteq s1 s2 =
      (EffectSet.subset s1 s2) || (EffectSet.equal s1 s2)


type skeleton =
  | SkelVar of Params.skel_param
  | PrimSkel of prim_ty
  | SkelArrow of skeleton * skeleton
  | SkelHandler of skeleton * skeleton
  | ForallSkel of Params.skel_param * skeleton


and target_ty = 
  | Tyvar of Params.ty_param
  | Arrow of target_ty * target_dirty
  | Tuple of target_ty list
  | Handler of target_dirty * target_dirty
  | PrimTy of prim_ty
  | QualTy of ct_ty * target_ty
  | QualDirt of ct_dirt * target_ty
  | TySchemeTy of Params.ty_param * skeleton * target_ty
  | TySchemeDirt of Params.dirt_param * target_ty
  | TySchemeSkel of Params.skel_param * target_ty

and
 target_dirty = ( target_ty * dirt)
and
 dirt = 
 | SetVar of effect_set * Params.dirt_param
 | SetEmpty of effect_set
and
 ct = 
 | LeqTy of (target_ty * target_ty)
 | LeqDirty of (target_dirty * target_dirty)
 | LeqDirt of (dirt * dirt)
and 
 prim_ty =
 | IntTy
 | BoolTy
 | StringTy
 | FloatTy
and
ct_ty = (target_ty * target_ty)
and
ct_dirt = (dirt * dirt)
and 
ct_dirty = (target_dirty * target_dirty)

let is_effect_member eff drt =
  begin match drt with
  | SetVar (eset,_) when (effect_set_mem eff eset) -> true
  | SetEmpty (eset) when (effect_set_mem eff eset) -> true
  | _ -> false
  end 

let rec types_are_equal ty1 ty2 =
  begin match (ty1,ty2) with
  | (Tyvar tv1, Tyvar tv2) -> tv1 = tv2
  | (Arrow (ttya1, dirtya1), Arrow (ttyb1, dirtyb1)) -> (types_are_equal ttya1 ttyb1) && (dirty_types_are_equal dirtya1 dirtyb1)
  | (Handler (dirtya1,dirtya2), Handler (dirtyb1,dirtyb2)) -> (dirty_types_are_equal dirtya1 dirtyb1) && (dirty_types_are_equal dirtya2 dirtyb2)
  | (PrimTy ptya, PrimTy ptyb) -> ptya = ptyb
  | _ -> false
  end

and dirty_types_are_equal (ty1,d1) (ty2,d2) = (types_are_equal ty1 ty2) && (dirts_are_equal d1 d2)

and dirts_are_equal d1 d2 =
  begin match (d1,d2) with
  | (SetVar (es1,dv1), SetVar(es2,dv2) ) -> ( EffectSet.equal es1 es2 ) && (dv1 = dv2)
  | (SetEmpty es1, SetEmpty es2) ->  ( EffectSet.equal es1 es2 )
  | _ -> false
  end

let rec print_target_ty ?max_level ty ppf =
  let print ?at_level = Print.print ?max_level ?at_level ppf in
  begin match ty with
  | Tyvar p -> Params.print_ty_param p ppf
  | Arrow (t1, (t2, drt)) ->
   	 print ~at_level:5 "@[%t -%t%s@ %t@]"
      (print_target_ty ~max_level:4 t1)
      (print_target_dirt drt)
      (Symbols.short_arrow ())
      (print_target_ty ~max_level:5 t2)
  | Tuple [] -> print "unit"
  | Tuple tys ->
  	   print ~at_level:2 "@[<hov>%t@]"
      (Print.sequence (Symbols.times ()) (print_target_ty ~max_level:1) tys)
  | Handler ((t1, drt1), (t2, drt2)) ->
    print ~at_level:6 "%t ! %t %s@ %t ! %t"
      (print_target_ty ~max_level:4 t1)
      (print_target_dirt drt1)
      (Symbols.handler_arrow ())
      (print_target_ty ~max_level:4 t2)
      (print_target_dirt drt2)
  | PrimTy p -> print_prim_ty p ppf
  | QualTy (c,tty) -> print "%t => %t" (print_ct_ty c) (print_target_ty tty)
  | QualDirt (c,tty) -> print "%t => %t" (print_ct_dirt c) (print_target_ty tty)
  | TySchemeTy (p,sk,tty) -> print "ForallTy (%t:%t). %t" (Params.print_ty_param p ) (print_skeleton sk) (print_target_ty tty)
  | TySchemeDirt (p,tty) -> print "ForallDirt %t. %t" (Params.print_dirt_param p ) (print_target_ty tty)
  | TySchemeSkel (p,tty) -> print "ForallSkel %t. %t" (Params.print_skel_param p ) (print_target_ty tty)
  end


and print_skeleton ?max_level sk ppf =
  let print ?at_level = Print.print ?max_level ?at_level ppf in
  begin match sk with
  | SkelVar p -> Params.print_skel_param p ppf
  | PrimSkel s -> print "prim_skel %t" (print_prim_ty s)
  | SkelArrow (sk1,sk2) -> print "%t -sk-> %t" (print_skeleton sk1) (print_skeleton sk2)
  | SkelHandler (sk1,sk2) -> print "%t =sk=> %t" (print_skeleton sk1) (print_skeleton sk2)
  | ForallSkel (p,sk1)-> print "ForallSkelSkel %t. %t" (Params.print_skel_param p) (print_skeleton sk1)
  end

and print_target_dirt drt ppf = 
	let print ?at_level = Print.print  ?at_level ppf in
	 begin match drt with
   | SetVar(set,p) -> 
        if effect_set_is_empty set
          then print "%t" (Params.print_dirt_param p)
          else let eff_list = effect_set_to_list set in
               print "{%t} U %t" (print_effect_list eff_list)  (Params.print_dirt_param p )
   | SetEmpty set -> 
        let eff_list = effect_set_to_list set in
        print "{%t}" (print_effect_list eff_list)
	  end

and print_effect_list eff_list ppf =
  let print ?at_level = Print.print  ?at_level ppf in
  match eff_list with 
  | [] -> ()
  | (x::[]) -> print "%s" x
  | (x::xs) -> print "%s, %t" x  (print_effect_list xs)

and print_target_dirty (t1, drt1) ppf = 
  let print ?at_level = Print.print  ?at_level ppf in
  print "%t ! %t" (print_target_ty t1) (print_target_dirt drt1)

and print_constraint c ppf=
	let print ?at_level = Print.print  ?at_level ppf in
	begin match c with
	| LeqTy (ty1,ty2) -> print "%t <= %t"  (print_target_ty ty1)  (print_target_ty ty2)
	| LeqDirty ((t1, drt1), (t2, drt2)) ->
      print "%t ! %t <= %t ! %t"
      (print_target_ty t1)
      (print_target_dirt drt1)
      (print_target_ty t2)
      (print_target_dirt drt2)
	| LeqDirt (d1,d2) -> print "%t <= %t"  (print_target_dirt d1)  (print_target_dirt d2)
	end

and print_ct_ty (ty1,ty2) ppf = 
    let print ?at_level = Print.print  ?at_level ppf in
    print "%t <= %t"  (print_target_ty ty1)  (print_target_ty ty2)

and print_ct_dirt (ty1,ty2) ppf = 
    let print ?at_level = Print.print  ?at_level ppf in
    print "%t <= %t"  (print_target_dirt ty1)  (print_target_dirt ty2)

and print_prim_ty pty ppf=
	let print ?at_level = Print.print  ?at_level ppf in
	begin match pty with
	| IntTy -> print "int"
 	| BoolTy -> print "bool"
 	| StringTy -> print "string"
 	| FloatTy -> print "float"
 	end


