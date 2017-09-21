module EffectSet = Set.Make (struct
                             type t = Common.effect
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

type target_ty = 
  | Tyvar of Params.ty_param
  | Arrow of target_ty * target_dirty
  | Tuple of target_ty list
  | Handler of target_dirty * target_dirty
  | PrimTy of prim_ty
  | QualTy of ct_ty * target_ty
  | QualDirt of ct_dirt * target_ty
  | TySchemeTy of Params.ty_param * target_ty
  | TySchemeDirt of Params.dirt_param * target_ty

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
  | TySchemeTy (p,tty) -> print "ForallTy %t. %t" (Params.print_ty_param p ) (print_target_ty tty)
  | TySchemeDirt (p,tty) -> print "ForallDirt %t. %t" (Params.print_dirt_param p ) (print_target_ty tty)
  end



and print_target_dirt drt ppf = 
	let print ?at_level = Print.print  ?at_level ppf in
	 begin match drt with
   | SetVar(set,p) -> 
        let eff_list = effect_set_to_list set in
        print "{%t} U %t" (print_effect_list eff_list)  (Params.print_dirt_param p )
   | SetEmpty set -> 
        let eff_list = effect_set_to_list set in
        print "{%t} U (/)" (print_effect_list eff_list)
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