
type target_ty = 
  | Tyvar of Params.ty_param
  | Arrow of target_ty * target_dirty
  | Tuple of target_ty list
  | Handler of target_dirty * target_dirty
  | PrimTy of prim_ty
  | QualTy of ct * target_ty
  | TySchemeTy of Params.ty_param * target_ty
  | TySchemeDirt of Params.dirt_param * target_ty

and
 target_dirty = ( target_ty * dirt)
and
 dirt = 
 | Empty
 | DirtVar of Params.dirt_param
 | Union of ( Common.effect * dirt)
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
  | QualTy (c,tty) -> print "%t => %t" (print_constraint c) (print_target_ty tty)
  | TySchemeTy (p,tty) -> print "ForallTy %t. %t" (Params.print_ty_param p ) (print_target_ty tty)
  | TySchemeDirt (p,tty) -> print "ForallDirt %t. %t" (Params.print_dirt_param p ) (print_target_ty tty)
  end


and print_target_dirt drt ppf = 
	let print ?at_level = Print.print  ?at_level ppf in
	 begin match drt with
	 | Empty -> print "(/)"
	 | DirtVar p -> print "%t" (Params.print_dirt_param p )
	 | Union (eff,d) -> print "%s U %t" eff (print_target_dirt d)
	  end

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
and print_prim_ty pty ppf=
	let print ?at_level = Print.print  ?at_level ppf in
	begin match pty with
	| IntTy -> print "int"
 	| BoolTy -> print "bool"
 	| StringTy -> print "string"
 	| FloatTy -> print "float"
 	end
