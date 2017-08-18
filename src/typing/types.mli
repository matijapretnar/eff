
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


val print_target_ty : ?max_level:int -> target_ty -> Format.formatter -> unit

val print_target_dirt : dirt -> Format.formatter -> unit

val print_constraint :  ct -> Format.formatter -> unit
