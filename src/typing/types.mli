type effect_set


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

val print_target_ty : ?max_level:int -> target_ty -> Format.formatter -> unit

val print_target_dirt : dirt -> Format.formatter -> unit

val print_effect_list :  OldUtils.effect list -> Format.formatter -> unit

val print_target_dirty: target_dirty -> Format.formatter -> unit

val print_constraint :  ct -> Format.formatter -> unit

val print_ct_ty : ct_ty -> Format.formatter -> unit



val empty_effect_set : effect_set

val list_to_effect_set : OldUtils.effect list -> effect_set

val effect_set_to_list: effect_set -> (OldUtils.effect list)

val effect_set_diff: effect_set -> effect_set -> effect_set

val effect_set_union: effect_set -> effect_set -> effect_set

val effect_set_is_empty: effect_set -> bool