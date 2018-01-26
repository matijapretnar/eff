type effect_set

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


val types_are_equal: target_ty -> target_ty -> bool

val dirty_types_are_equal: target_dirty -> target_dirty -> bool

val dirts_are_equal: dirt -> dirt -> bool


val print_target_ty : ?max_level:int -> target_ty -> Format.formatter -> unit

val print_target_dirt : dirt -> Format.formatter -> unit

val print_skeleton : ?max_level:int -> skeleton -> Format.formatter -> unit

val print_effect_list :  OldUtils.effect list -> Format.formatter -> unit

val print_target_dirty: target_dirty -> Format.formatter -> unit

val print_constraint :  ct -> Format.formatter -> unit

val print_ct_ty : ct_ty -> Format.formatter -> unit



module EffectSet : Set.S with type elt = OldUtils.effect and type t = effect_set

val is_effect_member:OldUtils.effect -> dirt -> bool