module Dirt : Symbol.S with type annot = unit
module Skel : Symbol.S with type annot = unit
module ETy : Symbol.S with type annot = unit
module DirtCoercion : Symbol.S with type annot = unit
module TyCoercion : Symbol.S with type annot = unit
module DirtyCoercion : Symbol.S with type annot = unit

type ty_param
val fresh_ty_param : unit -> ty_param
val beautifying_ty_subst : unit -> (unit -> ty_param)
val print_ty_param : ty_param -> Format.formatter -> unit
val print_type_param : ty_param -> Format.formatter -> unit
val print_old_ty_param : ?poly:ty_param list -> ty_param -> Format.formatter -> unit
