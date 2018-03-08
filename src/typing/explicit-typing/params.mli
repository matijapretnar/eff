module Ty : sig
    include Symbol.S with type annot = unit
    val print_type_param : t -> Format.formatter -> unit
    val print_old : ?poly:t list -> t -> Format.formatter -> unit
end

module Dirt : Symbol.S with type annot = unit

module Skel : Symbol.S with type annot = unit

module DirtCoercion : Symbol.S with type annot = unit

module TyCoercion : Symbol.S with type annot = unit

module DirtyCoercion : Symbol.S with type annot = unit
