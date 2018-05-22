module Ty : sig
  include Symbol.S with type annot = unit

  val print_type_param : t -> Format.formatter -> unit

  val print_old : ?poly:t list -> t -> Format.formatter -> unit
end
