module type Parameter = sig
  type t

  val compare : t -> t -> int

  val print : t -> Format.formatter -> unit
end

module type S = sig
  type elt

  type t

  val empty : t

  val is_empty : t -> bool

  val add : elt -> elt -> t -> t

  val remove : elt -> t -> elt list * elt list * t

  val merge : t -> t -> t

  val fold : (elt -> elt -> 'a -> 'a) -> t -> 'a -> 'a

  val filter : (elt -> elt -> bool) -> t -> t

  val get_prec : elt -> t -> elt list

  val get_succ : elt -> t -> elt list

  val map : (elt -> elt) -> t -> t

  val print : t -> Format.formatter -> unit
end

module Make (Elt : Parameter) : S with type elt = Elt.t
