module type Annotation = sig
  type t

  val print : bool -> t -> int -> Format.formatter -> unit
end

module Anonymous : Annotation with type t = unit

module String : Annotation with type t = string

module Int : Annotation with type t = int

module Parameter (Param : sig
  val ascii_symbol : string

  val utf8_symbol : string
end) : Annotation with type t = unit

module type S = sig
  type annot

  type t

  val compare : t -> t -> int

  val fresh : annot -> t

  val new_fresh : unit -> annot -> t

  val refresh : t -> t

  val print : ?safe:bool -> t -> Format.formatter -> unit

  val fold : (annot -> int -> 'a) -> t -> 'a
end

module Make (Annot : Annotation) : S with type annot = Annot.t
