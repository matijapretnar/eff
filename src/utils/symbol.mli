module type Annotation = sig
  type t

  val print : t -> int -> Format.formatter -> unit
end

module Anonymous : Annotation with type t = unit

module String : Annotation with type t = string

module type S = sig
  type annot

  type t

  val compare : t -> t -> int

  val fresh : annot -> t

  val print : t -> Format.formatter -> unit
end

module Make (Annot : Annotation) : S with type annot = Annot.t
