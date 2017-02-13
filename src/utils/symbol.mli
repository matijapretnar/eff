module type Annotation =
sig
  type t

  val print : bool -> t -> int -> Format.formatter -> unit
end

module Anonymous : Annotation with type t = unit

module String : Annotation with type t = string

module type S =
sig
  type annot
  type t

  val compare : t -> t -> int
  val fresh : ?special:bool -> annot -> t
  val refresh : t -> t
  val print : ?safe:bool -> t -> Format.formatter -> unit
  val is_special : t -> bool
end

module Make (Annot : Annotation) : S with type annot = Annot.t
