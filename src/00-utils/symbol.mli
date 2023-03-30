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

  module Set : sig
    include Set.S with type elt = t

    val print : t -> Format.formatter -> unit
  end

  module Map : sig
    include Map.S with type key = t

    val of_bindings : (key * 'a) list -> 'a t
    val compatible_union : 'a t -> 'a t -> 'a t
    val keys : 'a t -> key list
    val values : 'a t -> 'a list

    val print :
      ('a -> Format.formatter -> unit) -> 'a t -> Format.formatter -> unit
  end
end

module Make (Annot : Annotation) : S with type annot = Annot.t
