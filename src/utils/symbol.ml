module type Annotation = sig
  type t

  val print : t -> int -> Format.formatter -> unit
end

module Anonymous : Annotation with type t = unit = struct
  type t = unit

  let print _ n ppf = Format.pp_print_int ppf n
end

module String : Annotation with type t = string = struct
  type t = string

  let print s _ ppf = Format.pp_print_string ppf s
end

module type S = sig
  type annot

  type t

  val compare : t -> t -> int

  val fresh : annot -> t

  val print : t -> Format.formatter -> unit
end

module Make (Annot : Annotation) : S with type annot = Annot.t = struct
  type annot = Annot.t

  type t = int * annot

  let compare (n1, _) (n2, _) = Pervasives.compare n1 n2

  let count = ref 0

  let fresh ann = incr count ; (!count, ann)

  let print (n, ann) = Annot.print ann n
end
