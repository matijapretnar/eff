module type Annotation =
sig
  type t

  val print : bool -> t -> int -> Format.formatter -> unit
end

module Anonymous : Annotation with type t = unit =
struct
  type t = unit

  let print _ _ n ppf = Format.pp_print_int ppf n
end

module String : Annotation with type t = string =
struct
  type t = string

  let print safe desc n ppf =
    if safe then
      match desc.[0] with
      | ('a'..'z' | '_') ->
        Format.fprintf ppf "_%s_%d" desc n
      | _ -> Format.fprintf ppf "_var_%d (* %s *)" n desc
    else
      Format.fprintf ppf "%s" desc

end

module type S =
sig
  type annot
  type t

  val compare : t -> t -> int
  val fresh : annot -> t
  val refresh : t -> t
  val print : ?safe:bool -> t -> Format.formatter -> unit
end

module Make (Annot : Annotation) : S with type annot = Annot.t =
struct
  type annot = Annot.t
  type t = int * annot

  let compare (n1, _) (n2, _) = Pervasives.compare n1 n2

  let count = ref 0

  let fresh ann =
    incr count;
    (!count, ann)

  let refresh (_, ann) =
    incr count;
    (!count, ann)

  let print ?(safe=false) (n, ann) ppf =
    Annot.print safe ann n ppf
end
