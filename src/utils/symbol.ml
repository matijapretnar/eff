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
  val fresh : ?special:bool -> annot -> t
  val refresh : t -> t
  val print : ?safe:bool -> t -> Format.formatter -> unit
  val is_special : t -> bool
end

module Make (Annot : Annotation) : S with type annot = Annot.t =
struct
  type annot = Annot.t
  type t = int * annot * bool

  let compare (n1, _, _) (n2, _, _) = Pervasives.compare n1 n2

  let count = ref 0

  let fresh ?(special=false) ann =
    incr count;
    (!count, ann, special)

  let refresh (_, ann, special) =
    incr count;
    (!count, ann, special)

  let print ?(safe=false) (n, ann, special) ppf =
    Format.fprintf ppf "%t%s" (Annot.print safe ann n) (if special then "" else "")

  let is_special (_, _, special) = special
end
