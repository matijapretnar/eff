module type Annotation = sig
  type t

  val print : bool -> t -> int -> Format.formatter -> unit
end

module Anonymous : Annotation with type t = unit = struct
  type t = unit

  let print _ _ n ppf = Format.pp_print_int ppf n
end

module type PARAMETER = sig
  val ascii_symbol : string

  val utf8_symbol : string
end

module Parameter (Param : PARAMETER) : Annotation with type t = unit = struct
  type t = unit

  let print _ _ n ppf =
    let symbol =
      if !Config.ascii then Param.ascii_symbol else Param.utf8_symbol
    in
    Print.print ppf "%s%s" symbol (Symbols.subscript (Some (n + 1)))
end

module String : Annotation with type t = string = struct
  type t = string

  let print safe desc n ppf =
    if safe then
      match desc.[0] with
      | 'a' .. 'z' | '_' -> Format.fprintf ppf "%s" desc
      | '$' -> Format.fprintf ppf "_var_%d" n
      | _ -> Format.fprintf ppf "_var_%d (* %s *)" n desc
    else Format.fprintf ppf "%s" desc
end

module Int : Annotation with type t = int = struct
  type t = int

  let print _safe desc _n ppf = Format.fprintf ppf "%d" desc
end

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

module Make (Annot : Annotation) : S with type annot = Annot.t = struct
  type annot = Annot.t

  type t = int * annot

  let compare (n1, _) (n2, _) = Stdlib.compare n1 n2

  let new_fresh () =
    let count = ref (-1) in
    let fresh ann =
      incr count;
      (!count, ann)
    in
    fresh

  let fresh = new_fresh ()

  let refresh (_, ann) = fresh ann

  let print ?(safe = false) (n, ann) ppf = Annot.print safe ann n ppf

  let fold f (n, ann) = f ann n
end
