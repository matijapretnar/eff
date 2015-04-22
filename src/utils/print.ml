(** Pretty-printing functions *)

let message ~verbosity ?loc ~header fmt =
  if verbosity <= !Config.verbosity then
    match loc with
    | None -> Format.eprintf ("%s: " ^^ fmt ^^ "@.") header
    | Some loc -> Format.eprintf ("%s (%t): " ^^ fmt ^^ "@.") header (Location.print loc)
  else
    Format.ifprintf Format.err_formatter fmt

let error ?loc err_kind fmt = message ~verbosity:1 ?loc ~header:err_kind fmt

let check ?loc fmt = message ~verbosity:2 ?loc ~header:"Check" fmt

let warning ?loc fmt = message ~verbosity:3 ?loc ~header:"Warning" fmt

let debug ?loc fmt = message ~verbosity:4 ?loc ~header:"Debug" fmt

let print ?(at_level=min_int) ?(max_level=max_int) ppf =
  if at_level <= max_level then
    Format.fprintf ppf
  else
    fun fmt -> Format.fprintf ppf ("(@[" ^^ fmt ^^ "@])")

let rec sequence sep pp vs ppf =
  match vs with
  | [] -> ()
  | [v] -> pp v ppf
  | v :: vs -> Format.fprintf ppf "%t%s@,%t" (pp v) sep (sequence sep pp vs)

let field pp (f, v) ppf = print ppf "%s = %t" f (pp v)

let tuple pp lst ppf =
  match lst with
  | [] -> print ppf "()"
  | lst -> print ppf "(@[<hov>%t@])" (sequence ", " pp lst)

let record pp lst ppf =
  print ppf "{@[<hov>%t@]}" (sequence "; " (field pp) lst)
