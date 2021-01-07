(** Pretty-printing functions *)

let message ~verbosity ?loc ~header fmt =
  if verbosity <= !Config.verbosity then
    match loc with
    | Some loc when loc <> Location.unknown ->
        Format.fprintf !Config.error_formatter
          ("%s (%t):@," ^^ fmt ^^ "@.")
          header (Location.print loc)
    | _ -> Format.fprintf !Config.error_formatter ("%s: " ^^ fmt ^^ "@.") header
  else Format.ifprintf !Config.error_formatter fmt

let error ?loc err_kind fmt = message ~verbosity:1 ?loc ~header:err_kind fmt

let check ?loc fmt = message ~verbosity:2 ?loc ~header:"Check" fmt

let warning ?loc fmt = message ~verbosity:3 ?loc ~header:"Warning" fmt

let debug ?loc fmt = message ~verbosity:4 ?loc ~header:"Debug" fmt

let print ?(at_level = min_int) ?(max_level = max_int) ppf =
  if at_level <= max_level then Format.fprintf ppf
  else fun fmt -> Format.fprintf ppf ("(" ^^ fmt ^^ ")")

let rec sequence sep pp vs ppf =
  match vs with
  | [] -> ()
  | [ v ] -> pp v ppf
  | v :: vs -> Format.fprintf ppf "%t%s@,%t" (pp v) sep (sequence sep pp vs)

let field fpp vpp (f, v) ppf = print ppf "%t = %t" (fpp f) (vpp v)

let tuple pp lst ppf =
  match lst with
  | [] -> print ppf "()"
  | lst -> print ppf "(@[<hov>%t@])" (sequence ", " pp lst)

let record fpp vpp assoc ppf =
  let lst = Assoc.to_list assoc in
  print ppf "{@[<hov>%t@]}" (sequence "; " (field fpp vpp) lst)
