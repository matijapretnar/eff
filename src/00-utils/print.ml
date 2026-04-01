(** Pretty-printing functions *)

let () =
  Format.pp_set_max_indent !Config.error_formatter 1000;
  Format.pp_set_margin !Config.error_formatter 1000

let message ~verbosity ?loc ~header fmt =
  if verbosity <= !Config.verbosity then
    match loc with
    | Some loc ->
        Format.fprintf !Config.error_formatter
          ("%s (%t):@," ^^ fmt ^^ "@.")
          header (Location.print loc)
    | None ->
        Format.fprintf !Config.error_formatter ("%s: " ^^ fmt ^^ "@.") header
  else Format.ifprintf !Config.error_formatter fmt

let error ?loc err_kind fmt = message ~verbosity:1 ?loc ~header:err_kind fmt
let check ?loc fmt = message ~verbosity:2 ?loc ~header:"Check" fmt
let warning ?loc fmt = message ~verbosity:3 ?loc ~header:"Warning" fmt

let print ?(at_level = min_int) ?(max_level = max_int) ppf =
  if at_level <= max_level then Format.fprintf ppf
  else fun fmt -> Format.fprintf ppf ("(" ^^ fmt ^^ ")")

let sequence sep pp vs ppf =
  let i = String.length sep - 1 in
  let space = sep.[i] = ' ' in
  let sep = if space then String.sub sep 0 i else sep in
  let rec aux vs ppf =
    match vs with
    | [] -> ()
    | [ v ] -> pp v ppf
    | v :: vs when space -> Format.fprintf ppf "%t%s@ %t" (pp v) sep (aux vs)
    | v :: vs -> Format.fprintf ppf "%t%s@ %t" (pp v) sep (aux vs)
  in
  aux vs ppf

let printer_sequence sep printers ppf =
  sequence sep (fun printer ppf -> printer ppf) printers ppf

let field fpp vpp (f, v) ppf = print ppf "%t = %t" (fpp f) (vpp v)

let tuple pp lst ppf =
  match lst with
  | [] -> print ppf "()"
  | lst -> print ppf "(@[<hov>%t@])" (sequence ", " pp lst)

let record fpp vpp lst ppf =
  print ppf "{@[<hov>%t@]}" (sequence "; " (field fpp vpp) lst)

let debug_stack = ref []
let debug_depth = ref 0

let debug ?loc fmt =
  message ~verbosity:4 ?loc
    ~header:("Debug " ^ String.make (2 * !debug_depth) ' ')
    fmt

let open_scope fmt =
  Format.kfprintf
    (fun _ ->
      let scope = Format.flush_str_formatter () in
      debug "%s {" scope;
      debug_stack := scope :: !debug_stack;
      incr debug_depth)
    Format.str_formatter
    ("@[" ^^ fmt ^^ "@]")

let close_scope () =
  match !debug_stack with
  | [] -> assert false
  | scope :: scopes ->
      debug_stack := scopes;
      decr debug_depth;
      debug "%s }" scope
