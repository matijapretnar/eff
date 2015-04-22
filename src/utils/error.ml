(** Error reporting *)

type details = Location.t * string * string

let print (loc, err_kind, msg) =
  Print.error ~loc err_kind "%s" msg

exception Error of details

(** [error ~loc err_kind fmt] raises an [Error] of kind [err_kind] with a
    message [fmt] at a location [loc]. The [kfprintf] magic allows us to
    construct the [fmt] using a format string before raising the exception. *)
let error ?loc:(loc=Location.unknown) err_kind =
  let k _ =
    let msg = Format.flush_str_formatter () in
    raise (Error (loc, err_kind, msg))
  in
  fun fmt -> Format.kfprintf k Format.str_formatter ("@[" ^^ fmt ^^ "@]")

let fatal fmt = error "Fatal error" fmt
let syntax ~loc fmt = error ~loc "Syntax error" fmt
let typing ~loc fmt = error ~loc "Typing error" fmt
let runtime fmt = error "Runtime error" fmt
