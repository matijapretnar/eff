(** Error reporting *)

type t = Location.t * string * string

let print (loc, error_kind, msg) = Print.error ~loc error_kind "%s" msg

exception Error of t

(** [error ~loc error_kind fmt] raises an [Error] of kind [error_kind] with a
    message [fmt] at a location [loc]. The [kfprintf] magic allows us to
    construct the [fmt] using a format string before raising the exception. *)
let error ?(loc = Location.unknown) error_kind =
  let k _ =
    let msg = Format.flush_str_formatter () in
    raise (Error (loc, error_kind, msg))
  in
  fun fmt -> Format.kfprintf k Format.str_formatter ("@[" ^^ fmt ^^ "@]")

let fatal ?loc fmt = error ?loc "Fatal error" fmt

let syntax ~loc fmt = error ~loc "Syntax error" fmt

let typing ~loc fmt = error ~loc "Typing error" fmt

let runtime ?loc fmt = error ?loc "Runtime error" fmt
