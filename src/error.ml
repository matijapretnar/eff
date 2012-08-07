(** Errors raised by eff. *)

(** Each error has a position, a type (typing/runtime/...), and a message. *)
exception Error of (Common.position * string * string)

(** [error ~pos err_type msg] raises an error with an optional position [pos],
    an error type [err_type], and a message [msg]. The [kfprintf] magic allows
    one to write [msg] using a format string and its arguments. *)
let error ~pos err_type =
  let k _ =
    let msg = Format.flush_str_formatter () in
    raise (Error (pos, err_type, msg))
  in
  Format.kfprintf k Format.str_formatter

(** Shortcut functions for raising the most common errors. For example, to
    raise a typing error one writes [Error.typing "Unknown name %s." x]. *)

let fatal ~pos = error ~pos "Fatal error"
let syntax ~pos = error ~pos "Syntax error"
let typing ~pos = error ~pos "Typing error"
let runtime ~pos = error ~pos "Runtime error"
let exc ~pos = error ~pos "Exception"
