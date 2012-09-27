exception Error of (Common.position option * string * string)

(** [error ?pos err_type msg] raises an error with a position [pos], an error
    type [err_type], and a message [msg]. The [kfprintf] magic allows
    one to write the message using a format string. *)
let error ?pos err_type =
  let k _ =
    let msg = Format.flush_str_formatter () in
    raise (Error (pos, err_type, msg))
  in
  Format.kfprintf k Format.str_formatter

let fatal msg = error "Fatal error" msg
let syntax ~pos = error ~pos "Syntax error"
let typing ~pos = error ~pos "Typing error"
let runtime msg = error "Runtime error" msg
