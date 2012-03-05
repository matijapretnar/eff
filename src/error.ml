exception Error of (Common.position * string * string)

let error ?(pos=Common.Nowhere) err_type =
  let k _ =
    let msg = Format.flush_str_formatter () in
    raise (Error (pos, err_type, msg))
  in
  Format.kfprintf k Format.str_formatter

let fatal ?pos = error ?pos "Fatal"
let typing ?pos = error ?pos "Typing"
let runtime ?pos = error ?pos "Runtime"
let syntax ?pos = error ?pos "Syntax"
