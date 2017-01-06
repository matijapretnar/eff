type state = {
  environment : RuntimeEnv.t;
  typing : Infer.toplevel_state;
}

val initial_state : state

val parse :
  ((Lexing.lexbuf -> Parser.token) -> Lexing.lexbuf -> 'a) -> Lexing.lexbuf -> 'a

val exec_cmd : Format.formatter -> bool -> state -> Untyped.toplevel -> state

val use_file : Format.formatter -> state -> string * bool -> state
