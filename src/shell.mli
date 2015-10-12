type eff_state = (Ctx.t * (Scheme.dirty_scheme -> Scheme.dirty_scheme)) * Eval.env

val initial_state : eff_state

val parse :
  ((Lexing.lexbuf -> Parser.token) -> Lexing.lexbuf -> 'a) -> Lexing.lexbuf -> 'a

val exec_cmd : Format.formatter -> bool -> eff_state -> SugaredSyntax.toplevel -> eff_state

val use_file : Format.formatter -> eff_state -> string * bool -> eff_state
