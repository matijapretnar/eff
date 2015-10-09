type eff_state = (Ctx.t * (Scheme.dirty_scheme -> Scheme.dirty_scheme)) * Eval.env

val initial_state : eff_state

val parse :
  ((Lexing.lexbuf -> Parser.token) -> Lexing.lexbuf -> 'a) -> Lexing.lexbuf -> 'a

val exec_cmd : bool -> eff_state -> SugaredSyntax.toplevel -> eff_state

val use_file : eff_state -> string * bool -> eff_state
