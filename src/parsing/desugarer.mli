type state

val initial_state : state

val desugar_commands :
  state -> SugaredSyntax.commands -> state * CoreSyntax.commands
