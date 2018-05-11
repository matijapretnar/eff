type state

val initial : state

val desugar_commands :
  state -> SugaredSyntax.commands -> state * CoreSyntax.commands
