type state

val initial : state

val execute_file : Format.formatter -> string -> state -> state

val execute_source : Format.formatter -> string -> state -> state
