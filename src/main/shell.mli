type state

val initial_state : state

val execute_file : Format.formatter -> string -> state -> state

val execute_source : Format.formatter -> string -> state -> state

val compile_file : Format.formatter -> string -> state -> state
