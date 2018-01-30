type state

val initial_state : state

val use_file : Format.formatter -> string -> state -> state

val use_textfile : Format.formatter -> string -> state -> state

val use_toplevel : Format.formatter -> state -> state
