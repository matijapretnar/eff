type state

val initial_state : state

val use_file : Format.formatter -> state -> string * bool -> state
val use_textfile : Format.formatter -> state -> string -> state
val use_toplevel : Format.formatter -> state -> state
