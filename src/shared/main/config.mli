(** Configuration parameters *)

val version : string
(** Current version *)

val use_stdlib : bool ref
(** Should we load the standard library? *)

type backend = Runtime | Multicore of string

val backend : backend ref

val ascii : bool ref
(** Should we use ASCII instead of Unicode for printing out types? *)

val interactive_shell : bool ref
(** Should the interactive shell be run? *)

val wrapper : string list option ref
(** The command-line wrappers that we look for *)

val verbosity : int ref
(** Select which messages should be printed:
    - 0 no messages
    - 1 only errors
    - 2 errors and check
    - 3 errors, check, and warnings
    - 4 errors, check, warnings, and debug messages *)

val output_formatter : Format.formatter ref

val error_formatter : Format.formatter ref
