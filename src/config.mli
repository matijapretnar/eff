(** Configuration parameters *)

(** Possible locations of pervasives file

    Unless specified otherwise, we look for pervasives.eff _first_ next to the
    executable and _then_ in the relevant install directory. This makes it
    easier to experiment with pervasives.eff because Eff will work straight
    from the build directory. We are probably creating a security hole, but
    we'll deal with that when Eff actually gets used by more than a dozen
    people. *)
type pervasives =
  | PervasivesNone
  (* do not use pervasives *)
  | PervasivesDefault
  (* look in the default locations *)
  | PervasivesFile of string

(* look for pervasives in a specific location *)

val pervasives_file : pervasives ref
(** Location of the pervasives file *)

val disable_typing : bool ref
(** Should type-checking be disabled? *)

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
