(** Configuration parameters *)

val version : string
(** Current version *)

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

val pervasives_file : pervasives ref
(** Location of the pervasives file *)

type backend =
  | Runtime
  | Ocaml of string
  | Multicore of string

val backend : backend ref

val disable_optimization : bool ref
(** Should compiled computations be optimized? *)

val profiling : bool ref
(** Should profiling be enabled? *)

val optimization_fuel : int ref

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

val pure_print : bool ref
(** Should we use pure printing for computations? *)

val explicit_subtyping : bool ref
(** Should we use the new explicit subtyping effect system? *)

val output_formatter : Format.formatter ref

val error_formatter : Format.formatter ref
