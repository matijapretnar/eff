(** Configuration parameters *)

val version : string
(** Current version *)

val use_stdlib : bool ref
(** Should we load the standard library? *)

type backend = Runtime | Multicore | Ocaml

val backend : backend ref

val ascii : bool ref
(** Should we use ASCII instead of Unicode for printing out types? *)

val interactive_shell : bool ref
(** Should the interactive shell be run? *)

val wrapper : string list option ref
(** The command-line wrappers that we look for *)

val include_header_open : bool ref
(** Should we include the open OcamlHeader in the generated files? *)

val verbosity : int ref
(** Select which messages should be printed:
    - 0 no messages
    - 1 only errors
    - 2 errors and check
    - 3 errors, check, and warnings
    - 4 errors, check, warnings, and debug messages *)

val output_formatter : Format.formatter ref
val error_formatter : Format.formatter ref

val enable_optimization : bool ref
(** Should compiled computations be optimized? *)

val print_graph : bool ref

val profiling : bool ref
(** Should profiling be enabled? *)

val optimization_fuel : int ref

type 'a optimizator_base_config = {
  specialize_functions : 'a;
  eliminate_coercions : 'a;
  push_coercions : 'a;
  handler_reductions : 'a;
  purity_aware_translation : 'a;
}

type optimizator_config = bool optimizator_base_config

val optimizator_config : optimizator_config ref
