(** Configuration parameters *)

let version = "5.1"

type pervasives = PervasivesNone | PervasivesDefault

let pervasives_file = ref PervasivesDefault

type backend = Runtime | Ocaml of string | Multicore of string

let backend = ref Runtime

let disable_optimization = ref false

let optimization_fuel = ref 100

let ascii = ref false

let interactive_shell = ref true

(*let wrapper = ref (Some ["rlwrap"; "ledit"])*)

let wrapper = ref None

let verbosity = ref 3

let pure_print = ref false

let explicit_subtyping = ref false

let output_formatter = ref Format.std_formatter

let error_formatter = ref Format.err_formatter
