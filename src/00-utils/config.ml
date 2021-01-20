(** Configuration parameters *)

let version = "5.1"

let use_stdlib = ref false

type backend = Runtime | Multicore | Ocaml | ExplicitEffects

let backend = ref Runtime

let ascii = ref false

let interactive_shell = ref true

let wrapper = ref (Some [ "rlwrap"; "ledit" ])

let verbosity = ref 3

let output_formatter = ref Format.std_formatter

let error_formatter = ref Format.err_formatter

let enable_optimization = ref true

let profiling = ref false

let optimization_fuel = ref 100

let pure_print = ref false

let include_header = ref true
