(** Configuration parameters *)

let version = "5.1"

type pervasives =
  | PervasivesNone
  | PervasivesDefault
  | PervasivesFile of string

let pervasives_file = ref PervasivesDefault

let disable_typing = ref false

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
