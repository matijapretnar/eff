(** Configuration parameters *)

type pervasives =
  | PervasivesNone
  | PervasivesDefault
  | PervasivesFile of string

let pervasives_file = ref PervasivesDefault

let effect_annotations = ref true

let disable_beautify = ref false

let disable_typing = ref false

let disable_optimization = ref false

let optimization_fuel = ref 100

let ascii = ref false

let interactive_shell = ref true

(*let wrapper = ref (Some ["rlwrap"; "ledit"])*)

let wrapper = ref None

let verbosity = ref 3

let smart_print = ref true

let pure_print = ref false

let explicit_subtyping = ref false
