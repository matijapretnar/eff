(** Configuration parameters *)

let version = "5.0"

type pervasives =
  | PervasivesNone
  | PervasivesDefault
  | PervasivesFile of string

let pervasives_file = ref PervasivesDefault

let disable_typing = ref false

let ascii = ref false

let interactive_shell = ref true

let wrapper = ref (Some ["rlwrap"; "ledit"])

let verbosity = ref 3

let output_formatter = ref Format.std_formatter
