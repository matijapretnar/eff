(** Configuration parameters *)

type pervasives =
  | PervasivesNone
  | PervasivesDefault
  | PervasivesFile of string

let pervasives_file = ref PervasivesDefault

let effect_annotations = ref true

let disable_beautify = ref false

let disable_typing = ref false

let ascii = ref false

let interactive_shell = ref true

let wrapper = ref (Some ["rlwrap"; "ledit"])

let verbosity = ref 3
