(** Configuration parameters *)

let version = "5.1"
let use_stdlib = ref true

type backend = Runtime | Multicore | Ocaml

let backend = ref Runtime
let ascii = ref false
let interactive_shell = ref true
let wrapper = ref (Some [ "rlwrap"; "ledit" ])
let include_header_open = ref true
let verbosity = ref 3
let output_formatter = ref Format.std_formatter
let error_formatter = ref Format.err_formatter
let enable_optimization = ref true
let profiling = ref false
let print_graph = ref false
let optimization_fuel = ref 5

type 'a optimizator_base_config = {
  specialize_functions : 'a;
  eliminate_coercions : 'a;
  push_coercions : 'a;
  handler_reductions : 'a;
  purity_aware_translation : 'a;
}

type optimizator_config = bool optimizator_base_config

let optimizator_config =
  ref
    {
      (* ok *)
      specialize_functions = true;
      (* plays badly with lambda_lift *)
      eliminate_coercions = true;
      (* ok *)
      push_coercions = true;
      (* ok *)
      handler_reductions = true;
      (* not ok *)
      purity_aware_translation = true;
    }
