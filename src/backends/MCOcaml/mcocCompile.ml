(* Evaluation of the intermediate language, big step. *)
open CoreUtils
module Untyped = UntypedSyntax


module Backend : BackendSignature.T = struct
  
  type state = string

  let initial_state = "TODO"

  (* Processing functions *)
  let process_computation ppf state c ty = failwith "TODO"

  let process_type_of ppf state c ty = failwith "TODO"

  let process_reset ppf state = failwith "TODO"

  let process_help ppf state = failwith "TODO"
  
  let process_def_effect ppf state (eff, (ty1, ty2)) = failwith "TODO"

  let process_top_let ppf state defs vars = failwith "TODO"

  let process_top_let_rec ppf state defs vars = failwith "TODO"

  let process_external ppf state (x, ty, f) = failwith "TODO"

  let process_tydef ppf state tydefs = failwith "TODO"

  let finalize ppf state = failwith "TODO"

end