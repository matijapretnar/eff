(* Evaluation of the intermediate language, big step. *)

open Utils
module V = Value
module CoreTypes = Language.CoreTypes
module Untyped = Language.UntypedSyntax
module Type = Language.Type

module Backend : Language.BackendSignature.T = struct
  type state = Eval.state

  let initial_state = Eval.initial_state

  let load_primitive_value state x prim =
    Eval.update x (Primitives.primitive_value prim) state

  let load_primitive_effect state eff prim =
    Eval.add_runner eff (Primitives.runner prim) state

  (* Processing functions *)
  let process_computation state c =
    let v = Eval.run state c in
    Format.fprintf !Config.output_formatter "@[- : %t = %t@]@."
      (Type.print_pretty () (fst c.ty).ty)
      (V.print_value v);
    state

  let process_type_of state c =
    Format.fprintf !Config.output_formatter "- : %t\n" (Type.print_dirty c.ty);
    state

  let process_def_effect state _ = state

  let process_top_let state defs =
    match Assoc.to_list defs with
    | [] -> state
    | [ (x, (_params, _constraints, exp)) ] ->
        let v = Eval.eval_expression state exp in
        Format.fprintf !Config.output_formatter "@[val %t : %t = %t@]@."
          (Language.CoreTypes.Variable.print x)
          (Type.print_pretty () exp.ty.ty)
          (V.print_value v);
        Eval.update x v state
    | _ -> failwith __LOC__

  let process_top_let_rec state defs =
    let defs = Assoc.map (fun (_params, _constraints, abs) -> abs) defs in
    Assoc.iter
      (fun (f, abs) ->
        Format.fprintf !Config.output_formatter "@[val %t : %t = <fun>@]@."
          (Language.CoreTypes.Variable.print f)
          (Type.print_pretty () (Type.arrow abs.ty).ty))
      defs;
    Eval.extend_let_rec state defs

  let process_tydef state _tydefs = state

  let finalize _state = ()
end
