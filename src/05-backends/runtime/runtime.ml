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
      (Type.print_dirty c.ty) (V.print_value v);
    state

  let process_type_of state c =
    Format.fprintf !Config.output_formatter "- : %t\n" (Type.print_dirty c.ty);
    state

  let process_def_effect state _ = state

  let process_top_let state defs =
    match Assoc.to_list defs with
    | [] -> state
    | [ (x, (_ws, exp)) ] ->
        let v = Eval.eval_expression state exp in
        Format.fprintf !Config.output_formatter "@[%t : %t = %t@]@."
          (Language.CoreTypes.Variable.print x)
          (Type.print_ty exp.ty) (V.print_value v);
        Eval.update x v state
    | _ -> failwith __LOC__

  let process_top_let_rec state defs =
    Assoc.iter
      (fun (f, (_ws, abs)) ->
        Format.fprintf !Config.output_formatter "@[%t : %t = <fun>@]@."
          (Language.CoreTypes.Variable.print f)
          (Type.print_ty (Type.arrow abs.ty)))
      defs;
    Eval.extend_let_rec state defs

  let process_tydef state _tydefs = state

  let finalize _state = ()
end
