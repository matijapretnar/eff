(* Evaluation of the intermediate language, big step. *)

open Utils
module V = Value
module CoreTypes = Language.CoreTypes
module Type = Language.Type
module Untyped = Language.UntypedSyntax

module Backend : Language.BackendSignature.T = struct
  module RuntimeEnv = Map.Make (CoreTypes.Variable)

  type state = Eval.state

  let initial_state = Eval.initial_state

  let load_primitive state x prim =
    Eval.update x (Primitives.primitive_value prim) state

  (* Processing functions *)
  let process_computation state c ty =
    let v = Eval.run state c in
    Format.fprintf !Config.output_formatter "@[- : %t = %t@]@."
      (Type.print_beautiful ty) (V.print_value v);
    state

  let process_type_of state _c ty =
    Format.fprintf !Config.output_formatter "@[- : %t@]@."
      (Type.print_beautiful ty);
    state

  let process_def_effect state (_eff, (_ty1, _ty2)) = state

  let process_top_let state defs vars =
    let state' =
      List.fold_right
        (fun (p, c) st ->
          let v = Eval.run st c in
          Eval.extend p v st)
        defs state
    in
    List.iter
      (fun (x, tysch) ->
        match Eval.lookup x state' with
        | None -> assert false
        | Some v ->
            Format.fprintf !Config.output_formatter "@[val %t : %t = %t@]@."
              (CoreTypes.Variable.print x)
              (Type.print_beautiful tysch)
              (V.print_value v))
      vars;
    state'

  let process_top_let_rec state defs vars =
    let state' = Eval.extend_let_rec state defs in
    List.iter
      (fun (x, tysch) ->
        Format.fprintf !Config.output_formatter "@[val %t : %t = <fun>@]@."
          (CoreTypes.Variable.print x)
          (Type.print_beautiful tysch))
      vars;
    state'

  let process_tydef state _tydefs = state

  let finalize _state = ()
end
