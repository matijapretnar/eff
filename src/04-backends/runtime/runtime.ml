(* Evaluation of the intermediate language, big step. *)

open Utils
open Language
module V = Value
module Untyped = UntypedSyntax

module Backend : Language.BackendSignature.T = struct
  module RuntimeEnv = Map.Make (CoreTypes.Variable)

  type state = Eval.state

  let initial_state = Eval.initial_state

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
        (fun (p, e) st ->
          let v = Eval.eval st e in
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

  let process_external state (x, _ty, f) =
    match Assoc.lookup f External.values with
    | Some v -> Eval.update x v state
    | None -> Error.runtime "unknown external symbol %s." f

  let process_tydef state _tydefs = state

  let finalize _state = ()
end
