(* Evaluation of the intermediate language, big step. *)

open Utils
module V = Value
module Type = Language.Type

module Backend : Language.Backend.S = struct
  type state = Eval.state

  let initial_state = Eval.initial_state

  let load_primitive_value state x prim =
    Eval.update x (Primitives.primitive_value prim) state

  let load_primitive_effect state eff prim =
    Eval.add_runner eff (Primitives.runner prim) state

  (* Processing functions *)
  let process_computation state ((params : Type.Params.t), c, _) =
    let v = Eval.run state c in
    Format.fprintf !Config.output_formatter "- : @[%t@] = @[%t@]@."
      (Type.print_pretty params.skel_params (fst c.ty).ty)
      (V.print_value v);
    state

  let process_type_of state (_, c, _) =
    Format.fprintf !Config.output_formatter "- : %t@." (Type.print_dirty c.ty);
    state

  let process_def_effect state _ = state

  let process_top_let state defs =
    match defs with
    | [] -> state
    | [ (pat, (params : Type.Params.t), _constraints, comp) ] ->
        let v = Eval.run state comp in
        Format.fprintf !Config.output_formatter "@[val %t : %t = %t@]@."
          (Language.Term.print_pattern pat)
          (Type.print_pretty params.skel_params (fst comp.ty).ty)
          (V.print_value v);
        Eval.extend pat v state
    | _ -> failwith __LOC__

  let process_top_let_rec state defs =
    Assoc.iter
      (fun (f, ((params : Type.Params.t), _constraints, abs)) ->
        Format.fprintf !Config.output_formatter "@[val %t : %t = <fun>@]@."
          (Language.Term.Variable.print f)
          (Type.print_pretty params.skel_params (Type.arrow abs.ty).ty))
      defs;
    Eval.extend_let_rec state (Assoc.map (fun (_, _, abs) -> abs) defs)

  let process_tydef state _tydefs = state
  let finalize _state = ()
end
