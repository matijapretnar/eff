(* Compilation to multicore ocaml *)
open Utils

module Evaluate : Language.BackendSignature.T = struct
  (* ------------------------------------------------------------------------ *)
  (* Setup *)

  type state = { effect_system_state : ExplicitInfer.state; prog : string list }

  let initial_state =
    { effect_system_state = ExplicitInfer.initial_state; prog = [] }

  (* ------------------------------------------------------------------------ *)
  (* Processing functions *)
  let process_computation state c tysch =
    let c', _ty' =
      ExplicitInfer.tcTopLevelMono ~loc:Location.unknown
        state.effect_system_state c
    in
    state

  let process_type_of state c _tysch =
    let _, ty =
      ExplicitInfer.tcTopLevelMono ~loc:Location.unknown
        state.effect_system_state c
    in
    Format.fprintf Format.str_formatter "- : %t\n" (Types.print_target_dirty ty);
    { state with prog = Format.flush_str_formatter () :: state.prog }

  let process_def_effect state (eff, (ty1, ty2)) =
    let effect_system_state' =
      ExplicitInfer.add_effect eff (ty1, ty2) state.effect_system_state
    in
    { state with effect_system_state = effect_system_state' }

  let process_top_let state _defs _vars =
    Print.debug "ignoring top let binding";
    state

  let process_top_let_rec state _ _ =
    Print.debug "ignoring top let rec binding";
    state

  let process_external state (x, ty, _name) =
    let effect_system_state' =
      ExplicitInfer.addExternal state.effect_system_state x ty
    in
    { state with effect_system_state = effect_system_state' }

  let process_tydef state tydefs =
    let effect_system_state' =
      ExplicitInfer.add_type_definitions state.effect_system_state tydefs
    in
    { state with effect_system_state = effect_system_state' }

  let finalize state =
    List.iter
      (fun x -> Format.fprintf !Config.output_formatter "%s\n" x)
      (List.rev state.prog)
end

module CompileToPlainOCaml : Language.BackendSignature.T = struct
  (* ------------------------------------------------------------------------ *)
  (* Setup *)

  type state = { effect_system_state : ExplicitInfer.state; prog : string list }

  let initial_state =
    { effect_system_state = ExplicitInfer.initial_state; prog = [] }

  (* ------------------------------------------------------------------------ *)
  (* Processing functions *)
  let process_computation state c tysch =
    let c', _ty' =
      ExplicitInfer.tcTopLevelMono ~loc:Location.unknown
        state.effect_system_state c
    in
    state

  let process_type_of state c _tysch =
    let _, ty =
      ExplicitInfer.tcTopLevelMono ~loc:Location.unknown
        state.effect_system_state c
    in
    Format.fprintf Format.str_formatter "- : %t\n" (Types.print_target_dirty ty);
    { state with prog = Format.flush_str_formatter () :: state.prog }

  let process_def_effect state (eff, (ty1, ty2)) =
    let effect_system_state' =
      ExplicitInfer.add_effect eff (ty1, ty2) state.effect_system_state
    in
    { state with effect_system_state = effect_system_state' }

  let process_top_let state _defs _vars =
    Print.debug "ignoring top let binding";
    state

  let process_top_let_rec state _ _ =
    Print.debug "ignoring top let rec binding";
    state

  let process_external state (x, ty, _name) =
    let effect_system_state' =
      ExplicitInfer.addExternal state.effect_system_state x ty
    in
    { state with effect_system_state = effect_system_state' }

  let process_tydef state tydefs =
    let effect_system_state' =
      ExplicitInfer.add_type_definitions state.effect_system_state tydefs
    in
    { state with effect_system_state = effect_system_state' }

  let finalize state =
    List.iter
      (fun x -> Format.fprintf !Config.output_formatter "%s\n" x)
      (List.rev state.prog)
end
