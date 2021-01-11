(* Compilation to multicore ocaml *)
open Utils

module type BackendParameters = sig
  val output_file : string
end

module Backend (P : BackendParameters) : Language.BackendSignature.T = struct
  (* ------------------------------------------------------------------------ *)
  (* Setup *)

  type state = { effect_system_state : ExplicitInfer.state }

  let initial_state = { effect_system_state = ExplicitInfer.initial_state }

  (* ------------------------------------------------------------------------ *)
  (* Processing functions *)
  let process_computation state _c _ = state

  let process_type_of state _ _ = state

  let process_def_effect state (eff, (ty1, ty2)) =
    let effect_system_state' =
      ExplicitInfer.add_effect eff (ty1, ty2) state.effect_system_state
    in
    { effect_system_state = effect_system_state' }

  let process_top_let state _ _ =
    Print.debug "ignoring top let binding";
    state

  let process_top_let_rec state _ _ =
    Print.debug "ignoring top let rec binding";
    state

  let process_external state _ = state

  let process_tydef state _ = state

  let finalize _ =
    let channel = open_out P.output_file in
    let output_ppf = Format.formatter_of_out_channel channel in
    Format.fprintf output_ppf "TEST@.";
    close_out channel
end
