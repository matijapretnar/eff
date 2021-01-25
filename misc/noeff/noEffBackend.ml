module type BackendParameters = sig
  val output_file : string
end

module Backend (P : BackendParameters) : BackendSignature.T = struct
  (* ------------------------------------------------------------------------ *)
  (* Setup *)

  type state = { prog : NoEffSyntax.cmd list; typing : ExplicitInfer.state }

  let initial_state = { prog = []; typing = ExplicitInfer.initial_state }

  (* Auxiliary functions *)
  let update state cmd explicit_st =
    { prog = state.prog @ [ cmd ]; typing = explicit_st }

  let process_type ty = NoEffCompile.compile_type (Type.source_to_target ty)

  (* ------------------------------------------------------------------------ *)
  (* Processing functions *)
  let process_computation state c ty =
    let ex_st', { ExplicitInfer.computation = exeff_c } =
      ExplicitInfer.type_computation state.typing c
    in
    update state (NoEffSyntax.Term (NoEffCompile.compile_comp exeff_c)) ex_st'

  let process_type_of state c ty = failwith __LOC__ (* not implemented *)

  let process_def_effect state (eff, (ty1, ty2)) =
    update state
      (NoEffSyntax.DefEffect (eff, (process_type ty1, process_type ty2)))
      (ExplicitInfer.add_effect eff (ty1, ty2) state.typing)

  let process_top_let state defs vars = failwith __LOC__ (* not implemented *)

  let process_top_let_rec state defs vars = failwith __LOC__

  (* not implemented *)

  let process_external state (x, ty, f) =
    let ty' = Type.source_to_target ty in
    let typing_state' = ExplicitInfer.add_external state.typing x ty' in
    update state (NoEffSyntax.External (x, process_type ty, f)) typing_state'

  let process_tydef state tydefs = failwith __LOC__ (* not implemented *)

  let finalize state =
    let channel = open_out P.output_file in
    let output_ppf = Format.formatter_of_out_channel channel in
    NoEffPrint.pp_header output_ppf;
    List.iter (fun cmd -> NoEffPrint.pp_cmd cmd output_ppf) state.prog;
    close_out channel
end
