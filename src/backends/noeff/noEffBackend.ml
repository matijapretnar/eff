open CoreUtils

module type BackendParameters = sig
  val output_file : string
end

module Backend (P : BackendParameters) : BackendSignature.T = struct
  (* ------------------------------------------------------------------------ *)
  (* Setup *)

  type state = {prog: NoEffSyntax.cmd list}

  let initial_state = {prog= []}

  (* Auxiliary functions *)
  let update state cmd =
    Print.debug "%t@?" (NoEffPrint.pp_cmd cmd) ;
    {prog= state.prog @ [cmd]}

  let unty_comp_to_noeff_comp c = 
    let _, {ExplicitInfer.computation = exeff_c}  = ExplicitInfer.type_computation ExplicitInfer.initial_state c in
    NoEffCompile.compile_comp exeff_c

  let process_type ty = NoEffCompile.compile_type (Types.source_to_target ty)

  (* ------------------------------------------------------------------------ *)
  (* Processing functions *)
  let process_computation state c ty = 
     update state (NoEffSyntax.Term (unty_comp_to_noeff_comp c))

  let process_type_of state c ty = failwith __LOC__

  let process_def_effect state (eff, (ty1, ty2)) = 
    update state (NoEffSyntax.DefEffect (eff, (process_type ty1, process_type ty2)))

  let process_top_let state defs vars = 
    let converter (p, c) =
      (NoEffCompile.compile_pattern (ExplicitInfer.type_pattern p), unty_comp_to_noeff_comp c)
    in 
    update state (NoEffSyntax.TopLet (List.map converter defs))

  let process_top_let_rec state defs vars = 
    let converter (p, c) =
      (NoEffCompile.compile_pattern (ExplicitInfer.type_pattern p), unty_comp_to_noeff_comp c)
    in 
    update state (NoEffSyntax.TopLetRec (Assoc.map converter defs |> Assoc.to_list))

  let process_external state (x, ty, f) = update state (NoEffSyntax.External (x, process_type ty, f))

  let process_tydef state tydefs = failwith __LOC__

  let finalize state = 
    let channel = open_out P.output_file in
    let output_ppf = Format.formatter_of_out_channel channel in
    List.iter (fun cmd -> NoEffPrint.pp_cmd cmd output_ppf) state.prog ;
    close_out channel
end
