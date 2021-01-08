open CoreUtils
module FromNoEff = CodegenPlainOCaml_fromNoEff

module type BackendParameters = sig
  val output_file : string
end

module Backend (P : BackendParameters) = (*: BackendSignature.T *) struct
  (* ------------------------------------------------------------------------ *)
  (* Setup *)

  type state = {
    prog : OcamlSyntax.cmd list;
    typing : ExplicitInfer.state;
    env : TypeChecker.state;
  }

  let initial_state =
    {
      prog = [];
      typing = ExplicitInfer.initial_state;
      env = TypeChecker.initial_state;
    }

  (* Auxiliary functions *)
  let update state cmd explicit_st =
    { prog = state.prog @ [ cmd ]; typing = explicit_st; env = state.env }

  let process_type state ty =
    FromNoEff.elab_type
      (snd
         (ExeffToNoeff.type_elab state.typing state.env
            (Types.source_to_target ty)))

  (* ------------------------------------------------------------------------ *)
  (* Processing functions *)
  let process_computation state c ty =
    update state
      (OcamlSyntax.Term
         (FromNoEff.elab_term
            (snd (ExeffToNoeff.comp_elab state.typing state.env c))))
      state.typing

  let process_type_of state c ty =
    Print.warning
      "[#typeof] commands are ignored when compiling to Multicore OCaml.";
    state

  let process_def_effect state (eff, (ty1, ty2)) =
    update state
      (OcamlSyntax.DefEffect
         (eff, process_type state ty1, process_type state ty2))
      (ExplicitInfer.add_effect eff (ty1, ty2) state.typing)

  let process_top_let state defs vars =
    failwith "Top level bindings not supported"

  let process_top_let_rec state defs vars =
    failwith "Top level bindings not supported"

  let process_external state (x, ty, f) =
    let ty' = Types.source_to_target ty in
    let typing_state' = ExplicitInfer.addExternal state.typing x ty' in
    update state
      (OcamlSyntax.External (x, process_type state ty, f))
      typing_state'

  let process_tydef state tydefs =
    let converter (ty_params, tydef) =
      (ty_params, FromNoEff.elab_tydef (ExeffToNoeff.elab_tydef tydef))
    in
    let tydefs' = Assoc.map converter tydefs |> Assoc.to_list in
    update state (OcamlSyntax.TyDef tydefs') state.typing

  let finalize state =
    let channel = open_out P.output_file in
    let output_ppf = Format.formatter_of_out_channel channel in
    let header_file =
      Filename.concat
        (Filename.dirname Sys.argv.(0))
        "backendHeaderPlainOCaml.ml"
    in
    let header_channel = open_in header_file in
    let n = in_channel_length header_channel in
    let header = really_input_string header_channel n in
    close_in header_channel;
    Format.fprintf output_ppf "%s\n;;\n@." header;
    List.iter (fun cmd -> OcamlSyntax.print_command cmd output_ppf) state.prog;
    close_out channel
end
