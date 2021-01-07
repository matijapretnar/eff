let compile_file ppf filename st =
  let out_channel = open_out (filename ^ ".ml") in
  let out_ppf = Format.formatter_of_out_channel out_channel in
  (* look for header.ml next to the executable  *)
  let header_file_basename =
    match !Config.backend with
    | Config.MulticoreOCaml -> "backendHeaderMulticoreOCaml.ml"
    | Config.PlainOCaml -> "backendHeaderPlainOCaml.ml"
  in
  let header_file =
    Filename.concat (Filename.dirname Sys.argv.(0)) header_file_basename
  in
  let header_channel = open_in header_file in
  let n = in_channel_length header_channel in
  let header = really_input_string header_channel n in
  close_in header_channel;
  Format.fprintf out_ppf "%s\n;;\n@." header;
  let compile_cmd state cmd =
    let loc = cmd.CoreUtils.at in
    match cmd.CoreUtils.it with
    | Commands.Term t ->
        let desugarer_state', c =
          Desugarer.desugar_computation state.desugarer_state t
        in
        Print.debug "Compiling: %t" (UntypedSyntax.print_computation c);
        let ct, effect_system_state =
          ExplicitInfer.type_toplevel ~loc state.effect_system_state c
        in
        Print.debug
          "-- After Type Inference ----------------------------------------";
        Print.debug "%t" (Typed.print_computation ct);
        let ct =
          if !Config.disable_optimization then ct
          else Optimize.optimize_main_comp state.type_checker_state ct
        in
        Print.debug
          "-- After Optimization ------------------------------------------";
        Print.debug "%t" (Typed.print_computation ct);
        let ct_ty, ct_dirt =
          TypeChecker.type_of_computation state.type_checker_state ct
        in
        Print.debug "Type from Type Checker : %t ! %t"
          (Types.print_target_ty ct_ty)
          (Types.print_target_dirt ct_dirt);
        let erasure_ct = Erasure.typed_to_erasure_comp Assoc.empty ct in
        (match !Config.backend with
        | MulticoreOCaml ->
            CodegenMulticoreOCaml.print_computation erasure_ct out_ppf
        | PlainOCaml -> CodegenPlainOCaml.print_computation erasure_ct out_ppf);
        Format.fprintf out_ppf "\n;;\n ";
        print_endline "ended found something!";
        { state with desugarer_state = desugarer_state'; effect_system_state }
    | Commands.DefEffect tydef ->
        let eff, (ty1, ty2) =
          Desugarer.desugar_def_effect state.desugarer_state tydef
        in
        let effect_system_state =
          ExplicitInfer.add_effect eff (ty1, ty2) state.effect_system_state
        in
        Print.print out_ppf
          "type (_, _) effect += Effect_%s : (int, int) effect" eff;
        Format.fprintf out_ppf "\n;;\n ";
        { st with effect_system_state }
    | Commands.External ext -> (
        let desugarer_state, (x, ty, f) =
          Desugarer.desugar_external state.desugarer_state ext
        in
        match Assoc.lookup f External.values with
        | Some v ->
            let new_ty = Types.source_to_target ty in
            Print.print out_ppf "let %t = ( %s )"
              (CodegenPlainOCaml.print_variable x)
              f;
            Format.fprintf out_ppf "\n;;\n ";
            {
              st with
              type_system_state =
                SimpleCtx.extend state.type_system_state x
                  (Type.free_params ty, ty);
              effect_system_state =
                {
                  state.effect_system_state with
                  ExplicitInfer.context =
                    TypingEnv.update state.effect_system_state.context x new_ty;
                };
              type_checker_state =
                TypeChecker.extend_var_types state.type_checker_state x new_ty;
              runtime_state = Eval.update x v state.runtime_state;
            }
        | None -> Error.runtime "unknown external symbol %s." f)
    | _ -> st
  in
  let cmds = Lexer.read_file parse filename in
  let st = List.fold_left compile_cmd st (List.rev cmds) in
  Format.fprintf out_ppf "@? ";
  flush out_channel;
  close_out out_channel;
  st
