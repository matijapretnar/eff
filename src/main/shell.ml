open CoreUtils
module TypeSystem = SimpleInfer
module EffectSystem = ExplicitInfer

module type Shell = sig
  type state

  val initialize : unit -> state

  val execute_file : string -> state -> state

  val load_file : string -> state -> state

  val execute_source : string -> state -> state

  val load_source : string -> state -> state

  val finalize : state -> unit
end

module Make (Backend : BackendSignature.T) = struct
  type state =
    { desugarer_state: Desugarer.state
    ; type_system_state: TypeSystem.state
    ; effect_system_state: EffectSystem.state
    ; type_checker_state: TypeChecker.state
    ; backend_state: Backend.state }

  let initialize () =
    Random.self_init () ;
    { desugarer_state= Desugarer.initial_state
    ; type_system_state= TypeSystem.initial_state
    ; effect_system_state= EffectSystem.initial_state
    ; type_checker_state= TypeChecker.initial_state
    ; backend_state= Backend.initial_state }

  (* [exec_cmd ppf st cmd] executes toplevel command [cmd] in a state [st].
    It prints the result to [ppf] and returns the new state. *)
  let rec exec_cmd state {it= cmd; at= loc} =
    match cmd with
    | Commands.Term t ->
        let t_start = Sys.time() in
        (* Desugar to ImpEff *)
        Print.debug "exec_cmd: before desugaring";
        let _, c = Desugarer.desugar_computation state.desugarer_state t in
        let type_system_state', _ =
          TypeSystem.infer_top_comp state.type_system_state c
        in
        Print.debug "exec_cmd: after desugaring";
        (* Format.fprintf !Config.error_formatter "%t\n"
         *   (UntypedSyntax.print_computation c); *)

        (* Elaborate to ExEff *)
        Print.debug "exec_cmd: before elaboration";
        let c', inferredExEffType =
          ExplicitInfer.tcTopLevelMono ~loc:c.at state.effect_system_state c
        (* let c' = ExplicitInfer.tcTopLevel ~loc:c.at
         *            state.effect_system_state c *)
        in
        Print.debug "exec_cmd: after elaboration";
        (* Format.fprintf !Config.error_formatter "%t\n"
         *   (Typed.print_computation c'); *)

        (* Typecheck ExEff *)
        Print.debug "exec_cmd: before backend typechecking";
        let drty = TypeChecker.typeOfComputation state.type_checker_state c' in
        Print.debug "exec_cmd: after backend typechecking";

        (* Optimize ExEff *)
        let c'' =
          if !Config.disable_optimization
          then c'
          else (
            Print.debug "exec_cmd: before optimization";
            let c_opt = Optimize.optimize_main_comp state.type_checker_state c' in
            Print.debug "exec_cmd: after optimization";
            (* Format.fprintf !Config.error_formatter "%t\n"
             *   (Typed.print_computation c_opt); *)
              c_opt
            )
        in

        (* Erase ExEff back to ImpEff *)
        Print.debug "exec_cmd: before erasure";
        let c'''= ErasureUntyped.typed_to_untyped_comp (Assoc.empty) c'' in
        Print.debug "exec_cmd: after erasure";
        (* Format.fprintf !Config.error_formatter "%t\n"
         *   (UntypedSyntax.print_computation c'''); *)

        (* Compile / Interpret ImpEff *)
        Print.debug "exec_cmd: begin processing by backend";
        let t1 = Sys.time() in
        let t_compile = t1 -. t_start in
        let backend_state' =
          Backend.process_computation state.backend_state c''' drty
        in
        let t2 = Sys.time() in
        let t_process = t2 -. t1 in
        if !Config.profiling then
          print_profiling t_compile t_process;
        { state with
          type_system_state= type_system_state'
        ; backend_state= backend_state' }
    | Commands.TypeOf t ->
        let _, c = Desugarer.desugar_computation state.desugarer_state t in
        let type_system_state', _ =
          TypeSystem.infer_top_comp state.type_system_state c
        in
        let c', inferredExEffType =
          ExplicitInfer.tcTopLevelMono ~loc:c.at state.effect_system_state c
        in
        let drty = TypeChecker.typeOfComputation state.type_checker_state c' in
        let backend_state' =
          Backend.process_type_of state.backend_state c drty
        in
        { state with
          type_system_state= type_system_state'
        ; backend_state= backend_state' }
    | Commands.Help ->
        let help_text =
          "Toplevel commands:\n"
          ^ "#type <expr>;;     print the type of <expr> without evaluating it\n"
          ^ "#help;;            print this help\n"
          ^ "#quit;;            exit eff\n"
          ^ "#use \"<file>\";;  load commands from file\n"
        in
        Format.fprintf !Config.output_formatter "%s@." help_text ;
        state
    | Commands.DefEffect effect_def ->
        let desugarer_state', (eff, (ty1, ty2)) =
          Desugarer.desugar_def_effect state.desugarer_state effect_def
        in
        let type_system_state' =
          SimpleCtx.add_effect state.type_system_state eff (ty1, ty2)
        in
        let effect_system_state' =
          ExplicitInfer.add_effect eff (ty1, ty2) state.effect_system_state
        in
        let backend_state' =
          Backend.process_def_effect state.backend_state (eff, (ty1, ty2))
        in
        { state with
          desugarer_state= desugarer_state'
        ; type_system_state= type_system_state'
        ; effect_system_state= effect_system_state'
        ; backend_state= backend_state' }
    | Commands.Quit ->
        Backend.finalize state.backend_state ;
        exit 0
    | Commands.Use filename -> execute_file filename state
    | Commands.TopLet defs ->
        let desugarer_state', defs' =
          Desugarer.desugar_top_let state.desugarer_state defs
        in
        let vars, type_system_state' =
          TypeSystem.infer_top_let ~loc state.type_system_state defs'
        in
        let backend_state' =
          Backend.process_top_let state.backend_state defs' vars
        in
        { state with
          desugarer_state= desugarer_state'
        ; type_system_state= type_system_state'
        ; backend_state= backend_state' }
    | Commands.TopLetRec defs ->
        let desugarer_state', defs' =
          Desugarer.desugar_top_let_rec state.desugarer_state defs
        in
        let vars, type_system_state' =
          TypeSystem.infer_top_let_rec ~loc state.type_system_state defs'
        in
        let defs'' = Assoc.of_list defs' in
        let backend_state' =
          Backend.process_top_let_rec state.backend_state defs'' vars
        in
        { state with
          desugarer_state= desugarer_state'
        ; type_system_state= type_system_state'
        ; backend_state= backend_state' }
    | Commands.External ext_def ->
        let desugarer_state', (x, ty, f) =
          Desugarer.desugar_external state.desugarer_state ext_def
        in
        let type_system_state' =
          SimpleCtx.extend state.type_system_state x (Type.free_params ty, ty)
        in
        let ty' = Types.source_to_target ty in
        let effect_system_state' =
          EffectSystem.addExternal state.effect_system_state x ty'
        in
        let type_checker_state' =
          TypeChecker.addExternal state.type_checker_state x ty'
        in
        let backend_state' =
          Backend.process_external state.backend_state (x, ty, f)
        in
        { desugarer_state= desugarer_state'
        ; type_system_state= type_system_state'
        ; effect_system_state= effect_system_state'
        ; type_checker_state= type_checker_state'
        ; backend_state= backend_state' }
    | Commands.Tydef tydefs ->
        let desugarer_state', tydefs' =
          Desugarer.desugar_tydefs state.desugarer_state tydefs
        in
        Tctx.extend_tydefs ~loc tydefs' ;
        let backend_state' =
          Backend.process_tydef state.backend_state tydefs'
        in
        { state with
          desugarer_state= desugarer_state'; backend_state= backend_state' }

  and exec_cmds state cmds = fold exec_cmd state cmds

  and load_cmds state cmds =
    let old_output_formatter = !Config.output_formatter in
    Config.output_formatter :=
      Format.make_formatter (fun _ _ _ -> ()) (fun _ -> ()) ;
    let state' = exec_cmds state cmds in
    Config.output_formatter := old_output_formatter ;
    state'

  (* Parser wrapper *)
  and parse lexbuf =
    try Parser.commands Lexer.token lexbuf with
    | Parser.Error ->
        Error.syntax ~loc:(Location.of_lexeme lexbuf) "parser error"
    | Failure failmsg when failmsg = "lexing: empty token" ->
        Error.syntax ~loc:(Location.of_lexeme lexbuf) "unrecognised symbol."

  and execute_file filename state =
    Lexer.read_file parse filename |> exec_cmds state

  and load_file filename state =
    Lexer.read_file parse filename |> load_cmds state

  and execute_source str state = Lexer.read_string parse str |> exec_cmds state

  and load_source str state = Lexer.read_string parse str |> load_cmds state

  and finalize state = Backend.finalize state.backend_state

  and print_profiling t_comp t_process =
    Format.fprintf !Config.output_formatter "Compile time: %f\n" t_comp;
    Format.fprintf !Config.output_formatter "Process time: %f\n" t_process;
      ()
end
