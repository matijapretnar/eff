open Utils
open Language
open CoreUtils
open Parser
module TypeSystem = Typechecker.SimpleInfer
module TypeContext = Typechecker.TypeContext

module type Shell = sig
  type state

  val initialize : unit -> state

  val execute_file : string -> state -> state

  val load_file : string -> state -> state

  val execute_source : string -> state -> state

  val load_source : string -> state -> state

  val finalize : state -> unit
end

module Make (Backend : Backend.BackendSignature.T) = struct
  type state = {
    desugarer_state : Desugarer.state;
    type_system_state : TypeSystem.state;
    backend_state : Backend.state;
    type_context_state : TypeContext.state;
  }

  let initialize () =
    Random.self_init ();
    {
      desugarer_state = Desugarer.initial_state;
      type_system_state = TypeSystem.initial_state;
      backend_state = Backend.initial_state;
      type_context_state = TypeContext.initial_state;
    }

  (* [exec_cmd ppf st cmd] executes toplevel command [cmd] in a state [st].
     It prints the result to [ppf] and returns the new state. *)
  let rec exec_cmd state { it = cmd; at = loc } =
    Print.debug "Executing: %t" (Location.print loc);
    match cmd with
    | Commands.Term t ->
        let _, c = Desugarer.desugar_computation state.desugarer_state t in
        let type_system_state', ty =
          TypeSystem.infer_top_comp state.type_system_state
            state.type_context_state c
        in
        let backend_state' =
          Backend.process_computation state.backend_state c ty
        in
        {
          state with
          type_system_state = type_system_state';
          backend_state = backend_state';
        }
    | Commands.TypeOf t ->
        let _, c = Desugarer.desugar_computation state.desugarer_state t in
        let type_system_state', ty =
          TypeSystem.infer_top_comp state.type_system_state
            state.type_context_state c
        in
        let backend_state' = Backend.process_type_of state.backend_state c ty in
        {
          state with
          type_system_state = type_system_state';
          backend_state = backend_state';
        }
    | Commands.Help ->
        let help_text =
          "Toplevel commands:\n"
          ^ "#type <expr>;;     print the type of <expr> without evaluating it\n"
          ^ "#help;;            print this help\n"
          ^ "#quit;;            exit eff\n"
          ^ "#use \"<file>\";;  load commands from file\n"
        in
        Format.fprintf !Config.output_formatter "%s@." help_text;
        state
    | Commands.DefEffect effect_def ->
        let desugarer_state', (eff, (ty1, ty2)) =
          Desugarer.desugar_def_effect state.desugarer_state effect_def
        in
        let type_system_state' =
          TypeSystem.add_effect state.type_system_state eff (ty1, ty2)
        in
        let backend_state' =
          Backend.process_def_effect state.backend_state (eff, (ty1, ty2))
        in
        {
          state with
          type_system_state = type_system_state';
          desugarer_state = desugarer_state';
          backend_state = backend_state';
        }
    | Commands.Quit ->
        Backend.finalize state.backend_state;
        exit 0
    | Commands.Use filename -> execute_file filename state
    | Commands.TopLet defs ->
        let desugarer_state', defs' =
          Desugarer.desugar_top_let state.desugarer_state defs
        in
        let vars, type_system_state' =
          TypeSystem.infer_top_let state.type_system_state
            state.type_context_state defs'
        in
        let backend_state' =
          Backend.process_top_let state.backend_state defs' vars
        in
        {
          state with
          desugarer_state = desugarer_state';
          type_system_state = type_system_state';
          backend_state = backend_state';
        }
    | Commands.TopLetRec defs ->
        let desugarer_state', defs' =
          Desugarer.desugar_top_let_rec state.desugarer_state defs
        in
        let vars, type_system_state' =
          TypeSystem.infer_top_let_rec state.type_system_state
            state.type_context_state defs'
        in
        let defs'' = Assoc.of_list defs' in
        let backend_state' =
          Backend.process_top_let_rec state.backend_state defs'' vars
        in
        {
          state with
          desugarer_state = desugarer_state';
          type_system_state = type_system_state';
          backend_state = backend_state';
        }
    | Commands.External ext_def ->
        let desugarer_state', (x, ty, f) =
          Desugarer.desugar_external state.desugarer_state ext_def
        in
        let type_system_state' =
          TypeSystem.extend state.type_system_state x (Type.free_params ty, ty)
        in
        let backend_state' =
          Backend.process_external state.backend_state (x, ty, f)
        in
        {
          state with
          desugarer_state = desugarer_state';
          type_system_state = type_system_state';
          backend_state = backend_state';
        }
    | Commands.Tydef tydefs ->
        let desugarer_state', tydefs' =
          Desugarer.desugar_tydefs state.desugarer_state tydefs
        in
        let type_context_state' =
          TypeContext.extend_type_definitions ~loc tydefs'
            state.type_context_state
        in
        let backend_state' =
          Backend.process_tydef state.backend_state tydefs'
        in
        {
          state with
          desugarer_state = desugarer_state';
          type_context_state = type_context_state';
          backend_state = backend_state';
        }

  and exec_cmds state cmds = fold exec_cmd state cmds

  and load_cmds state cmds =
    let old_output_formatter = !Config.output_formatter in
    Config.output_formatter :=
      Format.make_formatter (fun _ _ _ -> ()) (fun _ -> ());
    let state' = exec_cmds state cmds in
    Config.output_formatter := old_output_formatter;
    state'

  (* Parser wrapper *)
  and parse lexbuf =
    try Grammar.commands Lexer.token lexbuf with
    | Grammar.Error ->
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
end
