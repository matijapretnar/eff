open Utils
open Language
open Parser
module TypeSystem = Typechecker.Infer

module type Shell = sig
  type state

  val initialize : unit -> state
  val execute_file : string -> state -> state
  val load_file : string -> state -> state
  val execute_source : string -> state -> state
  val load_source : string -> state -> state
  val finalize : state -> unit
end

module Make (Backend : Language.Backend.S) = struct
  type state = {
    desugarer_state : Desugarer.state;
    type_system_state : TypeSystem.state;
    optimizer_state : Optimizer.state;
    backend_state : Backend.state;
  }

  let add_primitive_effect state prim =
    let eff =
      Language.Term.Variable.fresh (Primitives.primitive_effect_name prim)
    in
    let type_system_state', eff' =
      TypeSystem.load_primitive_effect state.type_system_state eff prim
    in
    {
      state with
      desugarer_state =
        Desugarer.load_primitive_effect state.desugarer_state eff prim;
      type_system_state = type_system_state';
      backend_state =
        Backend.load_primitive_effect state.backend_state eff' prim;
    }

  let add_primitive_value state prim =
    let x =
      Language.Term.Variable.fresh (Primitives.primitive_value_name prim)
    in
    {
      state with
      desugarer_state =
        Desugarer.load_primitive_value state.desugarer_state x prim;
      type_system_state =
        TypeSystem.load_primitive_value state.type_system_state x prim;
      backend_state = Backend.load_primitive_value state.backend_state x prim;
    }

  let initialize () =
    Random.self_init ();
    let optimizer_state =
      Optimizer.initial_state
        {
          specialize_functions = !Config.optimizator_config.specialize_functions;
          eliminate_coercions = !Config.optimizator_config.eliminate_coercions;
          push_coercions = !Config.optimizator_config.push_coercions;
          handler_reductions = !Config.optimizator_config.handler_reductions;
          purity_aware_translation =
            !Config.optimizator_config.purity_aware_translation;
        }
    in
    let state =
      {
        desugarer_state = Desugarer.initial_state;
        type_system_state = TypeSystem.initial_state;
        optimizer_state;
        backend_state = Backend.initial_state;
      }
    in
    let state' =
      List.fold_left add_primitive_value state Primitives.primitive_values
    in
    let state'' =
      List.fold_left add_primitive_effect state' Primitives.primitive_effects
    in
    state''

  (* [exec_cmd ppf st cmd] executes toplevel command [cmd] in a state [st].
     It prints the result to [ppf] and returns the new state. *)
  let rec exec_cmd state { it = cmd; at = loc } =
    Print.debug "Executing command: %t" (Location.print loc);
    match cmd with
    | Commands.Term t ->
        let _, c = Desugarer.desugar_computation state.desugarer_state t in
        let c' = TypeSystem.process_computation state.type_system_state c in
        let c'' = Optimizer.process_computation state.optimizer_state c' in
        let backend_state' =
          Backend.process_computation state.backend_state c''
        in
        { state with backend_state = backend_state' }
    | Commands.TypeOf t ->
        let _, c = Desugarer.desugar_computation state.desugarer_state t in
        let top_comp =
          TypeSystem.process_computation state.type_system_state c
        in
        let top_comp' =
          Optimizer.process_computation state.optimizer_state top_comp
        in
        let backend_state' =
          Backend.process_type_of state.backend_state top_comp'
        in
        { state with backend_state = backend_state' }
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
          Desugarer.desugar_def_effect ~loc state.desugarer_state effect_def
        in
        let type_system_state', eff' =
          TypeSystem.process_def_effect eff (ty1, ty2) state.type_system_state
        in
        let backend_state' =
          Backend.process_def_effect state.backend_state eff'
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
          Desugarer.desugar_top_let ~loc state.desugarer_state defs
        in
        let type_system_state', defs'' =
          TypeSystem.process_top_let ~loc state.type_system_state defs'
        in
        let optimizer_state', defs''' =
          Optimizer.process_top_let state.optimizer_state defs''
        in
        let backend_state' =
          Backend.process_top_let state.backend_state defs'''
        in
        {
          desugarer_state = desugarer_state';
          type_system_state = type_system_state';
          optimizer_state = optimizer_state';
          backend_state = backend_state';
        }
    | Commands.TopLetRec defs ->
        let desugarer_state', defs' =
          Desugarer.desugar_top_let_rec state.desugarer_state defs
        in
        let defs'' = Assoc.of_list defs' in
        let type_system_state', defs''' =
          TypeSystem.process_top_let_rec ~loc state.type_system_state defs''
        in
        let optimizer_state', defs'''' =
          Optimizer.process_top_let_rec state.optimizer_state defs'''
        in
        let backend_state' =
          Backend.process_top_let_rec state.backend_state defs''''
        in
        {
          desugarer_state = desugarer_state';
          type_system_state = type_system_state';
          optimizer_state = optimizer_state';
          backend_state = backend_state';
        }
    | Commands.Tydef tydefs ->
        let desugarer_state', tydefs' =
          Desugarer.desugar_tydefs ~loc state.desugarer_state tydefs
        in
        let type_system_state' =
          TypeSystem.add_type_definitions state.type_system_state
            (tydefs' |> Assoc.to_list |> Type.Field.Map.of_bindings)
        in
        let backend_state' =
          Backend.process_tydef state.backend_state tydefs'
        in
        {
          state with
          desugarer_state = desugarer_state';
          type_system_state = type_system_state';
          backend_state = backend_state';
        }

  and exec_cmds state cmds = List.fold exec_cmd state cmds

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
