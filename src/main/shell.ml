open CoreUtils
module TypeSystem = SimpleInfer

module Backend = Eval.Backend

type state =
  { desugarer_state: Desugarer.state
  ; type_system_state: TypeSystem.state
  ; backend_state: Backend.state }

let initial_state =
  { desugarer_state= Desugarer.initial_state
  ; type_system_state= TypeSystem.initial_state
  ; backend_state= Backend.initial_state }

let _ = Random.self_init ()

(* [exec_cmd ppf st cmd] executes toplevel command [cmd] in a state [st].
   It prints the result to [ppf] and returns the new state. *)
let rec exec_cmd ppf state {it= cmd; at= loc} =
  match cmd with
  | Commands.Term t ->
      let _, c = Desugarer.desugar_computation state.desugarer_state t in
      let type_system_state', ty =
        TypeSystem.infer_top_comp state.type_system_state c
      in
      let backend_state' = 
        Backend.process_computation ppf state.backend_state c ty
      in
      { state with 
        type_system_state= type_system_state'
      ; backend_state= backend_state' }
  | Commands.TypeOf t ->
      let _, c = Desugarer.desugar_computation state.desugarer_state t in
      let type_system_state', ty =
        TypeSystem.infer_top_comp state.type_system_state c
      in
      let backend_state' = 
        Backend.process_type_of ppf state.backend_state c ty
      in
      { state with 
        type_system_state= type_system_state';
        backend_state= backend_state' }
  | Commands.Reset ->
      Tctx.reset () ;
      { desugarer_state= Desugarer.initial_state
      ; type_system_state= TypeSystem.initial_state
      ; backend_state= Backend.process_reset ppf state.backend_state }
  | Commands.Help ->
      { state with 
        backend_state= Backend.process_help ppf state.backend_state }
  | Commands.DefEffect effect_def ->
      let desugarer_state', (eff, (ty1, ty2)) =
        Desugarer.desugar_def_effect state.desugarer_state effect_def
      in
      let type_system_state' =
        SimpleCtx.add_effect state.type_system_state eff (ty1, ty2)
      in
      let backend_state' = 
        Backend.process_def_effect ppf state.backend_state (eff, (ty1, ty2))
      in
      { type_system_state= type_system_state'
      ; desugarer_state= desugarer_state' 
      ; backend_state= backend_state' }
  | Commands.Quit -> exit 0
  | Commands.Use filename -> execute_file ppf filename state
  | Commands.TopLet defs ->
      let desugarer_state', defs' =
        Desugarer.desugar_top_let state.desugarer_state defs
      in
      let vars, type_system_state' =
        TypeSystem.infer_top_let ~loc state.type_system_state defs'
      in
      let backend_state' = 
        Backend.process_top_let ppf state.backend_state defs' vars
      in
      { desugarer_state= desugarer_state'
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
        Backend.process_top_let_rec ppf state.backend_state defs'' vars
      in
      { desugarer_state= desugarer_state'
      ; type_system_state= type_system_state'
      ; backend_state= backend_state' }
  | Commands.External ext_def ->
      let desugarer_state', (x, ty, f) =
        Desugarer.desugar_external state.desugarer_state ext_def
      in
      let type_system_state' =
        SimpleCtx.extend state.type_system_state x (Type.free_params ty, ty)
      in
      let backend_state' =
        Backend.process_external ppf state.backend_state (x, ty, f)
      in
      { desugarer_state= desugarer_state'
      ; type_system_state= type_system_state'
      ; backend_state= backend_state' }
  | Commands.Tydef tydefs ->
      let desugarer_state', tydefs' =
        Desugarer.desugar_tydefs state.desugarer_state tydefs
      in
      Tctx.extend_tydefs ~loc tydefs' ;
      let backend_state' = 
        Backend.process_tydef ppf state.backend_state tydefs'
      in
      { state with
        desugarer_state= desugarer_state'
      ; backend_state= backend_state' }

and exec_cmds ppf state cmds = fold (exec_cmd ppf) state cmds

(* Parser wrapper *)
and parse lexbuf =
  try Parser.commands Lexer.token lexbuf with
  | Parser.Error ->
      Error.syntax ~loc:(Location.of_lexeme lexbuf) "parser error"
  | Failure failmsg when failmsg = "lexing: empty token" ->
      Error.syntax ~loc:(Location.of_lexeme lexbuf) "unrecognised symbol."

and execute_file ppf filename env =
  Lexer.read_file parse filename |> exec_cmds ppf env

and execute_source ppf str env =
  Lexer.read_string parse str |> exec_cmds ppf env
