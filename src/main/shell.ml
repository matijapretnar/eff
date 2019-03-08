let help_text =
  "Toplevel commands:\n"
  ^ "#type <expr>;;     print the type of <expr> without evaluating it\n"
  ^ "#reset;;           forget all definitions (including pervasives)\n"
  ^ "#help;;            print this help\n" ^ "#quit;;            exit eff\n"
  ^ "#use \"<file>\";;  load commands from file\n"

open CoreUtils
module TypeSystem = SimpleInfer
module Runtime = Eval

type state =
  { desugarer_state: Desugarer.state
  ; type_system_state: TypeSystem.state
  ; runtime_state: Runtime.state }

let initial_state =
  { desugarer_state= Desugarer.initial_state
  ; type_system_state= TypeSystem.initial_state
  ; runtime_state= Runtime.initial_state }

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
      let v = Runtime.run state.runtime_state c in
      Format.fprintf ppf "@[- : %t = %t@]@." (Type.print_beautiful ty)
        (Value.print_value v) ;
      {state with type_system_state= type_system_state'}
  | Commands.TypeOf t ->
      let _, c = Desugarer.desugar_computation state.desugarer_state t in
      let type_system_state', ty =
        TypeSystem.infer_top_comp state.type_system_state c
      in
      Format.fprintf ppf "@[- : %t@]@." (Type.print_beautiful ty) ;
      {state with type_system_state= type_system_state'}
  | Commands.Reset ->
      Format.fprintf ppf "Environment reset." ;
      Tctx.reset () ;
      initial_state
  | Commands.Help ->
      Format.fprintf ppf "%s" help_text ;
      state
  | Commands.DefEffect effect_def ->
      let desugarer_state', (eff, (ty1, ty2)) =
        Desugarer.desugar_def_effect state.desugarer_state effect_def
      in
      let type_system_state' =
        SimpleCtx.add_effect state.type_system_state eff (ty1, ty2)
      in
      {state with 
        type_system_state= type_system_state';
        desugarer_state= desugarer_state'}
  | Commands.Quit -> exit 0
  | Commands.Use filename -> execute_file ppf filename state
  | Commands.TopLet defs ->
      let desugarer_state', defs' =
        Desugarer.desugar_top_let state.desugarer_state defs
      in
      let vars, type_system_state' =
        TypeSystem.infer_top_let ~loc state.type_system_state defs'
      in
      let runtime_state' =
        List.fold_right
          (fun (p, c) env ->
            let v = Runtime.run env c in
            Runtime.extend p v env )
          defs' state.runtime_state
      in
      List.iter
        (fun (x, tysch) ->
          match Runtime.lookup x runtime_state' with
          | None -> assert false
          | Some v ->
              Format.fprintf ppf "@[val %t : %t = %t@]@."
                (CoreTypes.Variable.print x)
                (Type.print_beautiful tysch)
                (Value.print_value v) )
        vars ;
      { desugarer_state= desugarer_state'
      ; type_system_state= type_system_state'
      ; runtime_state= runtime_state' }
  | Commands.TopLetRec defs ->
      let desugarer_state', defs' =
        Desugarer.desugar_top_let_rec state.desugarer_state defs
      in
      let vars, type_system_state' =
        TypeSystem.infer_top_let_rec ~loc state.type_system_state defs'
      in
      let defs'' = Assoc.of_list defs' in
      let runtime_state' = Runtime.extend_let_rec state.runtime_state defs'' in
      List.iter
        (fun (x, tysch) ->
          Format.fprintf ppf "@[val %t : %t = <fun>@]@."
            (CoreTypes.Variable.print x)
            (Type.print_beautiful tysch) )
        vars ;
      { desugarer_state= desugarer_state'
      ; type_system_state= type_system_state'
      ; runtime_state= runtime_state' }
  | Commands.External ext_def -> (
      let desugarer_state', (x, ty, f) =
        Desugarer.desugar_external state.desugarer_state ext_def
      in
      match Assoc.lookup f External.values with
      | Some v ->
          let type_system_state' =
            SimpleCtx.extend state.type_system_state x (Type.free_params ty, ty)
          in
          { desugarer_state= desugarer_state'
          ; type_system_state= type_system_state'
          ; runtime_state= Runtime.update x v state.runtime_state }
      | None -> Error.runtime "unknown external symbol %s." f )
  | Commands.Tydef tydefs ->
      let desugarer_state', tydefs' =
        Desugarer.desugar_tydefs state.desugarer_state tydefs
      in
      Tctx.extend_tydefs ~loc tydefs' ;
      {state with desugarer_state= desugarer_state'}

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
