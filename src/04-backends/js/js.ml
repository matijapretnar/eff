(* Evaluation of the intermediate language, big step. *)
open Utils

module Backend : Language.BackendSignature.T = struct
  (* ------------------------------------------------------------------------ *)
  (* Setup *)

  type state = { prog : Syntax.cmd list }

  let initial_state = { prog = [] }

  (* Auxiliary functions *)
  let update state cmd =
    Print.debug "%t@?" (Syntax.print_cmd cmd);
    { prog = state.prog @ [ cmd ] }

  (* ------------------------------------------------------------------------ *)
  (* Processing functions *)
  let process_computation state c _ =
    let t = Translate.of_computation c in
    update state @@ Term t

  let process_type_of state _ _ =
    Print.warning "[#typeof] commands are ignored when compiling to JavaScript.";
    state

  let process_def_effect state _ =
    Print.warning "[effect] commands are ignored when compiling to JavaScript.";
    state

  let process_top_let state defs _ =
    let to_top_let_term abs =
      let _match, projections, term = Translate.of_abstraction_generic abs in
      (_match, term, Syntax.Sequence projections)
    in
    let top_let_terms = List.map to_top_let_term defs in
    update state @@ TopLet top_let_terms

  let process_top_let_rec state defs _ =
    let wrap_with_lambda (var, abs) =
      Syntax.Let (var, Lambda (Translate.of_abstraction abs))
    in
    let sequential_lets = List.map wrap_with_lambda @@ Assoc.to_list defs in
    update state @@ TopLetRec (Syntax.Sequence sequential_lets)

  let process_external state (x, _, f) = update state @@ External (x, f)

  let process_tydef state _ =
    Print.warning "[tydef] commands are ignored when compiling to JavaScript.";
    state

  let finalize state =
    let ppf = !Config.output_formatter in
    Format.fprintf ppf "%s@." Stdlib_js.source;
    List.iter (fun cmd -> Syntax.print_cmd cmd ppf) state.prog
end

let stdlib = Stdlib_eff.source
