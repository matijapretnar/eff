(* Compilation to multicore ocaml *)

open Utils

module Backend : Language.BackendSignature.T = struct
  (* ------------------------------------------------------------------------ *)
  (* Setup *)

  type state = { prog : Syntax.cmd list }

  let initial_state =
    {
      prog =
        [ (* Syntax.RawSource ("failwith", "failwith");
             Syntax.RawSource ("_ocaml_tophandler", Primitives.top_handler); *) ];
    }

  (* Auxiliary functions *)
  let update state cmd = { prog = state.prog @ [ cmd ] }

  (* ------------------------------------------------------------------------ *)
  (* Processing functions *)

  let load_primitive state x prim =
    update state (RawSource (x, Primitives.primitive_source prim))

  let process_computation state c _ty =
    let t = Translate.of_computation c in
    update state (Term t)

  let process_type_of state _c _ty =
    Print.warning
      "[#typeof] commands are ignored when compiling to Multicore OCaml.";
    state

  let process_def_effect state (eff, (ty1, ty2)) =
    let ty1' = Translate.of_type ty1 in
    let ty2' = Translate.of_type ty2 in
    update state (DefEffect (eff, (ty1', ty2')))

  let process_top_let state defs _vars =
    let converter (p, c) =
      (Translate.of_pattern p, Translate.of_computation c)
    in
    let defs' = List.map converter defs in
    update state (TopLet defs')

  let process_top_let_rec state defs _vars =
    let converter (p, c) =
      (Translate.of_pattern p, Translate.of_computation c)
    in
    let defs' = Assoc.map converter defs |> Assoc.to_list in
    update state (TopLetRec defs')

  let process_tydef state tydefs =
    let converter (ty_params, tydef) = (ty_params, Translate.of_tydef tydef) in
    let tydefs' = Assoc.map converter tydefs |> Assoc.to_list in
    update state (TyDef tydefs')

  let finalize state =
    List.iter
      (fun cmd -> Syntax.print_cmd cmd !Config.output_formatter)
      state.prog
end

let stdlib = Stdlib_eff.source
