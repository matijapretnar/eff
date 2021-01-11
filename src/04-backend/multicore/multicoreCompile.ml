(* Compilation to multicore ocaml *)

open Utils

module type BackendParameters = sig
  val output_file : string
end

module Backend (P : BackendParameters) : Backend.BackendSignature.T = struct
  (* ------------------------------------------------------------------------ *)
  (* Setup *)

  type state = { prog : MulticoreSyntax.cmd list }

  let initial_state = { prog = [] }

  (* Auxiliary functions *)
  let update state cmd =
    Print.debug "%t@?" (MulticoreSyntax.print_cmd cmd);
    { prog = state.prog @ [ cmd ] }

  (* ------------------------------------------------------------------------ *)
  (* Processing functions *)
  let process_computation state c _ty =
    let t = MulticoreTranslate.of_computation c in
    update state (Term t)

  let process_type_of state _c _ty =
    Print.warning
      "[#typeof] commands are ignored when compiling to Multicore OCaml.";
    state

  let process_def_effect state (eff, (ty1, ty2)) =
    let ty1' = MulticoreTranslate.of_type ty1 in
    let ty2' = MulticoreTranslate.of_type ty2 in
    update state (DefEffect (eff, (ty1', ty2')))

  let process_top_let state defs _vars =
    let converter (p, c) =
      (MulticoreTranslate.of_pattern p, MulticoreTranslate.of_computation c)
    in
    let defs' = List.map converter defs in
    update state (TopLet defs')

  let process_top_let_rec state defs _vars =
    let converter (p, c) =
      (MulticoreTranslate.of_pattern p, MulticoreTranslate.of_computation c)
    in
    let defs' = Assoc.map converter defs |> Assoc.to_list in
    update state (TopLetRec defs')

  let process_external state (x, ty, f) = update state (External (x, ty, f))

  let process_tydef state tydefs =
    let converter (ty_params, tydef) =
      (ty_params, MulticoreTranslate.of_tydef tydef)
    in
    let tydefs' = Assoc.map converter tydefs |> Assoc.to_list in
    update state (TyDef tydefs')

  let finalize state =
    let channel = open_out P.output_file in
    let output_ppf = Format.formatter_of_out_channel channel in
    List.iter (fun cmd -> MulticoreSyntax.print_cmd cmd output_ppf) state.prog;
    close_out channel
end
