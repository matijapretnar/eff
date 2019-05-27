(* Evaluation of the intermediate language, big step. *)
open CoreUtils
module Core = UntypedSyntax
module Multicore = MulticoreSyntax

module type BackendParameters = sig
  val output_file : string
end

module Backend (P : BackendParameters) : BackendSignature.T = struct
  (* ------------------------------------------------------------------------ *)
  (* Setup *)

  type state = {prog: Multicore.cmd list}

  let initial_state = {prog= []}

  (* Auxiliary functions *)
  let update state term =

    (* TODO the only thing missing is this.. printing of the translation in console *)
    (* let actual_translation = Format.flush_str_formatter () in
    Format.fprintf !Config.output_formatter "%s@?" actual_translation ;
    {prog= state.prog ^ actual_translation} *)
    {prog= state.prog @ [term]}

  (* ------------------------------------------------------------------------ *)
  (* Processing functions *)
  let process_computation state c ty =
    let t = Multicore.of_computation c in
    (* update state
      (translate state_ppf
         "let _ = @.@[<hv>(_ocaml_tophandler) (fun _ -> @,%t@,)@];;@."
         (translate_term t)) *)
      update state (Term t)

  let process_type_of state c ty =
    Print.warning
      "[#typeof] commands are ignored when compiling to Multicore OCaml." ;
    state

  let process_def_effect state (eff, (ty1, ty2)) =
    let ty1' = Multicore.of_type ty1 in
    let ty2' = Multicore.of_type ty2 in
    (* let translation = translate_def_effect (eff, (ty1', ty2')) state_ppf in
    update state translation *)
    update state (DefEffect (eff, (ty1', ty2')))

  let process_top_let state defs vars =
    let converter (p, c) =
      (Multicore.of_pattern p, Multicore.of_computation c)
    in
    let defs' = List.map converter defs in
    (* let translation = translate_top_let defs' state_ppf in
    update state translation *)
    update state (TopLet defs')

  let process_top_let_rec state defs vars =
    let converter (p, c) =
      (Multicore.of_pattern p, Multicore.of_computation c)
    in
    let defs' = Assoc.map converter defs |> Assoc.to_list in
    (* let translation = MulticoreTranslate.translate_top_let_rec defs' in *)
    (* state *)
   update state (TopLetRec defs')

  let process_external state (x, ty, f) =
    (* match Assoc.lookup f MulticoreExternal.values with
    | None -> Error.runtime "Unknown external symbol %s." f
    | Some (MulticoreExternal.Unknown as unknown) ->
        Print.warning
          ( "External symbol %s cannot be compiled. It has been replaced "
          ^^ "with [failwith \"Unknown external symbol %s.\"]." )
          f f ;
        let translation = translate_external x f unknown state_ppf in
        update state translation
    | Some (MulticoreExternal.Exists s as known) ->
        let translation = translate_external x f known state_ppf in
        update state translation *)
    update state (External (x, ty, f))

  let process_tydef state tydefs =
    let converter (ty_params, tydef) = (ty_params, Multicore.of_tydef tydef) in
    let tydefs' = Assoc.map converter tydefs |> Assoc.to_list in
    (* let translation = translate_tydefs tydefs' state_ppf in
    update state translation *)
    update state (TyDef tydefs')

  let finalize state = MulticoreTranslate.write_to_file P.output_file state.prog
end
