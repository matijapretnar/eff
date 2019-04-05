(* Evaluation of the intermediate language, big step. *)
open CoreUtils
module Core = UntypedSyntax
module MCOC = McocSyntax

module type Formatters = sig
  val warnings : Format.formatter
  val output : Format.formatter
end

module Backend (F : Formatters) : BackendSignature.T = struct
  
  let warnings_ppf = F.warnings

  let output_ppf = F.output

  type state = string

  let initial_state = ""

  let load_mode state = failwith "TODO"

  let execute_mode state = failwith "TODO"

  (* Auxiliary functions *)
  let update state translation = state ^ translation

  let issue_warning txt = 
    Format.fprintf warnings_ppf "Warning: %s\n" txt 

  let translation_of_term t = failwith "TODO"

  let translation_of_def_effect (eff, (ty1, ty2)) = failwith "TODO"

  let translation_of_top_let defs = failwith "TODO"

  let translation_of_top_let_rec defs = failwith "TODO"

  let translation_of_external name translation = failwith "TODO"

  let translation_of_tydefs tydefs = failwith "TODO"

  (* Processing functions *)
  let process_computation state c ty = 
    let t = MCOC.of_computation c in
    update state (translation_of_term t)

  let process_type_of state c ty = 
    issue_warning 
      "[#typeof] commands are ignored when compiling to MulticoreOCaml." ;
    state

  let process_reset state = 
    issue_warning 
      "[#reset] commands are ignored when compiling to MulticoreOCaml." ;
    state

  let process_help state =
    issue_warning 
      ("[#help] commands are ignored when compiling to MulticoreOCaml."
      ^ " Not even gods can help you here.") ;
    state
  
  let process_def_effect state (eff, (ty1, ty2)) =
    let ty1' = MCOC.of_type ty1 in
    let ty2' = MCOC.of_type ty2 in
    let translation = translation_of_def_effect (eff, (ty1', ty2')) in
    update state translation

  let process_top_let state defs vars =
    let converter (p, c) = (MCOC.of_pattern, MCOC.of_computation) in
    let defs' = List.map converter defs in
    let translation = translation_of_top_let defs' in
    update state translation

  let process_top_let_rec state defs vars =
    let converter (p, c) = (MCOC.of_pattern, MCOC.of_computation) in
    let defs' = Assoc.map converter defs in
    let translation = translation_of_top_let_rec defs' in
    update state translation

  let process_external state (x, ty, f) =
    match Assoc.lookup f McocExternal.values with
      | None -> Error.runtime "Unknown external symbol %s." f
      | Some (McocExternal.Unknown as unknown) ->
          let warning_text = 
            Printf.sprintf
              ("External symbol %s cannot be compiled. It has been replaced "
              ^^ "with [failwith \"Unknown external symbol %s.\"].") f f
          in
          issue_warning warning_text;
          let translation = translation_of_external x unknown in
          update state translation
      | Some ((McocExternal.Exists s) as known) ->
          let translation = translation_of_external x known in
          update state translation

  let process_tydef state tydefs = 
    let converter (ty_params, tydef) = (ty_params, MCOC.of_tydef tydef) in
    let tydefs' = Assoc.map converter tydefs in
    let translation = translation_of_tydefs tydefs' in
    update state translation

  let finalize state = Format.fprintf output_ppf "%s" state

end