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

  let intermediate_buf = Buffer.create 512
  let intermediate_ppf = Format.formatter_of_buffer intermediate_buf
  
  (* Auxiliary functions *)
  let update state cmd =
    MulticoreTranslate.translate_cmd intermediate_ppf cmd;
    Format.pp_print_flush intermediate_ppf ();
    let actual_translation = Buffer.contents intermediate_buf in
    Buffer.reset intermediate_buf;
    Format.fprintf !Config.output_formatter "%s@?" actual_translation ;
    {prog= state.prog @ [cmd]}

  (* ------------------------------------------------------------------------ *)
  (* Processing functions *)
  let process_computation state c ty =
    let t = Multicore.of_computation c in
      update state (Term t)

  let process_type_of state c ty =
    Print.warning
      "[#typeof] commands are ignored when compiling to Multicore OCaml." ;
    state

  let process_def_effect state (eff, (ty1, ty2)) =
    let ty1' = Multicore.of_type ty1 in
    let ty2' = Multicore.of_type ty2 in
    update state (DefEffect (eff, (ty1', ty2')))

  let process_top_let state defs vars =
    let converter (p, c) =
      (Multicore.of_pattern p, Multicore.of_computation c)
    in
    let defs' = List.map converter defs in
    update state (TopLet defs')

  let process_top_let_rec state defs vars =
    let converter (p, c) =
      (Multicore.of_pattern p, Multicore.of_computation c)
    in
    let defs' = Assoc.map converter defs |> Assoc.to_list in
    update state (TopLetRec defs')

  let process_external state (x, ty, f) =
    update state (External (x, ty, f))

  let process_tydef state tydefs =
    let converter (ty_params, tydef) = (ty_params, Multicore.of_tydef tydef) in
    let tydefs' = Assoc.map converter tydefs |> Assoc.to_list in
    update state (TyDef tydefs')

  let finalize state = MulticoreTranslate.write_to_file P.output_file state.prog
end
