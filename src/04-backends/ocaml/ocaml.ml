(* Compilation to multicore ocaml *)

module type BackendParameters = sig
  val output_file : string
end

module Backend (P : BackendParameters) : Language.BackendSignature.T = struct
  (* ------------------------------------------------------------------------ *)
  (* Setup *)

  type state = unit

  let initial_state = ()

  (* ------------------------------------------------------------------------ *)
  (* Processing functions *)
  let process_computation state _c _ = state

  let process_type_of state _ _ = state

  let process_def_effect state _ = state

  let process_top_let state _ _ = state

  let process_top_let_rec state _ _ = state

  let process_external state _ = state

  let process_tydef state _ = state

  let finalize _ =
    let channel = open_out P.output_file in
    let output_ppf = Format.formatter_of_out_channel channel in
    Format.fprintf output_ppf "TEST@.";
    close_out channel
end
