module type Shell = sig
  type state

  val initialize : unit -> state

  val execute_file : string -> state -> state

  val load_file : string -> state -> state

  val execute_source : string -> state -> state

  val load_source : string -> state -> state

  val finalize : state -> unit
end

module Make (Backend : Backend.BackendSignature.T) : Shell
