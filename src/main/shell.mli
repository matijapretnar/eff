
module type Shell = sig
  type state

  val initial_state : state

  val execute_file : string -> state -> state

  val load_file : string -> state -> state

  val execute_source : string -> state -> state
end

module Make (Backend : BackendSignature.T) : Shell