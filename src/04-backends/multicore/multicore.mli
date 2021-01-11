module type BackendParameters = sig
  val output_file : string
end

module Backend (P : BackendParameters) : Language.BackendSignature.T

val stdlib : string
