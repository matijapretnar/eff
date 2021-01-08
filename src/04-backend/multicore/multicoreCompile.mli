module type BackendParameters = sig
  val output_file : string
end

module Backend (P : BackendParameters) : Backend.BackendSignature.T
