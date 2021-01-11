module type BackendParameters = sig
  val output_file : string option
end

module Backend (P : BackendParameters) : Language.BackendSignature.T
