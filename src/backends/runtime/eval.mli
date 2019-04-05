module type OutputFormatter = sig
  val ppf : Format.formatter
end 

module Backend (OutF : OutputFormatter) : BackendSignature.T
