module type Formatters = sig
  val output : Format.formatter
end 

module Backend (F : Formatters) : BackendSignature.T