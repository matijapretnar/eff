module type Formatters = sig
  val warnings : Format.formatter
  val output : Format.formatter
end 

module Backend (F : Formatters) : BackendSignature.T
