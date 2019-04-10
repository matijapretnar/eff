module type Formatters = sig
  val warnings : Format.formatter
  val response : Format.formatter
  val output : Format.formatter
  val printing : bool
end 

module Backend (F : Formatters) : BackendSignature.T
