module CoreSyntax = UntypedSyntax

module TypeSystem = SimpleInfer

module type T = sig
  type state

  val initial_state : state

  val process_computation : 
    Format.formatter -> state -> CoreSyntax.computation
    -> CoreTypes.TyParam.t list * Type.ty -> state

  val process_type_of :
    Format.formatter -> state -> CoreSyntax.computation
    -> CoreTypes.TyParam.t list * Type.ty -> state

  val process_reset : Format.formatter -> state -> state

  val process_help : Format.formatter -> state -> state

  val process_def_effect :
    Format.formatter ->  state -> CoreTypes.Effect.t * (Type.ty * Type.ty)
    -> state

  val process_top_let :
    Format.formatter -> state
    -> (CoreSyntax.pattern * CoreSyntax.computation) list
    -> (TypeSystem.Untyped.variable * TypeSystem.Ctx.ty_scheme) list 
    -> state

  val process_top_let_rec :
    Format.formatter -> state
    -> (CoreSyntax.variable, CoreSyntax.abstraction) Assoc.t
    -> (TypeSystem.Untyped.variable * TypeSystem.Ctx.ty_scheme) list
    -> state

  val process_external :
    Format.formatter -> state
    -> CoreTypes.Variable.t * Type.ty * string
    -> state

  val process_tydef :
    Format.formatter -> state
    -> (CoreTypes.TyName.t, CoreTypes.TyParam.t list * Tctx.tydef) Assoc.t
    -> state

  val finalize : Format.formatter -> state -> unit
end