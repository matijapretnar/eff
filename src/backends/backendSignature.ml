module ExEff = Typed
module TypeSystem = SimpleInfer
(* STIEN: Supposed to eventually not use this anymore, now used for top let (rec) *)
module CoreSyntax = UntypedSyntax

module type T = sig
  type state

  val initial_state : state

  val process_computation :
       state
    -> ExEff.computation
    -> Types.target_dirty
    -> state

  val process_type_of :
       state
    -> ExEff.computation
    -> Types.target_dirty
    -> state

  val process_def_effect :
    state -> CoreTypes.Effect.t * (Type.ty * Type.ty) -> state

  val process_top_let :
       state
    -> (ExEff.pattern * ExEff.computation) list
    -> (CoreTypes.Variable.t * TypeSystem.Ctx.ty_scheme) list
    -> state

  val process_top_let_rec :
       state
    -> (ExEff.variable, ExEff.abstraction) Assoc.t
    -> (CoreTypes.Variable.t * TypeSystem.Ctx.ty_scheme) list
    -> state

  val process_external :
    state -> CoreTypes.Variable.t * Type.ty * string -> state

  val process_tydef :
       state
    -> (CoreTypes.TyName.t, CoreTypes.TyParam.t list * Tctx.tydef) Assoc.t
    -> state

  val finalize : state -> unit
end
