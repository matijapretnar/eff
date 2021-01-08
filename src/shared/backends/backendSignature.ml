open Utils
open Language
module CoreSyntax = UntypedSyntax
module TypeSystem = SimpleInfer

module type T = sig
  type state

  val initial_state : state

  val process_computation :
    state ->
    CoreSyntax.computation ->
    CoreTypes.TyParam.t list * Type.ty ->
    state

  val process_type_of :
    state ->
    CoreSyntax.computation ->
    CoreTypes.TyParam.t list * Type.ty ->
    state

  val process_def_effect :
    state -> CoreTypes.Effect.t * (Type.ty * Type.ty) -> state

  val process_top_let :
    state ->
    (CoreSyntax.pattern * CoreSyntax.computation) list ->
    (TypeSystem.Untyped.variable * TypeSystem.ty_scheme) list ->
    state

  val process_top_let_rec :
    state ->
    (CoreSyntax.variable, CoreSyntax.abstraction) Assoc.t ->
    (TypeSystem.Untyped.variable * TypeSystem.ty_scheme) list ->
    state

  val process_external :
    state -> CoreTypes.Variable.t * Type.ty * string -> state

  val process_tydef :
    state ->
    (CoreTypes.TyName.t, CoreTypes.TyParam.t list * TypeContext.tydef) Assoc.t ->
    state

  val finalize : state -> unit
end
