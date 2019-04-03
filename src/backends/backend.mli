module CoreSyntax = UntypedSyntax

type state

val initial_state : state

val process_computation : state -> CoreSyntax.computation -> state

val process_type_of : state -> CoreSyntax.computation -> state

val process_reset : state -> state

val process_help : state -> state

val process_def_effect : state -> CoreTypes.Effect.t * (Type.ty * Type.ty) -> state

val process_use : state -> string -> state

val process_top_let : state -> (TypeSystem.Untyped.variable * TypeSystem.Ctx.ty_scheme) list -> (CoreSyntax.pattern * CoreSyntax.computation) list -> state

val process_top_let_rec : state -> (TypeSystem.Untyped.variable * TypeSystem.Ctx.ty_scheme) list -> (CoreSyntax.variable * CoreSyntax.abstraction) list -> state

val process_external : state -> (CoreTypes.TyName.t, CoreTypes.TyParam.t list * Tctx.tydef) Assoc.t -> state

val process_tydef : state -> (CoreTypes.TyName.t, CoreTypes.TyParam.t list * Tctx.tydef) Assoc.t -> state

val finalize : state -> unit
