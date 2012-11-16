val warn_implicit_sequencing : bool ref
val disable_typing : bool ref
val nonexpansive : Core.plain_computation -> bool
val infer_let :
 pos:Common.position -> Ctx.t -> (Core.variable Pattern.t * Core.computation) list ->
   Ctx.t * Core.variable list * (Type.dirty_scheme -> Type.dirty_scheme)
val infer_let_rec :
 pos:Common.position -> Ctx.t -> (Core.variable * Core.abstraction) list ->
   Ctx.t * (Core.variable * Type.ty) list * (Type.dirty_scheme -> Type.dirty_scheme)
 val infer_comp : Ctx.t -> Core.computation -> Type.dirty_scheme