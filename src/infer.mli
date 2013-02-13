val warn_implicit_sequencing : bool ref
val disable_typing : bool ref
val infer_let :
 pos:Common.position -> Ctx.t -> (Core.variable Pattern.t * Core.computation) list ->
   Ctx.t * Core.variable list * (Scheme.dirty_scheme -> Scheme.dirty_scheme)
val infer_let_rec :
 pos:Common.position -> Ctx.t -> (Core.variable * Core.abstraction) list ->
   Ctx.t * (Core.variable * Type.ty) list * (Scheme.dirty_scheme -> Scheme.dirty_scheme)
 val infer_comp : Ctx.t -> Core.computation -> Scheme.dirty_scheme