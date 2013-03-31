val warn_implicit_sequencing : bool ref
val disable_typing : bool ref
val infer_let :
           pos:Common.position ->
           Ctx.t ->
           (Core.variable Pattern.t * Core.computation) list ->
           (Core.variable * Type.ty) list * (Core.variable * Type.ty) list *
           Scheme.context * Scheme.change list * Type.dirt
val infer_let_rec :
    pos:Common.position ->
           Ctx.t ->
           (Core.variable * Core.abstraction) list ->
           Scheme.context * Scheme.context * Scheme.change list
 val infer_comp : Ctx.t -> Core.computation -> Scheme.dirty_scheme