val warn_implicit_sequencing : bool ref
val disable_typing : bool ref
val nonexpansive : Core.plain_computation -> bool
         val infer_let :
           Ctx.t ->
           Common.position ->
           (Core.variable Pattern.t * Core.computation) list ->
           Ctx.t * (Core.variable, Type.ty) Common.assoc *
           (Core.variable * Type.ty) list * Type.instance_param list *
           Type.dirt_param list * Constr.constraints list         val infer_let_rec :
           Ctx.t ->
           Common.position ->
           (Core.variable * Core.abstraction) list ->
           (Core.variable * Type.ty) list * Ctx.t * (Core.variable, Type.ty) Common.assoc *
           Constr.constraints list
           val infer_comp :
  Ctx.t -> Core.computation -> Ctx.dirty_scheme