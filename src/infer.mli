val warn_implicit_sequencing : bool ref
val disable_typing : bool ref
val nonexpansive : Core.plain_computation -> bool
         val infer_let :
           Ctx.t ->
           Common.position ->
           (int Pattern.t * Core.computation) list ->
           Ctx.t * (int, Type.ty) Common.assoc * (int * Type.ty) list *
           Type.instance_param list * Type.dirt_param list *
           Constr.constraints list
val infer_let_rec :
   Ctx.t ->
   Common.position ->
   (int * Core.abstraction) list ->
   Ctx.t * (int * Type.ty) list * Constr.constraints list
val infer_comp :
  Ctx.t -> Core.computation -> Ctx.dirty_scheme