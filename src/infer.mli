val warn_implicit_sequencing : bool ref
val disable_typing : bool ref
val nonexpansive : Core.plain_computation -> bool
val infer_let :
  Ctx.t ->
  Common.position ->
  (int Pattern.t * Core.computation) list ->
  (int * Ctx.ty_scheme) list * Type.dirt_param list *
  Type.instance_param list * Ctx.t * Type.constraints list
val infer_let_rec :
  Ctx.t ->
  Common.position ->
  (int * Core.abstraction) list ->
  (int * Ctx.ty_scheme) list * Ctx.t * Type.constraints list
val infer_comp :
  Ctx.t -> Core.computation -> Type.dirty * Type.constraints list
