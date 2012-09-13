val warn_implicit_sequencing : bool ref
val disable_typing : bool ref
val nonexpansive : Core.plain_computation -> bool
val infer_let :
  Ctx.t ->
  Type.constraints list ref ->
  Common.position ->
  (Pattern.t * Core.computation) list ->
  (Common.variable * Ctx.ty_scheme) list * Type.dirt_param list *
  Type.instance_param list * Ctx.t
val infer_let_rec :
  Ctx.t ->
  Type.constraints list ref ->
  Common.position ->
  (Common.variable * Core.abstraction) list ->
  (Common.variable * Ctx.ty_scheme) list * Ctx.t
val infer_comp :
  Ctx.t -> Type.constraints list ref -> Core.computation -> Type.dirty
