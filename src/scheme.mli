type context = (Core.variable, Type.ty) Common.assoc
type ty_scheme = context * Type.ty * Constraints.t
type dirty_scheme = context * Type.dirty * Constraints.t
type change

val region_less :
  pos:'a ->
  Type.region_param ->
  Type.region_param -> change
val region_covers :
  Type.region_param ->
  Type.instance_param -> change
val just : Constraints.t -> change
val add_presence_bound :
  Type.presence_param ->
  Type.presence list -> change
val dirt_less :
  pos:Common.position ->
  Type.dirt ->
  Type.dirt ->
  change
val ty_less :
  pos:Common.position ->
  Type.ty ->
  Type.ty ->
  change
val dirty_less :
  pos:Common.position ->
  Type.dirty ->
  Type.dirty ->
  change
val trim_context :
  pos:Common.position ->
  context ->
  change

val gather_ty_scheme :
  pos:Common.position ->
  context ->
  Type.ty ->
  change list -> context * Type.ty * Constraints.t
val gather_dirty_scheme :
  pos:Common.position ->
  context ->
  Type.dirty ->
  change list -> context * Type.dirty * Constraints.t
val gather_pattern_scheme :
  pos:'a ->
  context ->
  Type.ty ->
  change list -> context * Type.ty * Constraints.t
