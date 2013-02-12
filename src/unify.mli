type ty_scheme = (Core.variable, Type.ty) Common.assoc * Type.ty * Type.t
type dirty_scheme = (Core.variable, Type.ty) Common.assoc * Type.dirty * Type.t
type context = (Core.variable, Type.ty) Common.assoc
type change

val region_less :
  pos:'a ->
  Type.region_param ->
  Type.region_param -> change
val region_covers :
  Type.region_param ->
  Type.instance_param -> change
val just : Type.t -> change
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
  change list -> context * Type.ty * Type.t
val gather_dirty_scheme :
  pos:Common.position ->
  context ->
  Type.dirty ->
  change list -> context * Type.dirty * Type.t
val gather_pattern_scheme :
  pos:'a ->
  context ->
  Type.ty ->
  change list -> context * Type.ty * Type.t
