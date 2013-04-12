type context = (Core.variable, Type.ty) Common.assoc
type ty_scheme = context * Type.ty * Constraints.t
type dirty_scheme = context * Type.dirty * Constraints.t
type change

val refresh : ty_scheme -> ty_scheme

val region_less :
  pos:'a ->
  Type.region_param ->
  Type.region_param -> change
val region_covers :
  Type.region_param ->
  Type.instance_param -> change
val just : Constraints.t -> change
val add_region_bound :
  Type.region_param ->
  Constraints.region_bound list -> change
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
val less_context :
  pos:Common.position ->
  context ->
  change

val finalize_ty_scheme :
  pos:Common.position ->
  context ->
  Type.ty ->
  change list -> context * Type.ty * Constraints.t
val finalize_dirty_scheme :
  pos:Common.position ->
  context ->
  Type.dirty ->
  change list -> context * Type.dirty * Constraints.t
val finalize_pattern_scheme :
  pos:'a ->
  context ->
  Type.ty ->
  change list -> context * Type.ty * Constraints.t
val add_to_top :
           pos:Common.position ->
           ('a * Type.ty) list ->
           Constraints.t ->
           ('a * Type.ty) list * Type.dirty * Constraints.t ->
           ('a * Type.ty) list * Type.dirty * Constraints.t
val subst_dirty_scheme : Type.substitution -> dirty_scheme -> dirty_scheme
val print_ty_scheme : ty_scheme -> Format.formatter -> unit
val print_dirty_scheme : dirty_scheme -> Format.formatter -> unit
