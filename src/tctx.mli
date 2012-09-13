type tydef =
    Record of (Common.field, Type.ty) Common.assoc
  | Sum of (Common.label, Type.ty option) Common.assoc
  | Inline of Type.ty
  | Effect of (Common.opsym, Type.ty * Type.ty) Common.assoc
type variance = bool * bool
type params =
    (Type.ty_param * variance) list * (Type.dirt_param * variance) list *
    (Type.region_param * variance) list
type tyctx = (Common.tyname, params * tydef) Common.assoc
val initial_tctx : tyctx
val tctx : tyctx ref
val reset : unit -> unit
val subst_tydef : Type.substitution -> tydef -> tydef
val lookup_params : Common.tyname -> params option
val lookup_tydef :
  pos:Common.position ->
  Common.tyname ->
  (Type.ty_param list * Type.dirt_param list * Type.region_param list) * tydef
val is_effect : pos:Common.position -> Common.tyname -> bool
val fresh_tydef :
  pos:Common.position ->
  Common.tyname ->
  (Type.ty_param, Type.dirt_param, Type.region_param) Trio.t * tydef
val find_variant :
  Common.label ->
  (Common.tyname * params * (Common.label, Type.ty option) Common.assoc *
   Type.ty option)
  option
val find_field :
  Common.field ->
  (Common.tyname * params * (Common.field, Type.ty) Common.assoc) option
val find_operation :
  Common.opsym -> (Common.tyname * params * Type.ty * Type.ty) option
val apply_to_params :
  Common.tyname ->
  Type.ty_param list * Type.dirt_param list * Type.region_param list ->
  Type.ty
val effect_to_params :
  Common.tyname ->
  Type.ty_param list * Type.dirt_param list * Type.region_param list ->
  Type.region_param -> Type.ty
val infer_variant : Common.label -> (Type.ty * Type.ty option) option
val infer_field :
  Common.field ->
  (Type.ty * (Common.tyname * (Common.field * Type.ty) list)) option
val infer_operation :
  Common.opsym -> Type.region_param -> (Type.ty * (Type.ty * Type.ty)) option
val transparent : pos:Common.position -> Common.tyname -> bool
val ty_apply :
  pos:Common.position ->
  Common.tyname ->
  Type.ty list * Type.dirt_param list * Type.region_param list -> tydef
val extend_tydefs :
  pos:Common.position ->
  (Common.tyname *
   ((Type.ty_param list * Type.dirt_param list * Type.region_param list) * tydef))
  list -> unit
