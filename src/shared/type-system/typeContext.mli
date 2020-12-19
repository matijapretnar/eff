type tydef =
  | Record of (CoreTypes.Field.t, Type.ty) Assoc.t
  | Sum of (CoreTypes.Label.t, Type.ty option) Assoc.t
  | Inline of Type.ty

type type_data

type state = (CoreTypes.TyName.t, type_data) Assoc.t

val initial_state : state

val extend_type_definitions :
  loc:Location.t ->
  (CoreTypes.TyName.t, CoreTypes.TyParam.t list * tydef) Assoc.t ->
  state ->
  state

val transparent : loc:Location.t -> CoreTypes.TyName.t -> state -> bool

val ty_apply :
  loc:Location.t -> CoreTypes.TyName.t -> Type.ty list -> state -> tydef

val infer_variant :
  CoreTypes.Label.t -> state -> (Type.ty * Type.ty option) option

val infer_field :
  CoreTypes.Label.t ->
  state ->
  (Type.ty * (CoreTypes.TyName.t * (CoreTypes.Field.t, Type.ty) Assoc.t)) option

val find_field :
  CoreTypes.Field.t ->
  state ->
  (CoreTypes.TyName.t
  * CoreTypes.TyParam.t list
  * (CoreTypes.Field.t, Type.ty) Assoc.t)
  option

val find_variant :
  CoreTypes.Label.t ->
  state ->
  (CoreTypes.TyName.t
  * CoreTypes.TyParam.t list
  * (CoreTypes.Label.t, Type.ty option) Assoc.t
  * Type.ty option)
  option
