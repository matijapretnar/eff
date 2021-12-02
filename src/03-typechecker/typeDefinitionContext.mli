open Utils
open Language

type state = (CoreTypes.TyName.t, Type.type_data) Assoc.t

val initial_state : state

val extend_type_definitions :
  loc:Location.t ->
  (CoreTypes.TyName.t, Type.type_data) Assoc.t ->
  state ->
  state

val transparent : loc:Location.t -> CoreTypes.TyName.t -> state -> bool

val infer_variant : CoreTypes.Label.t -> state -> Type.ty option * Type.ty

val infer_field :
  CoreTypes.Label.t ->
  state ->
  Type.ty * (CoreTypes.TyName.t * (CoreTypes.Field.t, Type.ty) Assoc.t)

val find_field :
  CoreTypes.Field.t ->
  state ->
  (CoreTypes.TyName.t * Type.Params.t * (CoreTypes.Field.t, Type.ty) Assoc.t)
  option

val find_variant :
  CoreTypes.Label.t ->
  state ->
  (CoreTypes.TyName.t
  * Type.Params.t
  * (CoreTypes.Label.t, Type.ty option) Assoc.t
  * Type.ty option)
  option
