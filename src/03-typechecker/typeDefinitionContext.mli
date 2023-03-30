open Utils
open Language

type state = (TyName.t, Type.type_data) Assoc.t

val initial_state : state
val extend_type_definitions : Type.type_data Type.Field.Map.t -> state -> state
val infer_variant : Type.Label.t -> state -> Type.ty option * Type.ty

val infer_field :
  Type.Label.t -> state -> Type.ty * (TyName.t * Type.ty Type.Field.Map.t)

val find_field :
  Type.Field.t ->
  state ->
  (TyName.t * Type.tydef_params * Type.ty Type.Field.Map.t) option

val find_variant :
  Type.Label.t ->
  state ->
  (TyName.t
  * Type.tydef_params
  * Type.ty option Type.Field.Map.t
  * Type.ty option)
  option
