open Utils
open Language

type state = (Type.TyName.t, Type.type_data) Assoc.t

val initial_state : state

val extend_type_definitions :
  loc:Location.t -> Type.type_data Type.Field.Map.t -> state -> state

val transparent : loc:Location.t -> Type.TyName.t -> state -> bool

val infer_variant : Type.Label.t -> state -> Type.ty option * Type.ty

val infer_field :
  Type.Label.t -> state -> Type.ty * (Type.TyName.t * Type.ty Type.Field.Map.t)

val find_field :
  Type.Field.t ->
  state ->
  (Type.TyName.t * Type.Params.t * Type.ty Type.Field.Map.t) option

val find_variant :
  Type.Label.t ->
  state ->
  (Type.TyName.t
  * Type.Params.t
  * Type.ty option Type.Field.Map.t
  * Type.ty option)
  option
