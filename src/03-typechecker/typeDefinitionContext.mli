open Utils
open Language

type state = (Type.TyName.t, Type.type_data) Assoc.t

val initial_state : state

val extend_type_definitions :
  loc:Location.t -> (Type.TyName.t, Type.type_data) Assoc.t -> state -> state

val transparent : loc:Location.t -> Type.TyName.t -> state -> bool

val infer_variant : Type.Label.t -> state -> Type.ty option * Type.ty

val infer_field :
  Type.Label.t ->
  state ->
  Type.ty * (Type.TyName.t * (Type.Field.t, Type.ty) Assoc.t)

val find_field :
  Type.Field.t ->
  state ->
  (Type.TyName.t * Type.Params.t * (Type.Field.t, Type.ty) Assoc.t) option

val find_variant :
  Type.Label.t ->
  state ->
  (Type.TyName.t
  * Type.Params.t
  * (Type.Label.t, Type.ty option) Assoc.t
  * Type.ty option)
  option
