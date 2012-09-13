val empty_constraint : 'a list
val constraints_of_graph : Constr.t -> Type.constraints list
val solve : Type.constraints list -> Type.substitution * Constr.t
val pos_neg_params :
  Type.ty ->
  (Type.ty_param, Type.dirt_param, Type.region_param) Trio.t *
  (Type.ty_param, Type.dirt_param, Type.region_param) Trio.t
val garbage_collect :
  (Constr.Ty.elt list * Type.dirt_param list * Type.region_param list) *
  (Constr.Ty.elt list * Type.dirt_param list * Type.region_param list) ->
  Constr.t -> Constr.t
