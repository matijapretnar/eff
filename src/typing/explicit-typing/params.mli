type ty_param
type dirt_param
type ty_coercion_param
type dirt_coercion_param
type dirty_coercion_param
type skel_param
type e_ty_param

val fresh_ty_param : unit -> ty_param
val fresh_dirt_param : unit -> dirt_param
val fresh_ty_coercion_param: unit -> ty_coercion_param
val fresh_dirt_coercion_param: unit -> dirt_coercion_param
val fresh_dirty_coercion_param: unit -> dirty_coercion_param
val fresh_skel_param: unit -> skel_param
val fresh_e_ty_param : unit -> e_ty_param

val beautifying_ty_subst : unit -> (unit -> ty_param)

val print_ty_param : ty_param -> Format.formatter -> unit
val print_dirt_param : dirt_param -> Format.formatter -> unit
val print_ty_coercion_param : ty_coercion_param -> Format.formatter -> unit
val print_dirt_coercion_param : dirt_coercion_param -> Format.formatter -> unit
val print_dirty_coercion_param : dirty_coercion_param -> Format.formatter -> unit
val print_skel_param : skel_param -> Format.formatter -> unit
val print_e_ty_param : e_ty_param -> Format.formatter -> unit
val print_type_param : ty_param -> Format.formatter -> unit
val print_old_ty_param : ?poly:ty_param list -> ty_param -> Format.formatter -> unit
