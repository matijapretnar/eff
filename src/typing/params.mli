type ty_param
type dirt_param
type region_param
type ty_coercion_param
type dirt_coercion_param
type dirty_coercion_param

val fresh_ty_param : unit -> ty_param
val fresh_dirt_param : unit -> dirt_param
val fresh_region_param : unit -> region_param
val fresh_ty_coercion_param: unit -> ty_coercion_param
val fresh_dirt_coercion_param: unit -> dirt_coercion_param
val fresh_dirty_coercion_param: unit -> dirty_coercion_param

type t

val make : ty_param list * dirt_param list * region_param list -> t
val unmake : t -> ty_param list * dirt_param list * region_param list

val add_ty_param : ty_param -> t -> t
val add_dirt_param : dirt_param -> t -> t
val add_region_param : region_param -> t -> t

val ty_param_mem : ty_param -> t -> bool
val dirt_param_mem : dirt_param -> t -> bool
val region_param_mem : region_param -> t -> bool

type substitution = {
  ty_param : ty_param -> ty_param;
  dirt_param : dirt_param -> dirt_param;
  region_param : region_param -> region_param;
}

(** [identity_subst] is a substitution that makes no changes. *)
val identity_subst : substitution

val beautifying_subst : unit -> substitution

val refreshing_subst : unit -> substitution

val empty : t

val append : t -> t -> t

val flatten_map : ('a -> t) -> 'a list -> t

val diff : t -> t -> t

val uniq : t -> t

val print_ty_param : ?non_poly:t -> ty_param -> Format.formatter -> unit
val print_ty_coercion_param : ?non_poly:t -> ty_coercion_param -> Format.formatter -> unit
val print_dirty_coercion_param : ?non_poly:t -> dirty_coercion_param -> Format.formatter -> unit
val print_dirt_coercion_param : ?non_poly:t -> dirt_coercion_param -> Format.formatter -> unit
val print_dirt_param : ?non_poly:t -> dirt_param -> Format.formatter -> unit
val print_region_param : ?non_poly:t -> region_param -> Format.formatter -> unit
val print_type_param : ty_param -> Format.formatter -> unit

val project_ty_params : t -> ty_param list
val project_dirt_params : t -> dirt_param list
