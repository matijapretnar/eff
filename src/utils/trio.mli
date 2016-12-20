type ty_param
type dirt_param
type region_param

val fresh_ty_param : unit -> ty_param
val fresh_dirt_param : unit -> dirt_param
val fresh_region_param : unit -> region_param

type t = ty_param list * dirt_param list * region_param list

type substitution = {
  ty_param : ty_param -> ty_param;
  dirt_param : dirt_param -> dirt_param;
  region_param : region_param -> region_param;
}

val identity_subst : substitution

val beautifying_subst : unit -> substitution

val refreshing_subst : unit -> substitution

val empty : t

val append : t -> t -> t

val flatten_map : ('a -> t) -> 'a list -> t

val diff : t -> t -> t

val uniq : t -> t

val print_ty_param : ?non_poly:t -> ty_param -> Format.formatter -> unit
val print_dirt_param : ?non_poly:t -> dirt_param -> Format.formatter -> unit
val print_region_param : ?non_poly:t -> region_param -> Format.formatter -> unit
val print_type_param : ty_param -> Format.formatter -> unit