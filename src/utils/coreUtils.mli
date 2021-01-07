type 'a located = { it : 'a; at : Location.t }

type comparison = Less | Equal | Greater | Invalid

val fold : ('a -> 'b -> 'a) -> 'a -> 'b list -> 'a

val fold_map :
  ('state -> 'a -> 'state * 'b) -> 'state -> 'a list -> 'state * 'b list

val concat_map : ('a -> 'b list) -> 'a list -> 'b list

val left_to_right_map : ('a -> 'b) -> 'a list -> 'b list
(** Custom definition of map to ensure the order of sideffects. *)

val unique_elements : 'a list -> 'a list
(** Returns a list of all unique elements of given list. *)

val no_duplicates : 'a list -> bool
(** Checks that the list doesn't contain duplicates. *)

val list_diff : 'a list -> 'a list -> 'a list
(** Returns elements of the first list that or not present in the second. *)

val option_map : ('a -> 'b) -> 'a option -> 'b option
(** [option_map f] maps [None] to [None] and [Some x] to [Some (f x)]. *)

val map_default : ('a -> 'b) -> 'b -> 'a option -> 'b
