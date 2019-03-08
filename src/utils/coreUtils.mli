type 'a located = {it: 'a; at: Location.t}

type comparison = Less | Equal | Greater | Invalid

val fold : ('a -> 'b -> 'a) -> 'a -> 'b list -> 'a

val fold_map :
  ('state -> 'a -> 'state * 'b) -> 'state -> 'a list -> 'state * 'b list

(** Custom definition of map to ensure the order of sideffects. *)
val left_to_right_map : ('a -> 'b) -> 'a list -> 'b list

(** Returns a list of all unique elements of given list. *)
val unique_elements : 'a list -> 'a list

(** Checks that the list doesn't contain duplicates. *)
val no_duplicates : 'a list -> bool

(** Returns elements of the first list that or not present in the second. *)
val list_diff : 'a list -> 'a list -> 'a list