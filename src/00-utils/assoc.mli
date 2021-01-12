type ('key, 'v) t
(** Association lists *)

val empty : ('k, 'v) t
(** The empty association list. *)

val lookup : 'k -> ('k, 'v) t -> 'v option
(** [lookup k assoc] returns the most recent value associated with [k] in
    [assoc] if it exists. *)

val find_if : ('k * 'v -> bool) -> ('k, 'v) t -> ('k * 'v) option
(** [find_if p assoc] returns the first [(k, v)] for which [p] returns [true]
    if it exists. *)

val pop : ('k, 'v) t -> (('k * 'v) * ('k, 'v) t) option
(** [pop assoc] returns the first element and the rest of [assoc]. *)

val update : 'k -> 'v -> ('k, 'v) t -> ('k, 'v) t
(** [update k v assoc] overshadows the previous value for [k] with [v].
    If [remove k assoc] is used once, the previous value will be associated
    with [k] again. *)

val replace : 'k -> 'v -> ('k, 'v) t -> ('k, 'v) t
(** [replace k v assoc] replaces the previous value for [k] with [v] if [k]
    is associated with a value in [assoc]. *)

val remove : 'k -> ('k, 'v) t -> ('k, 'v) t
(** [remove k assoc] removes the most recent association with [k]. *)

val iter : ('k * 'v -> unit) -> ('k, 'v) t -> unit
(** [iter f assoc] iterates the function [f] over all elements of [assoc]. *)

val map : ('v -> 'w) -> ('k, 'v) t -> ('k, 'w) t
(** [map f assoc] transforms each [(k, v)] in [assoc] into [(k, f v)]. *)

val kmap : ('k * 'v -> 'h * 'w) -> ('k, 'v) t -> ('h, 'w) t
(** [kmap f assoc] transforms each [(k, v)] in [assoc] into [f (k, v)]. *)

val map_of_list : ('a -> 'k * 'v) -> 'a list -> ('k, 'v) t
(** [map_of_list f lst] transforms each element of [lst] in a pair [(k, v)]
    with the function [f] and builds an association list from it. *)

val fold_left : ('acc -> 'k * 'v -> 'acc) -> 'acc -> ('k, 'v) t -> 'acc
(** [fold_left f acc assoc] folds [f] over [assoc] from left to right. *)

val fold_right : ('k * 'v -> 'acc -> 'acc) -> ('k, 'v) t -> 'acc -> 'acc
(** [fold_right f assoc acc] folds [f] over [assoc] from right to left. *)

val fold_map :
  ('acc -> 'v -> 'acc * 'w) -> 'acc -> ('k, 'v) t -> 'acc * ('k, 'w) t
(** [fold_map f state assoc] folds from left to right ON VALUES and also maps
    at the same time. *)

val kfold_map :
  ('acc -> 'k * 'v -> 'acc * ('h * 'w)) ->
  'acc ->
  ('k, 'v) t ->
  'acc * ('h, 'w) t
(** [kfold_map f state assoc] folds from left to right and also maps at the same time. *)

val length : ('k, 'v) t -> int
(** [length assoc] returns the length of the association list. *)

val values_of : ('k, 'v) t -> 'v list
(** [values_of assoc] constructs a list of all values in [assoc] in the same
    order. *)

val keys_of : ('k, 'v) t -> 'k list
(** [keys_of assoc] constructs a list of all keys in [assoc] in the same
    order. *)

val rev : ('k, 'v) t -> ('k, 'v) t
(** [rev assoc] reverses the order of elements in [assoc]. *)

val concat : ('k, 'v) t -> ('k, 'v) t -> ('k, 'v) t
(** [concat assoc1 assoc2] joins two association lists. If keys are
    repeated, the values in [assoc1] overshadow those of [assoc2]. *)

val of_list : ('k * 'v) list -> ('k, 'v) t
(** Switch to lists and back. *)

val to_list : ('k, 'v) t -> ('k * 'v) list
