(** Association lists *)
type ('key, 'v) t

(** The empty association list. *)
val empty : ('k, 'v) t



(** [lookup k assoc] returns the most recent value associated with [k] in
    [assoc] if it exists. *)
val lookup : 'k -> ('k, 'v) t -> 'v option

(** [find_if p assoc] returns the first [(k, v)] for which [p] returns [true]
    if it exists. *)
val find_if : (('k * 'v) -> bool) -> ('k, 'v) t -> ('k * 'v) option

(** [pop assoc] returns the first element and the rest of [assoc]. *)
val pop : ('k, 'v) t -> ('k * 'v) option * ('k, 'v) t



(** [update k v assoc] overshadows the previous value for [k] with [v].
    If [remove k assoc] is used once, the previous value will be associated
    with [k] again. *)
val update : 'k -> 'v -> ('k, 'v) t -> ('k, 'v) t

(** [replace k v assoc] replaces the previous value for [k] with [v] if [k]
    is associated with a value in [assoc]. *)
val replace : 'k -> 'v -> ('k, 'v) t -> ('k, 'v) t

(** [remove k assoc] removes the most recent association with [k]. *)
val remove : 'k -> ('k, 'v) t -> ('k, 'v) t



(** [iter f assoc] iterates the function [f] over all elements of [assoc]. *)
val iter : (('k * 'v) -> unit) -> ('k, 'v) t -> unit

(** [map f assoc] transforms each [(k, v)] in [assoc] into [(k, f v)]. *)
val map : ('v -> 'new_v) -> ('k, 'v) t -> ('k, 'new_v) t

(** [kmap f assoc] transforms each [(k, v)] in [assoc] into [f (k, v)]. *)
val kmap : (('k * 'v) -> ('new_k * 'new_v)) -> ('k, 'v) t -> ('new_k, 'new_v) t

(** [map_of_list f lst] transforms each element of [lst] in a pair [(k, v)]
    with the function [f] and builds an association list from it. *)
val map_of_list : ('a -> ('k * 'v)) -> 'a list -> ('k, 'v) t

(** [fold_left f acc assoc] folds [f] over [assoc] from left to right. *)
val fold_left : ('acc -> ('k * 'v) -> 'acc) -> 'acc -> ('k, 'v) t -> 'acc

(** [fold_right f assoc acc] folds [f] over [assoc] from right to left. *)
val fold_right : (('k * 'v) -> 'acc -> 'acc) -> ('k, 'v) t -> 'acc -> 'acc



(** [length assoc] returns the length of the association list. *)
val length : ('k, 'v) t -> int

(** [values_of assoc] constructs a list of all values in [assoc] in the same
    order. *)
val values_of : ('k, 'v) t -> 'v list

(** [keys_of assoc] constructs a list of all keys in [assoc] in the same
    order. *)
val keys_of : ('k, 'v) t -> 'k list

(** [rev assoc] reverses the order of elements in [assoc]. *)
val rev : ('k, 'v) t -> ('k, 'v) t

(** [concat assoc1 assoc2] joins two association lists. If keys are
    repeated, the values in [assoc1] overshadow those of [assoc2]. *)
val concat : ('k, 'v) t -> ('k, 'v) t -> ('k, 'v) t



(** Switch to lists and back. *)
val of_list : ('k * 'v) list -> ('k, 'v) t

val to_list : ('k, 'v) t -> ('k * 'v) list
