(** Association lists *)
type ('key, 'value) t = ('key * 'value) list

(** [lookup k assoc] returns the most recent value associated with [k] in the 
   association list [assoc]. *)
val lookup : 'key -> ('key, 'value) t -> 'value option

(** [remove k assoc] removes the most recent association with [k]. *)
val remove : 'key -> ('key, 'value) t -> ('key, 'value) t

(** [update k v assoc] overshadows the previous value for [k] with [v].
   If [remove k assoc] is used once, the previous value will be associated
   with [k] again. *)
val update : 'key -> 'value -> ('key, 'value) t -> ('key, 'value) t

(** [map f assoc] transforms each [(k, v)] in [assoc] into [(k, f v)]. *)
val map : ('value -> 'new_value) -> ('key, 'value) t -> ('key, 'new_value) t
