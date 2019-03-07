(** OldUtils.definitions. *)

(** Types shared by different modules *)

(** effect symbols *)
type effect = string

(** variant labels *)
type label = string

(** record fields *)
type field = string

(** type names *)
type tyname = string

(** type parameters *)
type typaram = string

(** dirt parameters *)
type dirtparam = int

type comparison = Less | Equal | Greater | Invalid

(** Variants for the built-in list type *)
val cons : label

val nil : label

val no_duplicates : 'a list -> bool

(* [find_duplicate xs ys] returns [Some x] if [x] is the first element of [xs]
   that appears [ys]. It returns [None] if there is no such element. *)
val find_duplicate : 'a list -> 'a list -> 'a option

(** NB: We use our own [map] to be sure that the order of side-effects is
    well-defined. *)

val map : ('a -> 'b) -> 'a list -> 'b list

val flatten_map : ('a -> 'b list) -> 'a list -> 'b list

(** [option_map f] maps [None] to [None] and [Some x] to [Some (f x)]. *)
val option_map : ('a -> 'b) -> 'a option -> 'b option

(** [uniq lst] returns [lst] with all duplicates removed, keeping the first
    occurence of each element. *)

val uniq : 'a list -> 'a list

(** [split n lst] splits [lst] into two parts containing (up to) the first [n]
    elements and the rest. *)

val split : int -> 'a list -> 'a list * 'a list

(** [diff lst1 lst2] returns [lst1] with all members of [lst2] removed *)
val diff : 'a list -> 'a list -> 'a list
