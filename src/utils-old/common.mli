type effect = string
type label = string
type field = string
type tyname = string
type typaram = string
type dirtparam = int
type regionparam = int
val id : 'a -> 'a
val compose : ('b -> 'c) -> ('a -> 'b) -> ('a -> 'c)
type comparison = Less | Equal | Greater | Invalid
val cons : string
val nil : string
type ('a, 'b) assoc = ('a * 'b) list
val lookup : 'a -> ('a * 'b) list -> 'b option
val lookup_default : 'a -> ('a * 'b) list -> 'b -> 'b
val find : ('a -> bool) -> 'a list -> 'a option
val update : 'a -> 'b -> ('a * 'b) list -> ('a * 'b) list
val injective : ('a -> 'b) -> 'a list -> bool
val find_duplicate : 'a list -> 'a list -> 'a option
val map : ('a -> 'b) -> 'a list -> 'b list
val flatten_map : ('a -> 'b list) -> 'a list -> 'b list
val option_map : ('a -> 'b) -> 'a option -> 'b option
val repeat : 'a -> int -> 'a list
val assoc_map : ('a -> 'b) -> ('c * 'a) list -> ('c * 'b) list
val fresh : (int -> 'a) -> unit -> 'a
val uniq : 'a list -> 'a list
val split : int -> 'a list -> 'a list * 'a list
val diff : 'a list -> 'a list -> 'a list
val assoc_flatten : ('a * 'b) list -> ('a * 'b list) list

type ('a, 'b, 'c) trio = 'a list * 'b list * 'c list

val trio_empty : ('a, 'b, 'c) trio

val trio_append : ('a, 'b, 'c) trio -> ('a, 'b, 'c) trio -> ('a, 'b, 'c) trio
val trio_snds :  ('a * 'b, 'c * 'd, 'e * 'f) trio -> ('b, 'd, 'f) trio
val trio_flatten_map : ('a -> ('b, 'c, 'd) trio) -> 'a list -> ('b, 'c, 'd) trio
val trio_diff : ('a, 'b, 'c) trio -> ('a, 'b, 'c) trio -> ('a, 'b, 'c) trio
val trio_uniq : ('a, 'b, 'c) trio -> ('a, 'b, 'c) trio
