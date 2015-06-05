type variable = string
type opsym = string
type effect = string
type label = string
type field = string
type tyname = string
type typaram = string
type dirtparam = int
type regionparam = int
val id : 'a -> 'a
val compose : ('b -> 'c) -> ('a -> 'b) -> ('a -> 'c)
type const =
    Integer of Big_int.big_int
  | String of string
  | Boolean of bool
  | Float of float
type comparison = Less | Equal | Greater | Invalid
val compare_const : const -> const -> comparison
val equal_const : const -> const -> bool
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
val print_const : const -> Format.formatter -> unit
val assoc_flatten : ('a * 'b) list -> ('a * 'b list) list
