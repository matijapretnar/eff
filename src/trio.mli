type ('a, 'b, 'c) t = 'a list * 'b list * 'c list

val empty : ('a, 'b, 'c) t

val append : ('a, 'b, 'c) t -> ('a, 'b, 'c) t -> ('a, 'b, 'c) t
val snds :  ('a * 'b, 'c * 'd, 'e * 'f) t -> ('b, 'd, 'f) t
val flatten_map : ('a -> ('b, 'c, 'd) t) -> 'a list -> ('b, 'c, 'd) t
val diff : ('a, 'b, 'c) t -> ('a, 'b, 'c) t -> ('a, 'b, 'c) t
val uniq : ('a, 'b, 'c) t -> ('a, 'b, 'c) t
